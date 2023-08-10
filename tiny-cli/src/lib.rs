#![cfg_attr(not(test), no_std)]
#![warn(clippy::pedantic)]

extern crate alloc;
use alloc::string::String;
use core::fmt::{Display, Formatter};
use core::str::Utf8Error;

#[derive(Debug)]
pub struct ArgParseError {
    help: String,
    cause: ArgParseCause,
}

impl ArgParseError {
    #[must_use]
    pub fn new(help: String, cause: ArgParseCause) -> Self {
        Self { help, cause }
    }
}

impl Display for ArgParseError {
    fn fmt(&self, f: &mut Formatter<'_>) -> core::fmt::Result {
        let res = f.write_str(&self.help);
        match &self.cause {
            ArgParseCause::NotUtf8(e) => {
                res?;
                f.write_fmt(format_args!("Caused by: {e}"))
            }
            ArgParseCause::MissingRequiredField(field) => {
                res?;
                f.write_fmt(format_args!("Missing required field {field}"))
            }
            ArgParseCause::UnrecognizedArg(e) => {
                f.write_fmt(format_args!("Unrecognized argument: {e}"))
            }
            ArgParseCause::NoDashStart => f.write_str("Expected dash"),
            ArgParseCause::ExpectedArgFollowing(arg) => {
                f.write_fmt(format_args!("Expected arg following: {arg}"))
            }
            ArgParseCause::FailedParse(field) => {
                f.write_fmt(format_args!("Failed to parse value for field: {field}"))
            }
            ArgParseCause::Help => res,
        }
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
pub enum ArgParseCause {
    Help,
    NotUtf8(Utf8Error),
    MissingRequiredField(&'static str),
    UnrecognizedArg(String),
    ExpectedArgFollowing(&'static str),
    NoDashStart,
    FailedParse(&'static str),
}

/// A macro that parses args.
/// The goal is not to be a beautiful full-featured arg-parser, there are many projects
/// which does that better.
/// This is only supposed to supposed to support the minimum to create a CLI that takes arguments.
/// There are Four kinds of arguments that are accepted:
/// 1. Required arguments, passed as `--long` or `-s` (short) followed by `argument`.
/// 2. Optional arguments, passed as `--long` or `-s` (short) followed by `argument`, or not at all.
/// 3. Repeating arguments, passed 0 or more times as `--long` or `-s` (short) followed by `argument`.
/// 4. Subcommands, passed as `command-name`.
/// I have a special distaste for `proc_macros`, regular macros are limited but can at least be
/// expanded with relative ease, but it does come with limitations. One of those being the
/// above fields having to be declared in order. Required always first, subcommands always last.
///
/// Some more requirements:
/// 1. Repeating arguments are always `Vec<T>`.
/// 2. Optional arguments are always `Option<T>`.
/// 3. Subcommands are always `Option<T>`
/// 4. `arg_parse!`-structs need a `#[name("")]`-section, followed by a `#[description("")]`-section
/// 5. All fields except subcommands need a `#[short(""), long(""), description("")]` right above it.
/// 6. Optional fields require a `#[optional]` above the required 5.
/// 7. Repeating arguments need a `#[repeating]` above the required 5.
/// 8. Subcommands need a `#[subcommand("")]` right above it
///
/// Ex:
/// ```
/// extern crate alloc;
/// use tiny_cli::arg_parse;
/// arg_parse!(
///     #[name("My nested command")]
///     #[description("Use this nested subcommand for fun and profit")]
///     pub struct NestedSc {
///         #[short("f"), long("field-1"), description("My first field")]
///         my_sc_field: String,
///         #[short("s"), long("sc-field"), description("My sc second field")]
///         my_other_sc_field: i64,
///     }
/// );
/// arg_parse!(
///     #[name("My first first level subcommand")]
///     #[description("Use this nested subcommand for fun and profit")]
///     pub struct ScOne {
///         #[short("h"), long("has-field"), description("My first field")]
///         my_sc_field: String,
///         #[subcommand("nested")]
///         nested: Option<NestedSc>,
///     }
/// );
/// arg_parse!(
///     #[name("My second first level subcommand")]
///     #[description("Use this nested subcommand for fun and profit")]
///     pub struct ScTwo {
///         #[optional]
///         #[short("h"), long("has-field"), description("My first field")]
///         opt_option: Option<String>,
///         #[repeating]
///         #[short("r"), long("rep-field"), description("My repeating field")]
///         rep_option: Vec<i32>,
///     }
/// );
///
/// arg_parse!(
///     #[name("My top level command")]
///     #[description("Use top level command with subcommands for fun and profit")]
///     pub struct Mc {
///         #[short("m"), long("my-field"), description("My first field")]
///         my_field: String,
///
///         #[subcommand("first-sub")]
///         subcommand_one: Option<ScOne>,
///
///         #[subcommand("second-sub")]
///         subcommand_two: Option<ScTwo>,
///     }
/// );
/// ```
#[macro_export]
macro_rules! arg_parse {
    (
        #[name($name:expr)]
        #[description($app_desc:expr)]
        $(#[$outer:meta])*
        $vis:vis struct $ArgStruct:ident {
            $(
                #[short($short_desc:expr), long($long_desc:expr), description($desc:expr)]
                $required_field:ident: $req_ty:ty,
            )*
            $(
                #[optional]
                #[short($opt_short_desc:expr), long($opt_long_desc:expr), description($opt_desc:expr)]
                $optional_field:ident: Option<$opt_ty:ty>,
            )*
            $(
                #[repeating]
                #[short($rep_short_desc:expr), long($rep_long_desc:expr), description($rep_desc:expr)]
                $repeating_field:ident: Vec<$rep_ty:ty>,
            )*
            $(
                #[subcommand($sc_name:expr)]
                $subcommand:ident: Option<$sc_ty:ty>,
            )*
        }
    ) => {
        $(#[$outer])*
        $vis struct $ArgStruct {
            $(
                $required_field: $req_ty,
            )*
            $(
                $optional_field: Option<$opt_ty>,
            )*
            $(
                $repeating_field: Vec<$rep_ty>,
            )*
            $(
                $subcommand: Option<$sc_ty>,
            )*
        }

        impl $crate::Parser for $ArgStruct {
            #[inline(never)]
            #[allow(clippy::too_many_lines)]
            fn parse<'a>(it: &mut impl Iterator<Item=Result<&'a str, core::str::Utf8Error>>) -> Result<Self, $crate::ArgParseError> {
                use core::str::FromStr;
                #[allow(dead_code)]
                use alloc::string::ToString;
                $(let mut $required_field: Option<$req_ty> = None;)*
                $(let mut $optional_field: Option<$opt_ty> = None;)*
                $(let mut $repeating_field: Vec<$rep_ty> = Vec::new();)*
                $(let mut $subcommand: Option<$sc_ty> = None;)*
                loop {
                    if let Some(next) = it.next() {
                        let n = next
                            .map_err(|e| $crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::NotUtf8(e)))?;
                        if n.starts_with('-') {
                            if let Some((a, b)) = n.split_once("--") {
                                if !a.is_empty() {
                                    return Err($crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::NoDashStart));
                                }
                                match b {
                                    "--help" => return Err($crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::Help)),
                                    $(
                                        $long_desc => {
                                            let next = it.next()
                                                .ok_or_else(|| $crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::ExpectedArgFollowing(stringify!($long_desc))))?
                                                .map_err(|e| $crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::NotUtf8(e)))?;
                                            $required_field = Some(<$req_ty>::from_str(next)
                                                .map_err(|_err| $crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::FailedParse(stringify!($required_field))))?
                                            );
                                        },
                                    )*
                                    $(
                                        $opt_long_desc => {
                                            let next = it.next()
                                                .ok_or_else(|| $crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::ExpectedArgFollowing(stringify!($opt_long_desc))))?
                                                .map_err(|e| $crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::NotUtf8(e)))?;
                                            $optional_field = Some(<$opt_ty>::from_str(next)
                                                .map_err(|_err| $crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::FailedParse(stringify!($optional_field))))?
                                            );
                                        },
                                    )*
                                    $(
                                        $rep_long_desc => {
                                            let next = it.next()
                                                .ok_or_else(|| $crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::ExpectedArgFollowing(stringify!($rep_long_desc))))?
                                                .map_err(|e| $crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::NotUtf8(e)))?;
                                            $repeating_field.push(<$rep_ty>::from_str(next)
                                                .map_err(|_err| $crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::FailedParse(stringify!($repeating_field))))?);
                                        },
                                    )*
                                    arg => return Err($crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::UnrecognizedArg(arg.to_string()))),
                                }
                            } else if let Some((a, b)) = n.split_once('-') {
                                if !a.is_empty() {
                                    return Err($crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::NoDashStart));
                                }
                                match b {
                                    $(
                                        $short_desc => {
                                            let next = it.next()
                                                .ok_or_else(|| $crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::ExpectedArgFollowing(stringify!($short_desc))))?
                                                .map_err(|e| $crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::NotUtf8(e)))?;
                                            $required_field = Some(<$req_ty>::from_str(next)
                                                .map_err(|_err| $crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::FailedParse(stringify!($required_field))))?
                                            );
                                        },
                                    )*
                                    $(
                                        $opt_short_desc => {
                                            let next = it.next()
                                                .ok_or_else(|| $crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::ExpectedArgFollowing(stringify!($opt_short_desc))))?
                                                .map_err(|e| $crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::NotUtf8(e)))?;
                                            $optional_field = Some(<$opt_ty>::from_str(next)
                                                .map_err(|_err| $crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::FailedParse(stringify!($optional_field))))?
                                            );
                                        },
                                    )*
                                    $(
                                        $rep_short_desc => {
                                            let next = it.next()
                                                .ok_or_else(|| $crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::ExpectedArgFollowing(stringify!($rep_short_desc))))?
                                                .map_err(|e| $crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::NotUtf8(e)))?;
                                            $repeating_field.push(<$rep_ty>::from_str(next)
                                                .map_err(|_err| $crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::FailedParse(stringify!($repeating_field))))?);
                                        },
                                    )*
                                    arg => return Err($crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::UnrecognizedArg(arg.to_string()))),
                                }
                            } else {
                                return Err($crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::NoDashStart))
                            }
                        } else {
                            match n {
                                $(
                                    $sc_name => $subcommand = Some(<$sc_ty>::parse(it)?),
                                )*
                                _ => {
                                    return Err($crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::NoDashStart));
                                }
                            }
                        }
                    } else {
                        break;
                    }
                }
                Ok(Self {
                    $($required_field: $required_field.ok_or_else(|| $crate::ArgParseError::new(Self::gen_help(), $crate::ArgParseCause::MissingRequiredField(stringify!($required_field))))?,)*
                    $($optional_field,)*
                    $($repeating_field,)*
                    $($subcommand,)*
                })

            }
        }

        impl $ArgStruct {
            #[inline(never)]
            fn gen_help() -> alloc::string::String {
                use core::fmt::Write;
                let mut help = alloc::format!("Usage: {} [OPTIONS] [COMMAND] ...\n{}\n", $name, $app_desc);
                $(
                    let _ = help.write_fmt(format_args!("  -{}, --{} {}\n", $short_desc, $long_desc, $desc));
                )*
                $(
                    let _ = help.write_fmt(format_args!("  -{}, --{} [OPTIONAL] {}\n", $opt_short_desc, $opt_long_desc, $opt_desc));
                )*
                $(
                    let _ = help.write_fmt(format_args!("  -{}, --{} [REPEATING] {}\n", $rep_short_desc, $rep_long_desc, $rep_desc));
                )*
                $(
                    let _ = help.write_fmt(format_args!("[COMMAND] {}\n", $sc_name));
                )*
                help
            }
        }


    }
}

pub trait Parser: Sized {
    /// Attempts to construct `Self` from provided arguments.
    /// # Errors
    /// Parsing errors, see `ArgParseCause`
    fn parse<'a>(
        it: &mut impl Iterator<Item = Result<&'a str, Utf8Error>>,
    ) -> Result<Self, ArgParseError>;
}

#[cfg(test)]
mod tests {
    use super::*;
    use alloc::string::ToString;
    use alloc::vec;
    arg_parse! (
            #[name("My has all but subcommand cli")]
            #[description("Use for fun and profit")]
            #[derive(Debug)]
            pub struct UseAllKindsArgs {
                #[short("f"), long("field-1"), description("My first field")]
                my_field: i32,
                #[short("m"), long("field-2"), description("My second field")]
                my_field2: i32,
                #[optional]
                #[short("n"), long("opt-missing"), description("My optional field, don't fill")]
                my_opt_field_missing: Option<u32>,
                #[optional]
                #[short("o"), long("opt"), description("My optional field, fill")]
                my_opt_field_present: Option<u32>,
                #[repeating]
                #[short("r"), long("rep"), description("My repeating field")]
                my_rep_field: Vec<i128>,
            }
    );

    #[test]
    fn happy_case_regular_command() {
        let mut args = [
            Ok("--field-1"),
            Ok("15"),
            Ok("-m"),
            Ok("19"),
            Ok("-o"),
            Ok("3"),
            Ok("--rep"),
            Ok("1000"),
            Ok("--rep"),
            Ok("2000"),
            Ok("--rep"),
            Ok("3000"),
        ]
        .into_iter();
        let ma = UseAllKindsArgs::parse(&mut args).unwrap();
        assert_eq!(15, ma.my_field);
        assert_eq!(19, ma.my_field2);
        assert!(ma.my_opt_field_missing.is_none());
        assert_eq!(3, ma.my_opt_field_present.unwrap());
        assert_eq!(vec![1000, 2000, 3000], ma.my_rep_field);
    }

    #[test]
    fn unrecognized_field_bad_long() {
        let mut args = [
            // No field-11
            Ok("--field-11"),
            Ok("15"),
            Ok("-m"),
            Ok("19"),
            Ok("-o"),
            Ok("3"),
            Ok("--rep"),
            Ok("1000"),
            Ok("--rep"),
            Ok("2000"),
            Ok("--rep"),
            Ok("3000"),
        ]
        .into_iter();
        match UseAllKindsArgs::parse(&mut args) {
            Ok(_) => {
                panic!("Expected error");
            }
            Err(e) => {
                let bad_match = "field-11".to_string();
                assert_eq!(e.cause, ArgParseCause::UnrecognizedArg(bad_match));
            }
        }
    }

    #[test]
    fn unrecognized_field_bad_short() {
        let mut args = [
            // No k
            Ok("-k"),
            Ok("15"),
            Ok("-m"),
            Ok("19"),
            Ok("-o"),
            Ok("3"),
            Ok("--rep"),
            Ok("1000"),
            Ok("--rep"),
            Ok("2000"),
            Ok("--rep"),
            Ok("3000"),
        ]
        .into_iter();
        match UseAllKindsArgs::parse(&mut args) {
            Ok(_) => {
                panic!("Expected error");
            }
            Err(e) => {
                let bad_match = "k".to_string();
                assert_eq!(e.cause, ArgParseCause::UnrecognizedArg(bad_match));
            }
        }
    }

    #[test]
    fn err_in_it() {
        let invalid_utf8 = b"\xc3\x28";
        let e = core::str::from_utf8(invalid_utf8).err().unwrap();
        let mut args = [Err(e)].into_iter();
        match UseAllKindsArgs::parse(&mut args) {
            Ok(_) => {
                panic!("Expected error");
            }
            Err(e) => {
                assert!(matches!(e.cause, ArgParseCause::NotUtf8(_)));
            }
        }
    }

    #[test]
    fn unrecognized_field_no_dash_no_subcommand() {
        let mut args = [
            // No k
            Ok("hello"),
            Ok("15"),
            Ok("-m"),
            Ok("19"),
            Ok("-o"),
            Ok("3"),
            Ok("--rep"),
            Ok("1000"),
            Ok("--rep"),
            Ok("2000"),
            Ok("--rep"),
            Ok("3000"),
        ]
        .into_iter();
        match UseAllKindsArgs::parse(&mut args) {
            Ok(_) => {
                panic!("Expected error");
            }
            Err(e) => {
                assert!(matches!(e.cause, ArgParseCause::NoDashStart));
            }
        }
    }

    arg_parse!(
        #[name("My nested command")]
        #[description("Use this nested subcommand for fun and profit")]
        pub struct NestedSc {
            #[short("f"), long("field-1"), description("My first field")]
            my_sc_field: String,
            #[short("s"), long("sc-field"), description("My sc second field")]
            my_other_sc_field: i64,
        }
    );
    arg_parse!(
        #[name("My first first level subcommand")]
        #[description("Use this nested subcommand for fun and profit")]
        pub struct ScOne {
            #[short("h"), long("has-field"), description("My first field")]
            my_sc_field: String,
            #[subcommand("nested")]
            nested: Option<NestedSc>,
        }
    );
    arg_parse!(
        #[name("My second first level subcommand")]
        #[description("Use this nested subcommand for fun and profit")]
        pub struct ScTwo {
            #[optional]
            #[short("h"), long("has-field"), description("My first field")]
            opt_option: Option<String>,
        }
    );
    arg_parse!(
        #[name("My top level command")]
        #[description("Use top level command with subcommands for fun and profit")]
        pub struct Mc {
            #[short("m"), long("my-field"), description("My first field")]
            my_field: String,

            #[subcommand("first-sub")]
            subcommand_one: Option<ScOne>,

            #[subcommand("second-sub")]
            subcommand_two: Option<ScTwo>,
        }
    );

    #[test]
    fn subcommand_dont_invoke() {
        let mut args = [Ok("-m"), Ok("Hello!")].into_iter();
        let mc = Mc::parse(&mut args).unwrap();
        assert_eq!("Hello!", mc.my_field);
    }

    #[test]
    fn subcommand_invoke_first_fail_on_required_args() {
        let mut args = [Ok("-m"), Ok("Hello!"), Ok("first-sub")].into_iter();
        match Mc::parse(&mut args) {
            Ok(_) => {
                panic!("Expected error");
            }
            Err(e) => {
                assert!(matches!(
                    e.cause,
                    ArgParseCause::MissingRequiredField("my_sc_field")
                ));
            }
        }
    }

    #[test]
    fn subcommand_invoke_first_success() {
        let mut args = [
            Ok("-m"),
            Ok("Hello!"),
            Ok("first-sub"),
            Ok("--has-field"),
            Ok("Hello there field!"),
        ]
        .into_iter();
        let mc = Mc::parse(&mut args).unwrap();
        assert_eq!("Hello!", mc.my_field);
        assert!(mc.subcommand_two.is_none());
        let sub = mc.subcommand_one.unwrap();
        assert_eq!("Hello there field!", sub.my_sc_field);
    }

    #[test]
    fn subcommand_invoke_second_success() {
        let mut args = [
            Ok("-m"),
            Ok("Hello!"),
            Ok("second-sub"),
            Ok("--has-field"),
            Ok("Give opt!"),
        ]
        .into_iter();
        let mc = Mc::parse(&mut args).unwrap();
        assert_eq!("Hello!", mc.my_field);
        assert!(mc.subcommand_one.is_none());
        let sub = mc.subcommand_two.unwrap();
        assert_eq!("Give opt!", sub.opt_option.unwrap());
    }

    #[test]
    fn subcommand_invoke_first_nested_success() {
        let mut args = [
            Ok("-m"),
            Ok("Hello!"),
            Ok("first-sub"),
            Ok("--has-field"),
            Ok("provided"),
            Ok("nested"),
            Ok("--field-1"),
            Ok("provided-nested"),
            Ok("--sc-field"),
            Ok("555"),
        ]
        .into_iter();
        let mc = Mc::parse(&mut args).unwrap();
        assert_eq!("Hello!", mc.my_field);
        assert!(mc.subcommand_two.is_none());
        let sub = mc.subcommand_one.unwrap();
        assert_eq!("provided", sub.my_sc_field);
        let nested = sub.nested.unwrap();
        assert_eq!("provided-nested", nested.my_sc_field);
        assert_eq!(555, nested.my_other_sc_field);
    }
}
