module

public section

namespace CFSG.F4.Native

@[expose] def t46XYWord (s : String) : List Int := s.toList.map fun c => if c == 'x' then 1 else 2

@[expose] def t46SubRoot (_ : Unit := ()) : Nat := 11

@[expose] def t46TvWords (_ : Unit := ()) : Array (List Int) := #[
    "xyxyxyyxyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyyxyxyyxyyx",
    "xyxyyxyyxyxyyxyyxyyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyxyxyxyyxyxyxyyx",
    "xyyxyxyyxyxyxyyxyxyyxyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyyxyxyyxyxyyxyyxyxyyxyx",
    "xyxyyxyxyxyyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyxyyxyyxyxyyx",
    "yyxyxyyxyyxyxyxyyxyyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyxyxyyxyyxyxyxyyxy",
    "yxyyxyyxyxyyxyyxyxyxyyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyxyyxyyxyxyxyyxyxyxyy",
    "yyxyxyyxyxyyxyyxyxyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyyxyyxyxyxyyxyxyyxy",
    "yyxyxyxyyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyxyyxyyxy",
    "yyxyyxyyxyyxyyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyxyxyxyxy",
    "xyyxyxyyxyyxyxyyxyyxyxyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyyxyyxyxyxyyxyxyxyyxyx",
    "xyyxyyxyxyxyyxyyxyxyxyyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyxyyxyyxyxyxyyxyyxyxyx",
    "yxyxyyxyxyyxyyxyxyxyyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyxyyxyyxyxyxyyxyxyyxyy",
    "xyyxyxyxyyxyxyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyyxyyxyxyyxyyxyx",
    "yyxyyxyxyxyyxyyxyxyxyyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyxyyxyyxyxyxyyxyyxyxy",
    "xyyxyxyyxyxyxyyxyyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyxyxyyxyyxyxyyxyx",
    "xyyxyyxyxyyxyyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyxyxyyxyxyx",
    "yyxyyxyxyxyxyyxyyxyyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyxyxyxyyxyyxyyxyxy",
    "yxyyxyxyyxyyxyxyxyyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyxyyxyyxyxyxyyxyxyy",
    "xyyxyxyyxyyxyxyyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyxyyxyxyxyyxyx",
    "yyxyxyyxyxyxyyxyyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyxyxyyxyyxyxyyxy",
    "xyxyxyxyxyyxyxyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyyxyyxyxyyxyyxyyxyyx",
    "yxyyxyxyyxyxyxyyxyyxyyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyxyxyxyyxyyxyxyyxyxyy",
    "yxyyxyyxyxyyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyxyyxyxyxyy",
    "yyxyyxyxyyxyxyxyyxyyxyxyyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyxyyxyxyxyyxyyxyxyyxyxy",
    "yxyxyxyxyyxyxyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyyxyyxyxyyxyyxyyxyy",
    "yxyxyyxyyxyyxyxyyxyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyyxyxyyxyxyxyxyyxyy",
    "yyxyxyxyyxyxyxyyxyyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyxyxyyxyyxyxyyxyyxy",
    "xyxyyxyxyyxyyxyxyxyyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyxyyxyyxyxyxyyxyxyyx",
    "yxyyxyxyyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyxyyxyxyy",
    "yxyxyxyxyxyyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyxyyxyyxyyxyyxyy",
    "yxyxyxyyxyyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyxyxyyxyyxyy",
    "yyxyxyxyyxyxyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyyxyyxyxyyxyyxy",
    "xyxyyxyyxyxyyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyxyyxyxyxyyx",
    "yxyxyyxyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyyxyxyyxyy",
    "yxyyxyxyxyyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyxyyxyyxyxyy",
    "yyxyyxyyxyxyxyyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyxyyxyyxyxyxy",
    "yyxyxyyxyyxyxyyxyyxyxyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyyxyyxyxyxyyxyxyxyyxy",
    "yyxyxyyxyyxyxyyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyxyyxyxyxyyxy",
    "yyxyxyyxyxyxyyxyxyyxyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyyxyxyyxyxyyxyyxyxyyxy",
    "xyyxyxyxyyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyxyyxyyxyx",
    "yxyyxyxyxyyxyxyyxyyxyxyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyyxyyxyxyxyyxyxyyxyyxyxyy",
    "yyxyyxyxyyxyyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyxyxyyxyxy",
    "yxyyxyxyyxyxyyxyxyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyyxyyxyxyyxyxyyxyxyy",
    "yxyyxyyxyxyyxyyxyyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyxyxyxyyxyxyxyy",
    "yxyyxyxyxyxyxyyxyyxyyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyxyxyxyyxyyxyyxyyxyxyy",
    "xyxyxyyxyxyxyxyyxyxyyxyxyyxyxyyxyxyyxyxyxyyxyxyyxyyx"].map t46XYWord

end CFSG.F4.Native
