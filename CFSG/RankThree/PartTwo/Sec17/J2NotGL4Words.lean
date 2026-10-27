module

public import Aesop.BuiltinRules
public import Mathlib.Data.Nat.Notation
public import Mathlib.Tactic.Attr.Core

public section

namespace CFSG.RankThree.PartTwo.Sec17.J2NotGL4

@[expose] def parseW (s : String) : List (ℕ × Bool) :=
  s.toList.map fun c => if c = 's' then (0, true) else if c = 't' then (1, true) else (1, false)

abbrev pw (w : List (ℕ × Bool)) (k : ℕ) : List (ℕ × Bool) := (List.replicate k w).flatten

@[expose] def wx7 : List (ℕ × Bool) := parseW "ststsTst"

@[expose] def wy7 : List (ℕ × Bool) := parseW "sTsTstsTsTstsTstsTstsTststsTstsTstsTsT"

@[expose] def wa5 : List (ℕ × Bool) := parseW "sTstsTststsTstsTstsTstsTsTst"

@[expose] def wb5 : List (ℕ × Bool) := parseW "sTstsTstsTsTstsTstsTststsTst"

@[expose] def wy5 : List (ℕ × Bool) := parseW "TststsTstsTsts"

end CFSG.RankThree.PartTwo.Sec17.J2NotGL4
