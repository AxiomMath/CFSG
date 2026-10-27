module

public import CFSG.Sporadic.Schreier.RuJ49Check

public section

namespace CFSG.Sporadic.RuSchreier.J49.Sl2

open CFSG.Monster.B.Co2.Native

set_option compiler.extract_closed false

@[expose] def rowsText : String :=
  include_str "../../../Certificates/Data/CFSGNative/RuSchreier/ruJ49Sl2.txt"

@[expose] def parseRow (s : String) : ℕ × List ℤ :=
  match (s.splitOn " ").filterMap String.toInt? with
  | [] => (0, [])
  | k :: w => (k.toNat, w)

@[expose] def rows (_ : Unit := ()) : List (ℕ × List ℤ) :=
  ((rowsText.splitOn "\n").filter fun l => !l.isEmpty).map parseRow

@[expose] def wordOf (R : List (ℕ × List ℤ)) (k : ℕ) : List ℤ := (R.lookup k).getD []

@[expose] def dA (k : ℕ) : ℕ := k % 5

@[expose] def dB (k : ℕ) : ℕ := k / 5 % 5

@[expose] def dC (k : ℕ) : ℕ := k / 25 % 5

@[expose] def dD (k : ℕ) : ℕ := k / 125 % 5

@[expose] def enc (a b c d : ℕ) : ℕ := a + 5 * (b + 5 * (c + 5 * d))

@[expose] def keyMul (k l : ℕ) : ℕ :=
  enc ((dA k * dA l + dB k * dC l) % 5) ((dA k * dB l + dB k * dD l) % 5)
    ((dC k * dA l + dD k * dC l) % 5) ((dC k * dB l + dD k * dD l) % 5)

@[expose] def isSL (k : ℕ) : Bool := (dA k * dD k + 4 * (dB k * dC k)) % 5 == 1

@[expose] def slKeys (_ : Unit := ()) : List ℕ := (List.range 625).filter isSL

@[expose] def gkey (l : ℤ) : ℕ := if l = 1 then 533 else 107

@[expose] def keyProd : List ℤ → ℕ
  | [] => 126
  | l :: w => keyMul (gkey l) (keyProd w)

@[expose] def tabK (S Sinv : Array (Array ℕ)) (R : List (ℕ × List ℤ)) (k : ℕ) : Array ℕ :=
  wordA 4060 S Sinv (wordOf R k)

@[expose] def checkG (g0 g3 : Array ℕ) : Bool :=
  let S : Array (Array ℕ) := #[g0, g3]
  let Sinv : Array (Array ℕ) := #[ruInv g0, ruInv g3]
  let R := rows ()
  let ks := slKeys ()
  isInvA 4060 g0 (ruInv g0) && isInvA 4060 g3 (ruInv g3) &&
    (List.range 625).all (fun k => (wordOf R k).all fun l => l == 1 || l == 2) &&
    ks.all (fun k => keyProd (wordOf R k) == k) &&
    ks.all (fun k =>
      eqA 4060 (tabK S Sinv R (keyMul k 533)) (compA 4060 (tabK S Sinv R k) g0) &&
      eqA 4060 (tabK S Sinv R (keyMul k 107)) (compA 4060 (tabK S Sinv R k) g3)) &&
    ks.all (fun k => k == 126 || !eqA 4060 (tabK S Sinv R k) (idA 4060)) &&
    wordOf R 126 == [] && wordOf R 533 == [1] && wordOf R 107 == [2]

@[expose] def check (_ : Unit := ()) : Bool :=
  let T := tabs ()
  (wordList ()).length == 19 && (wordList ()).all (lettersOK 2) && checkG (tabOf T 0) (tabOf T 3)

end CFSG.Sporadic.RuSchreier.J49.Sl2
