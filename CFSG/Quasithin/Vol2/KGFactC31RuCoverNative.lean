module

public import CFSG.Sporadic.Recognition.RuMultiplierInputs
public import CFSG.Sporadic.Schreier.RuCheckCentersInputs

public section

namespace CFSG.Quasithin.KGC31.RuCover

open CFSG.CosetTable CFSG.LieType.Multipliers CFSG.Sporadic.Presentation.Ru.Exact
  CFSG.Sporadic.Bridge.SurjD.Native CFSG.Sporadic.Th.Native CFSG.Sporadic.Schreier.Tits
  CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.LieType.Multipliers.Tits
  CFSG.Sporadic.Recognition.RuMultiplier CFSG.Sporadic.RuSchreier

@[expose] def ruP1 : List (Fin gc × Bool) := toLetters gc ruSpec.surjWords[1]!

@[expose] def p0A (_ : Unit := ()) : Array ℕ := wordArr 16240 ruRhoArrs (zword ruP0)

@[expose] def p1A (_ : Unit := ()) : Array ℕ := wordArr 16240 ruRhoArrs (zword ruP1)

@[expose] def pA (_ : Unit := ()) : Array (Array ℕ) := #[p0A, p1A]

@[expose] def zA (_ : Unit := ()) : Array ℕ := compA 16240 p0A p0A

@[expose] def eW : List (List Int) := [
    [1, 1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -2, -1, -2, -1,
     -2, -1, -2, -1, -2, -1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 2,
     1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, -1, 2, -1, 2, -1, -2, -2, -1, 2, -1, -2, -2, -1, 2, -1,
     -2, -2, -1, -2, -1, -2, -1, -2, -2, -1, -1, -2, -2, -1, -2, -1, 2, -1, -2, -2, -1, -2, -1,
     2, -1, 2, 2, 1, -2, 1, 2, 1, 2, 1, -2, 1, 2, 1, 2, 1, -2, -2],
    [2, 1, -2, 1, 2, 1, 2, 2, 1, -2, 1, -2, 1, 2, 1, -2, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1,
     -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, 1, 2, 1, 2, 1, -2, -1,
     -2, -2, -1, -2, -1, 2, -1, 2, -1, -2, -1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, -2, -1, -2, -1, -2,
     -1, -2, -1, -2, -1, -2, -1, -2, -2, -2, -2, -1, -1, -2, -2, -1, -1, -1, -2, -2, -2, -1, -2,
     -1, -1, -2, -2, -2, -1, -2, -2, -2, -1, -2, -1, -2, -2, -1, -2, -2, -2, -1, 2, -1, -2, -1,
     -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -2,
     -1, -2, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, 2, 1, 2, 2, 1, -2, 1, -2, 1, -2, 1, -2, 1,
     2, 1, -2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 1, 2, 2, 1, 2, 1, 2, 2, 1, -2, 1, 2, 1,
     2, 1, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 2, 1, 2, 1, 2,
     1, 2, 1],
    [1, 1, -2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -2, -1, 2, -1, -2, -1, -2, -1, -2,
     -1, -2, -1, -2, 1, 2, 1, 2, 1, 2, -1, -1, -2, -1, -2, -2, -1, -1, -1, -2, -2, -1, -2, -1,
     -2, -1, -1, -2, -1, -2, -2, 1, 2, 1, 2, 1, 2, 2, 1, -2, 1, 2, 1, -2, -1, -1, -1, -2, -1, -2,
     -2, -1, -1, -1, -2, -2, -1, -2, -1, -2, -1, -1, -2, -1, -2, -2, 1, 2, 1, 2, 1, 2, 2, 1, -2,
     1, 2, 1, -2, -1, -2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -2, -1, 2, 2, 1, 2, 1, 2, 1, 2,
     2, 1, -2, 1, 2, 1, -2, -1, -2, -1, -2, -1, -2, -1, -2, 1, 2, 1, 2, 1, 2, 1, -2, -2, -1, -2,
     -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -2, -1, 2, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1,
     -2, -2, -1, -2, -1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, -2, 1,
     -2, 1, 2, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, -2]]

@[expose] def nW : List (List Int) := [
    [1, 2, 1, 2, 2, 1, -2, 1, 2, 2, -1, -1, -2, -1, -2, -2, -1, -1, -1, -2, -2, -1, -2, -1, -2,
     -1, -1, -2, -1, -2, -2, 1, 2, 1, 2, 1, 2, 2, 1, -2, 1, 2, 1, -2, -1, -2, -1, -2, -1, -2, -1,
     -2, 1, 2, 1, 2, 1, 2, 2, -1, -2, -1, -2, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, 1, 2, 1,
     2, 1, 2, 2, 1, 2, 2, 1, 2, 1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -2, -2,
     -2, -1, -1, -2, -2, -1, -1, -1, -2, -2, -2, -1, -2, -1, -1, -2, -2, -2, -1, -2, -2, -2, -1,
     -2, -1, -2, -2, -1, -2, -2, -2, -1, 2, -1, -2, -1, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2,
     -1, -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1,
     2, -1, 2, -1, -2, -2, -2, -1, -1, -1, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, -2, -2, -1, 2,
     -1, 2, -1, -2, -1, -2, -1, 2, -1, 2, -1, -2, -2, -1, -2, -1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 2,
     1, 2, 1, 2, 2, 1, 2, 1, 2, 2, 1, -2, 1, -2, 1, 2, -1, -2, -1, -2, -1, -2, -2, -1, 2, -1, 2,
     -1, 2, -1, 2, 2, 1, -2, 1, -2, 1, -2, 1, 2, 2, 1, 2, 1, 2, 1, 2, 1, -2],
    [2, 1, -2, 1, -2, 1, -2, 1, 2, -1, 2, -1, 2, -1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1,
     2, 1, 2, 1, 2, 1, -2, 1, -2, 1, -2, 1, 2, 1, 2, 1, 2, 1, 2, 1, -2, -1, -2, -1, -2, -1, -2,
     -1, 2, 1, 2, 1, 2, 1, 2, 1, 2, -1, -2, -1, -2, -1, -2, -1, 2, 1, 2, 1, 2, 1, 2, 1, 2, 2, 2,
     -1, -2, -1, 2, -1, -2, -2, -1, -2, -1, -2, -1, -2, -1, 2, -1, 2, -1, 2, -1, -2, -1, -2, -1,
     -2, -1, -2, -1, -2, -1, 2, -1, -2, -1, -2, -1, -2, -1, -2, -1, -2, -1]]

@[expose] def tabC : List (List ℕ) := [[1, 4, 2], [2, 6, 7]]

@[expose] def eCode : List ℕ := [1, 2, 4, 6, 7, 3, 5]

@[expose] def prodA (n : ℕ) (S : Array (Array ℕ)) (c : ℕ) : Array ℕ :=
  (List.range 3).foldl (fun acc j => if c.testBit j then compA n acc S[j]! else acc) (idA n)

@[expose] def eA (i : ℕ) : Array ℕ := wordArr 16240 pA (eW.getD i [])

@[expose] def nA (j : ℕ) : Array ℕ := wordArr 16240 pA (nW.getD j [])

@[expose] def eArr (_ : Unit := ()) : Array (Array ℕ) := #[eA 0, eA 1, eA 2]

@[expose] def nArr (_ : Unit := ()) : Array (Array ℕ) := #[nA 0, nA 1]

@[expose] def aA (_ : Unit := ()) : Array (Array ℕ) := #[ruA0A, ruA1A]

@[expose] def coverChk16240 (_ : Unit := ()) : Bool :=
  let E := eArr
  let N := nArr
  let z := zA
  lettersOK gc (zword ruP0) && lettersOK gc (zword ruP1) && allPermsOK 16240 pA &&
    ((List.range 3).all fun i => lettersOK 2 (eW.getD i [])) &&
    ((List.range 2).all fun j => lettersOK 2 (nW.getD j [])) &&
    allPermsOK 16240 N &&
    ((List.range 3).all fun i => eqA 16240 (compA 16240 E[i]! E[i]!) (idA 16240)) &&
    ((List.range 3).all fun i => (List.range 3).all fun j =>
      eqA 16240 (compA 16240 E[i]! E[j]!) (compA 16240 E[j]! E[i]!)) &&
    ((List.range 8).all fun c => !eqA 16240 (prodA 16240 E c) z) &&
    (List.range 2).all fun j => (List.range 3).all fun i =>
      eqA 16240 (compA 16240 (compA 16240 N[j]! E[i]!) (invCand 16240 N[j]!))
        (prodA 16240 E ((tabC.getD j []).getD i 0))

@[expose] def coverChk4060 (_ : Unit := ()) : Bool :=
  let A := aA
  allPermsOK 4060 A &&
    ((List.range 3).all fun i => eqA 4060 (wordArr 4060 A (eW.getD i [])) ruEArr[i]!) &&
    eqA 4060 (wordArr 4060 A (nW.getD 0 [])) ruNs0A &&
    eqA 4060 (wordArr 4060 A (nW.getD 1 [])) ruNs1A &&
    (List.range 7).all fun k =>
      eqA 4060 ruEArr[k]! (prodA 4060 #[ruEArr[0]!, ruEArr[1]!, ruEArr[2]!] (eCode.getD k 0))

@[expose] def coverChk (_ : Unit := ()) : Bool := coverChk16240 && coverChk4060

end CFSG.Quasithin.KGC31.RuCover

end
