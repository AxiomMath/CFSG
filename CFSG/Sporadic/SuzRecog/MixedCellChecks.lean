module

public import CFSG.Sporadic.SuzRecog.MixedCellCollapse
public import CFSG.Sporadic.SuzRecog.RootTwistChecks

public section

namespace CFSG.Sporadic.SuzRecog.MixedCellCheck

open CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzOddCore
  CFSG.Sporadic.SuzRecog.LevelTwoData CFSG.Sporadic.SuzRecog.ModelGroupsCheck
  CFSG.Sporadic.SuzRecog.B0TwistData CFSG.Sporadic.SuzRecog.MixedCellData
  CFSG.Sporadic.SuzRecog.MixedCell

@[expose] def p1A : Array Nat := LevelTwo.aPts[LevelTwo.p1]!

@[expose] def sA : Array Nat := LevelTwo.swapE.1

@[expose] def cA (k : Nat) : Array Nat := (LevelTwo.cellC k).1

@[expose] def cpA (k : Nat) : Array Nat := (LevelTwo.cellC' k).1

@[expose] def eA (k : Nat) : Array Nat := compA 1782 (invCand 1782 (cA k)) (compA 1782 sA (cpA k))

@[expose] def conjInvA (g a : Array Nat) : Array Nat := compA 1782 (invCand 1782 g) (compA 1782 a g)

@[expose] def boundW (k : Nat) : List (List Nat) := if k = 0 then boundW0 else boundW2

@[expose] def wA : Array Nat := compA 1782 t1A p1A

@[expose] def mcGens : Array (Array Nat) := #[h1Arr, h2Arr, rhoArr, aArr, bArr, sA, tauA, w0Arr]

@[expose] def mcCodeA (c : Nat) : Array Nat :=
  if c % 2 = 0 then mcGens[c / 2]! else invCand 1782 mcGens[c / 2]!

@[expose] def mcWordA : List Nat → Array Nat
  | [] => idA 1782
  | c :: w => compA 1782 (mcCodeA c) (mcWordA w)

@[expose] def codesLt (n : Nat) (w : List Nat) : Bool := w.all fun c => decide (c < n)

@[expose] def codesPsi (w : List Nat) : Bool := w.all fun c => decide (4 ≤ c ∧ c < 10)

@[expose] def codesBound (w : List Nat) : Bool :=
  w.all fun c => decide (c < 6 ∨ (12 ≤ c ∧ c < 16))

@[expose] def mcPermsOK : Bool :=
  permOK h1Arr && permOK h2Arr && permOK aArr && permOK bArr && permOK p1A && permOK sA &&
    permOK (cA 0) && permOK (cpA 0) && permOK (cA 2) && permOK (cpA 2)

@[expose] def mcMembersOK : Bool := inM h1Arr && inM h2Arr && inM aArr && inM bArr

@[expose] def mcCommOK : Bool :=
  commA h1Arr t1A && commA h1Arr rhoArr && commA h2Arr t1A && commA h2Arr rhoArr &&
    commA aArr rhoArr && normR0 aArr && commA bArr rhoArr && normR0 bArr

@[expose] def mcLettersOK : Bool :=
  relsH1.all (codesLt 6) && relsH2.all codesPsi &&
    relsA.all (fun p => codesLt 6 p.1 && codesPsi p.2) &&
    edge.all (fun p => codesLt 6 p.1 && codesLt 6 p.2) && codesLt 6 sq &&
    [0, 2].all (fun k => codesLt 6 (cW k) && codesLt 6 (cpW k) && codesPsi (eW k) &&
      (deltaW k).all (codesLt 4) && decide ((deltaW k).length = 16) &&
      (boundW k).all codesBound) &&
    codesLt 4 kGenAW && codesLt 4 kGenBW && codesLt 4 xW

@[expose] def mcRelsOK : Bool :=
  (relsH1 ++ relsH2).all (fun w => eqA 1782 (mcWordA w) (idA 1782)) &&
    relsA.all (fun p => eqA 1782 (mcWordA p.1) (mcWordA p.2)) &&
    edge.all (fun p =>
      commA (mcWordA p.1) p1A && eqA 1782 (mcWordA p.2) (conjA sA (mcWordA p.1))) &&
    eqA 1782 (mcWordA sq) (compA 1782 sA sA)

@[expose] def mcCellsOK : Bool :=
  [0, 2].all (fun k => eqA 1782 (mcWordA (cW k)) (cA k) && eqA 1782 (mcWordA (cpW k)) (cpA k) &&
      eqA 1782 (mcWordA (eW k)) (eA k) && decide ((deltaW k).getD 0 [0] = []) &&
      eqA 1782 (mcWordA ((deltaW k).getD 1 [])) wA) &&
    eqA 1782 (mcWordA kGenAW) RootTwistData.kGenAArr &&
    eqA 1782 (mcWordA kGenBW) RootTwistData.kGenBArr &&
    eqA 1782 (conjA sA t1A) p1A && eqA 1782 (conjA sA p1A) t1A

@[expose] def mcBoundOK (k : Nat) : Bool :=
  let ms := (boundW k).map mcWordA
  let ds := (deltaW k).map mcWordA
  decide ((boundW k).getD 0 [] = [4]) && eqA 1782 (mcWordA ((boundW k).getD 1 [])) t1A &&
    ms.all (fun m => commA m p1A && normR0 (conjInvA (cpA k) m) &&
      commA (conjA (eA k) (conjInvA (cpA k) m)) t1A && commA (conjA sA m) t1A) &&
    allLt 3456 fun i =>
      !(ms.all fun m => commA RootTwistCheck.kEls[i]! m) ||
        ds.any fun d => eqA 1782 RootTwistCheck.kEls[i]! d

@[expose] def mcRemarkOK : Bool :=
  let x := mcWordA xW
  commA x w0Arr && commA x w1A && eqA 1782 (conjA x tauA) (compA 1782 tauA t1A) &&
    eqA 1782 (compA 1782 x x) (idA 1782) &&
    C1Model.v0Enum.tabs.all (fun v => !commA v w1A || commA v x) &&
    badPairs.all fun t =>
      [(0, t.1), (2, t.2.1)].all fun kn =>
        let a := conjA (cA kn.1) x
        let b := conjA (cpA kn.1) x
        let d := mcWordA ((deltaW kn.1).getD kn.2 [])
        eqA 1782 (compA 1782 (conjInvA sA a) (compA 1782 d b))
            (if t.2.2 = 0 then idA 1782 else wA) &&
          commA a p1A && commA (conjInvA sA a) t1A

end CFSG.Sporadic.SuzRecog.MixedCellCheck
