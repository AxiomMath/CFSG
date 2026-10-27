module

public import Certificates.Data.TitsAschbacherE32
public import Certificates.Data.TitsFiveLocal
public import CFSG.Sporadic.Schreier.TitsCentralCheckInputs

public section

namespace Certificates.TitsAschbacherFive

open CFSG.Sporadic.Schreier.Tits CFSG.Monster.B.Co2.Native Certificates.TitsAschbacherParrott
  Certificates.TitsAschbacherE32 Certificates.MaxD2Perm CFSG.PSL3Four.Native

@[expose] def u2Word : List ℕ := [1, 0, 2, 1, 2]

@[expose] def deltaHWord : List ℕ := [1, 2, 2, 2, 0, 2]

@[expose] def deltaAWord : List ℤ :=
  [-2, 1, -2, -1, 2, 1, 1, -2, 1, -2, -1, 2, -1, 2, 2, -1, 2, -1, -2, -1, -2, 1, 2, -1, -2, -1,
    -2, -1, 2, 2, 2, 1, 2, 1, -2, -1, -2, 1, 1, 2, 2, 1, 2, -1, 2, -1, -2, -1, -2, 1, 2, -1, -1,
    -1, -2, 1, 2, -1, 2]

@[expose] def deltaBWord : List ℤ := [-2, 1, -2, -1, 2, 1, 1, -2]

@[expose] def deltaExp : ℕ := 2

@[expose] def u2Arr (_ : Unit) : Array ℕ := hArr u2Word

@[expose] def deltaArr (_ : Unit) : Array ℕ :=
  compA 1755 (compA 1755 (hArr deltaHWord)
    (powA (compA 1755 (wT titsDData deltaAWord) titsZArr) deltaExp)) (wT titsDData deltaBWord)

@[expose] def transCheck (_ : Unit) : Bool :=
  let rT := (rEnum titsDData).tabs
  let nT := (nEnum titsDData).tabs
  let uT := wT titsDData titsDData.uW
  allBelow rT.size fun k => rT[k]! == idTab 1755 ||
    anyBelow nT.size fun j => eqA 1755 (compA 1755 nT[j]! uT) (compA 1755 rT[k]! nT[j]!)

@[expose] def fiveCheck (_ : Unit) : Bool :=
  hLetters u2Word && hLetters deltaHWord &&
    eqA 1755 (compA 1755 (u2Arr ()) xArr) (compA 1755 (powA xArr 3) (u2Arr ())) &&
    eqA 1755 (compA 1755 (u2Arr ()) (u2Arr ())) (compA 1755 titsZArr (vA 2)) &&
    eqA 1755 (compA 1755 (deltaArr ()) (wT titsDData titsDData.uW))
      (compA 1755 xArr (deltaArr ())) &&
    transCheck ()

end Certificates.TitsAschbacherFive
