module

public import CFSG.Sporadic.Co2Jc.Words
public import CFSG.Sporadic.Co2Jc.Data.Orbits

public section

namespace CFSG.Sporadic.Co2Jc.Native

open CFSG.Sporadic.Co2Jc.Data

set_option compiler.extract_closed false

@[expose] def labAt (m : Nat) : Nat := Data.lab[m]!

@[expose] def repAt (l : Nat) : Nat := Data.rep[l]!

@[expose] def parAt (m : Nat) : Nat := Data.par[m]!

@[expose] def depAt (m : Nat) : Nat := Data.dep[m]!

@[expose] def classCoords (l : Nat) : Finset Nat :=
  (Finset.range 1024).filter fun m => labAt m == l

@[expose] def classCount (l : Nat) : Nat := (classCoords l).card

@[expose] def classSizeAt (l : Nat) : Nat := Data.classSize[l]!

@[expose] def fCoords (x : Nat) : Finset Nat :=
  (Finset.range 1024).filter fun s =>
    (labAt s == 1 || labAt s == 3) && (labAt (s ^^^ x) == 1 || labAt (s ^^^ x) == 3)

@[expose] def fCount (x : Nat) : Nat := (fCoords x).card

@[expose] def labSizeChk : Bool :=
  (Data.lab.size == 1024) && (Data.rep.size == 4) && (Data.par.size == 1024) &&
    (Data.dep.size == 1024)

@[expose] def repChk : Bool :=
  (repAt 0 == 0) && (repAt 1 == 1) && decide (repAt 2 < 1024) &&
    decide (repAt 3 < 1024) && (repAt 3 == 40) && (labAt (repAt 1) == 1) &&
    (labAt (repAt 2) == 2) && (labAt (repAt 3) == 3)

@[expose] def labZeroChk : Bool := labAt 0 == 0

@[expose] def labValChk : Bool :=
  (List.range 1024).all fun m =>
    decide (m = 0 ∨ labAt m = 1 ∨ labAt m = 2 ∨ labAt m = 3)

@[expose] def labOmChk : Bool :=
  (List.range 1024).all fun m => decide (labAt m = 1 ↔ m ∈ Co2Smith.Native.glNJOm)

@[expose] def labStepChk : Bool :=
  (List.range 3).all fun k => (List.range 1024).all fun m =>
    decide (Co2Smith.Native.glNJT k m < 1024 ∧
      labAt (Co2Smith.Native.glNJT k m) = labAt m)

@[expose] def classSizeChk : Bool :=
  classCount 1 == classSizeAt 1 && classCount 2 == classSizeAt 2 &&
    classCount 3 == classSizeAt 3

@[expose] def treeChk : Bool :=
  (depAt (repAt 1) == 0) && (depAt (repAt 2) == 0) && (depAt (repAt 3) == 0) &&
    (List.range 1024).all fun m =>
      decide (m = 0 ∨ (m = repAt (labAt m) ∧ depAt m = 0) ∨
        (parAt m < 1024 ∧ depAt (parAt m) + 1 = depAt m ∧ labAt (parAt m) = labAt m ∧
          (wordAct g1w (parAt m) = m ∨ wordAct g2w (parAt m) = m)))

@[expose] def fixedChk : Bool :=
  (List.range 1024).all fun m =>
    decide ((wordAct [1] m = m ∧ wordAct [0, 0] m = m) ↔ (m = 0 ∨ m = 1))

@[expose] def fChk : Bool :=
  (fCount 1 == 392) && (fCount 40 == 452)

@[expose] def orbitsChecks : List Bool :=
  [labSizeChk, repChk, labZeroChk, labValChk, labOmChk, labStepChk, classSizeChk,
    treeChk, fixedChk, fChk]

@[expose] def orbitsOK : Bool := orbitsChecks.all id

end CFSG.Sporadic.Co2Jc.Native
