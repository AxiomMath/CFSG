module

public import Certificates.Data.SuzModelGroupsInputs
public import CFSG.Sporadic.SuzRecog.C1ModelTests

public section

namespace CFSG.Sporadic.SuzRecog.ModelGroupsCheck

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Sporadic.SuzRecog.LevelTwoData
  CFSG.Sporadic.SuzRecog.ModelGroupsData CFSG.Sporadic.SuzOddCore

@[expose] def conjA (g a : Array Nat) : Array Nat := compA 1782 g (compA 1782 a (invCand 1782 g))

@[expose] def permOK (g : Array Nat) : Bool := isInvA 1782 g (invCand 1782 g)

@[expose] def commA (g h : Array Nat) : Bool := eqA 1782 (compA 1782 g h) (compA 1782 h g)

@[expose] def inZ (r x : Array Nat) : Bool := eqA 1782 x r || eqA 1782 x (compA 1782 r r)

@[expose] def t1A : Array Nat := tArr 1

@[expose] def rho2A : Array Nat := conjA w0Arr rhoArr

@[expose] def w1A : Array Nat := conjA rhoArr w0Arr

@[expose] def w2A : Array Nat := compA 1782 w0Arr w1A

@[expose] def zA : Array Nat := C1Model.zT

@[expose] def tauA : Array Nat := C1Model.tauT

@[expose] def aA : Array Nat := c1Strong 0

@[expose] def bA : Array Nat := c1Strong 1

@[expose] def r0A (r : Nat) : Array Nat :=
  if r = 0 then idA 1782 else if r = 1 then w0Arr else if r = 2 then w1A else w2A

@[expose] def a4A (i : Nat) : Array Nat := compA 1782 (r0A (i / 3)) (powA 1782 rhoArr (i % 3))

@[expose] def e8A (i : Nat) : Array Nat := compA 1782 (r0A (i / 2)) (powA 1782 tauA (i % 2))

@[expose] def inR0 (x : Array Nat) : Bool := eqA 1782 x w0Arr || eqA 1782 x w1A || eqA 1782 x w2A

@[expose] def normR0 (g : Array Nat) : Bool := inR0 (conjA g w0Arr) && inR0 (conjA g w1A)

@[expose] def pairA (g : Array Nat) : Bool :=
  (inZ rhoArr (conjA g rhoArr) && inZ rho2A (conjA g rho2A)) ||
    (inZ rho2A (conjA g rhoArr) && inZ rhoArr (conjA g rho2A))

@[expose] def a4Idx (x : Array Nat) : Nat :=
  ((List.range 12).find? fun j => eqA 1782 x (a4A j)).getD 12

@[expose] def chainOK (S : Array (Array Nat)) (k : Nat) (base : List Nat) (W : Array (List Int))
    (orbits : List Nat) : Bool :=
  rawChainOK 1782 (S.extract 0 k) S base.toArray W 4 &&
    rawOrbitSizes 1782 S base.toArray == orbits

@[expose] def permsOK : Bool :=
  permOK rhoArr && permOK w0Arr && permOK aA && permOK bA && permOK s1Arr && permOK s2Arr

@[expose] def membersOK : Bool :=
  inM rhoArr && inM w0Arr && inM t1A && inM aA && inM bA && inM s1Arr && inM s2Arr

@[expose] def commOK : Bool :=
  commA t1A rhoArr && commA aA rhoArr && commA aA t1A && commA bA t1A && commA s1Arr t1A &&
    commA s2Arr t1A

@[expose] def basicOK : Bool :=
  eqA 1782 (powA 1782 rhoArr 3) (idA 1782) && !eqA 1782 rhoArr (idA 1782) &&
    eqA 1782 (compA 1782 rhoArr (invCand 1782 rho2A)) w2A && !inZ rho2A rhoArr

@[expose] def normOK : Bool := normR0 s2Arr

@[expose] def pairOK : Bool := pairA tauA && pairA bA && pairA s2Arr

@[expose] def a4OK : Bool :=
  allLt 12 (fun i => permOK (a4A i) &&
    decide (a4Idx (compA 1782 rhoArr (a4A i)) < 12) &&
    eqA 1782 (compA 1782 rhoArr (a4A i)) (a4A (a4Idx (compA 1782 rhoArr (a4A i)))) &&
    decide (a4Idx (compA 1782 rho2A (a4A i)) < 12) &&
    eqA 1782 (compA 1782 rho2A (a4A i)) (a4A (a4Idx (compA 1782 rho2A (a4A i)))) &&
    (i % 3 == 0 || !eqA 1782 (compA 1782 (a4A i) (a4A i)) (idA 1782))) &&
  allLt 12 fun i => allLt 12 fun j => i == j ||
    !inZ (conjA (a4A i) rhoArr) (conjA (a4A j) rhoArr) ||
    !inZ (conjA (a4A i) rho2A) (conjA (a4A j) rho2A)

@[expose] def cos8OK : Bool :=
  allLt 8 (fun i => permOK (e8A i)) &&
    allLt 8 fun i => allLt 8 fun j => i == j ||
      !eqA 1782 (conjA (e8A i) rhoArr) (conjA (e8A j) rhoArr)

@[expose] def nr0OK : Bool :=
  nr0StrongArrs.size == 9 && chainOK nr0StrongArrs 5 nr0Base nr0Words [42, 960, 12] &&
    eqA 1782 (nr0Strong 0) t1A && eqA 1782 (nr0Strong 1) zA && eqA 1782 (nr0Strong 2) w0Arr &&
    eqA 1782 (nr0Strong 3) rhoArr && eqA 1782 (nr0Strong 4) tauA

@[expose] def csplitOK : Bool :=
  csplitStrongArrs.size == 9 &&
    chainOK csplitStrongArrs 4 csplitBase csplitWords [162, 360, 56, 3] &&
    eqA 1782 (csplitStrong 0) t1A && eqA 1782 (csplitStrong 1) zA &&
    eqA 1782 (csplitStrong 2) rhoArr && eqA 1782 (csplitStrong 3) aA

@[expose] def c1OK : Bool :=
  c1StrongArrs.size == 11 && chainOK c1StrongArrs 2 c1Base c1Words [54, 20, 16, 12, 4, 2, 2]

@[expose] def j0rhoOK : Bool :=
  j0rhoStrongArrs.size == 7 && chainOK j0rhoStrongArrs 3 j0rhoBase j0rhoWords [120, 126, 4] &&
    eqA 1782 (j0rhoStrong 0) t1A && eqA 1782 (j0rhoStrong 1) zA &&
    eqA 1782 (j0rhoStrong 2) rhoArr

end CFSG.Sporadic.SuzRecog.ModelGroupsCheck
