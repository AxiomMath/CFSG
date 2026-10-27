module

public import Certificates.Data.SuzRootTwistInputs
public import CFSG.Sporadic.SuzRecog.ModelGroupsChecks
public import CFSG.Sporadic.SuzRecog.LevelTwoCoverCheck

public section

namespace CFSG.Sporadic.SuzRecog.RootTwistCheck

open CFSG.Monster.B.Co2.Native CFSG.Sporadic.SuzRecog.LevelTwoData
  CFSG.Sporadic.SuzRecog.RootTwistData CFSG.Sporadic.SuzRecog.ModelGroupsCheck
  CFSG.Sporadic.SuzOddCore

@[expose] def aPrimeArr : Array Nat := LevelTwo.aPts[LevelTwo.p1]!

@[expose] def vRootArr : Array Nat := LevelTwo.wPts[135]!

@[expose] def vRoot'Arr : Array Nat := LevelTwo.wPts[55]!

@[expose] def vRoot1A : Array Nat := conjA rhoArr vRootArr

@[expose] def vRoot1A' : Array Nat := conjA rhoArr vRoot'Arr

@[expose] def inV (v v₁ z : Array Nat) : Bool :=
  eqA 1782 z v || eqA 1782 z v₁ || eqA 1782 z (compA 1782 v v₁)

@[expose] def normV (v v₁ g : Array Nat) : Bool := inV v v₁ (conjA g v) && inV v v₁ (conjA g v₁)

@[expose] def permsOK : Bool :=
  permOK rhoArr && permOK aPrimeArr && permOK vRootArr && permOK vRoot'Arr && permOK xTwArr &&
    permOK yTwArr

@[expose] def membersOK : Bool := inM rhoArr && inM xTwArr && inM yTwArr

@[expose] def commOK : Bool :=
  commA rhoArr t1A && commA rhoArr aPrimeArr && commA xTwArr t1A && commA xTwArr aPrimeArr &&
    commA yTwArr t1A && commA yTwArr aPrimeArr

@[expose] def normOK : Bool :=
  normV vRootArr vRoot1A rhoArr && normV vRootArr vRoot1A xTwArr &&
    normV vRoot'Arr vRoot1A' rhoArr && normV vRoot'Arr vRoot1A' yTwArr

@[expose] def sqOK : Bool :=
  eqA 1782 (powA 1782 rhoArr 3) (idA 1782) &&
    eqA 1782 (powA 1782 (compA 1782 xTwArr yTwArr) 2) (idA 1782) &&
    !eqA 1782 (powA 1782 (compA 1782 xTwArr (conjA rhoArr yTwArr)) 2) (idA 1782) &&
    !eqA 1782 (powA 1782 (compA 1782 xTwArr (conjA (powA 1782 rhoArr 2) yTwArr)) 2) (idA 1782)

@[expose] def evenOK : Bool :=
  commA (compA 1782 xTwArr (invCand 1782 rhoArr)) vRootArr &&
    commA (compA 1782 xTwArr (invCand 1782 rhoArr)) vRoot1A &&
    commA (compA 1782 yTwArr rhoArr) vRoot'Arr && commA (compA 1782 yTwArr rhoArr) vRoot1A'

@[expose] def kGens : Array (Array Nat) :=
  #[kGenAArr, kGenBArr, invCand 1782 kGenAArr, invCand 1782 kGenBArr]

@[expose] def kSearch : Array (Array Nat) × Array Nat × Array Nat := Id.run do
  let mut els : Array (Array Nat) := #[idA 1782]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut seen : Std.HashSet Nat := (∅ : Std.HashSet Nat).insert (LevelTwo.fp (idA 1782))
  for h in [0:3456] do
    if h < els.size then
      for s in [0:2] do
        let y := compA 1782 kGens[s]! els[h]!
        if !seen.contains (LevelTwo.fp y) then
          seen := seen.insert (LevelTwo.fp y)
          els := els.push y
          par := par.push h
          lab := lab.push s
  return (els, par, lab)

@[expose] def kEls : Array (Array Nat) := kSearch.1

@[expose] def kPar : Array Nat := kSearch.2.1

@[expose] def kLab : Array Nat := kSearch.2.2

@[expose] def kTab : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := ∅
  for i in [0:kEls.size] do
    m := m.insert (LevelTwo.fp kEls[i]!) i
  return m

@[expose] def kStep (i s : Nat) : Bool :=
  let y := compA 1782 kGens[s]! kEls[i]!
  let j := kTab.getD (LevelTwo.fp y) 3456
  decide (j < 3456) && eqA 1782 y kEls[j]!

@[expose] def kGenOK : Bool :=
  permOK kGenAArr && permOK kGenBArr && inM kGenAArr && inM kGenBArr &&
    commA kGenAArr t1A && commA kGenBArr t1A && commA kGenAArr rhoArr && commA kGenBArr rhoArr

@[expose] def kEnumOK : Bool :=
  kEls.size == 3456 && eqA 1782 kEls[0]! (idA 1782) &&
    allLt 3456 fun i =>
      permOK kEls[i]! && kTab.getD (LevelTwo.fp kEls[i]!) 3456 == i &&
        (i == 0 || (decide (kPar[i]! < i) && decide (kLab[i]! < 2) &&
          eqA 1782 kEls[i]! (compA 1782 kGens[kLab[i]!]! kEls[kPar[i]!]!))) &&
        allLt 4 fun s => kStep i s

@[expose] def kCentreOK : Bool :=
  allLt 3456 fun i =>
    !(commA kEls[i]! kGenAArr && commA kEls[i]! kGenBArr &&
        eqA 1782 (powA 1782 kEls[i]! 3) (idA 1782)) ||
      eqA 1782 kEls[i]! (idA 1782) || eqA 1782 kEls[i]! rhoArr ||
      eqA 1782 kEls[i]! (compA 1782 rhoArr rhoArr)

@[expose] def cGens : Array (Array Nat) := #[aA, bA]

irreducible_def rhoClassSearch : Array (Array Nat) × Array Nat × Array Nat := Id.run do
  let mut tr : Array (Array Nat) := #[idA 1782]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  let mut seen : Std.HashSet Nat := (∅ : Std.HashSet Nat).insert (LevelTwo.fp rhoArr)
  for h in [0:960] do
    if h < tr.size then
      for s in [0:2] do
        let g := compA 1782 cGens[s]! tr[h]!
        if !seen.contains (LevelTwo.fp (conjA g rhoArr)) then
          seen := seen.insert (LevelTwo.fp (conjA g rhoArr))
          tr := tr.push g
          par := par.push h
          lab := lab.push s
  return (tr, par, lab)

@[expose] def cTr : Array (Array Nat) := rhoClassSearch.1

@[expose] def cPar : Array Nat := rhoClassSearch.2.1

@[expose] def cLab : Array Nat := rhoClassSearch.2.2

@[expose] def cTab : Std.HashMap Nat Nat := Id.run do
  let mut m : Std.HashMap Nat Nat := ∅
  for i in [0:cTr.size] do
    m := m.insert (LevelTwo.fp (conjA cTr[i]! rhoArr)) i
  return m

@[expose] def classOK : Bool :=
  permOK aA && permOK bA && inM aA && inM bA && commA aA t1A && commA bA t1A &&
    cTr.size == 960 && eqA 1782 cTr[0]! (idA 1782) &&
    allLt 960 fun i =>
      permOK cTr[i]! && cTab.getD (LevelTwo.fp (conjA cTr[i]! rhoArr)) 960 == i &&
        (i == 0 || (decide (cPar[i]! < i) && decide (cLab[i]! < 2) &&
          eqA 1782 cTr[i]! (compA 1782 cGens[cLab[i]!]! cTr[cPar[i]!]!)))

@[expose] def hEl (v : Nat) : LevelTwo.Elt := LevelTwo.elPq.getD v LevelTwo.eltOne

@[expose] def uEl (v : Nat) : LevelTwo.Elt :=
  let k := LevelTwo.elQp.getD (LevelTwo.actV (hEl v).2 (hEl v).1 LevelTwo.p1) LevelTwo.eltOne
  (compA 1782 (hEl v).1 k.1, compA 1782 k.2 (hEl v).2)

@[expose] def conjInvA (g : LevelTwo.Elt) (a : Array Nat) : Array Nat :=
  compA 1782 g.2 (compA 1782 a g.1)

@[expose] def w0RArr : Array Nat := conjA rhoArr w0Arr

@[expose] def evenAt (m : Array Nat) (a : Nat) : Bool :=
  commA (compA 1782 m (powA 1782 (invCand 1782 rhoArr) a)) w0Arr &&
    commA (compA 1782 m (powA 1782 (invCand 1782 rhoArr) a)) w0RArr

@[expose] def plusB (m : Array Nat) : Bool :=
  commA m t1A && normV w0Arr w0RArr m && (evenAt m 0 || evenAt m 1 || evenAt m 2)

@[expose] def squareOK (v : Nat) (m : Array Nat) : Bool :=
  LevelTwo.pElemOK (hEl v) 2835 v && LevelTwo.elemOK (uEl v).1 (uEl v).2 &&
    LevelTwo.sendsB (uEl v).1 (uEl v).2 0 LevelTwo.p1 &&
    LevelTwo.sendsB (uEl v).1 (uEl v).2 2835 v &&
    plusB (conjInvA (hEl v) m) && plusB (conjInvA (uEl v) m)

@[expose] def transOK : Bool := squareOK 2970 xTwArr && squareOK 2890 yTwArr

@[expose] def sheetAt (u : Nat) : Nat :=
  ((List.range 3).find? fun i =>
    ElimCert.adjB LevelTwoCover.nbrC (LevelTwo.p1 + 2997 * i) u).getD 3

@[expose] def sheetOK (v : Nat) : Bool :=
  LevelTwoCover.listedAt0 v && decide (sheetAt (LevelTwoCover.liftAt0 v) < 3) &&
    ElimCert.adjB LevelTwoCover.nbrC (LevelTwo.p1 + 2997 * sheetAt (LevelTwoCover.liftAt0 v))
      (LevelTwoCover.liftAt0 v)

@[expose] def holOK : Bool :=
  sheetOK 2970 && sheetOK 2890 &&
    sheetAt (LevelTwoCover.liftAt0 2970) != sheetAt (LevelTwoCover.liftAt0 2890)

end CFSG.Sporadic.SuzRecog.RootTwistCheck
