module

public import Certificates.Data.RouteP.Bridge
public import Certificates.Data.RouteP.Plane
public import Certificates.Data.CFSGNative.Perm.Chain

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

open CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose, irreducible] def coverStabText : String := include_str "CoverStab.txt"

@[expose, irreducible] def coverN0Text : String := include_str "CoverN0.txt"

@[expose, irreducible] def baseText : String := include_str "Base.txt"

@[expose] def lineNums (text pre : String) (skip : Nat) : Array Nat :=
  match (text.splitOn "\n").find? (·.startsWith pre) with
  | none => #[]
  | some l => (((l.splitOn " ").drop skip).filterMap String.toNat?).toArray

@[expose] def invArr (p : Array Nat) : Array Nat := Id.run do
  let mut r : Array Nat := Array.replicate p.size 0
  for i in [0:p.size] do
    r := r.set! p[i]! i
  return r

@[expose] def objLines (_ : Unit := ()) : Array (List Int) :=
  slpLines coverStabText ++ slpLines coverN0Text

@[expose] def objProg (_ : Unit := ()) : List Instr := compileSLP 2 (objLines ())

@[expose] def objRegs (_ : Unit := ()) : Array Table :=
  mTabs () ++ Array.replicate 57 (idT degree)

@[expose] def objRun (_ : Unit := ()) : Array Table × Bool :=
  runSLP degree (objProg ()) (objRegs ())

@[expose] def tauReg : Nat := 9

@[expose] def epsReg (j : Nat) : Nat := 31 + 2 * j

@[expose] def aReg : Nat := 53

@[expose] def bReg : Nat := 57

@[expose] def dataOK (_ : Unit := ()) : Bool :=
  (objLines ()).size == 56 &&
  lineNums coverStabText "OUT H0 " 2 == #[7, 8, 9, 10] &&
  lineNums coverN0Text "OUT EPS " 2 == #[32, 34, 36, 38, 40, 42, 44, 46, 48, 50, 52] &&
  lineNums coverN0Text "OUT M24AB " 2 == #[54, 58] &&
  lineNums coverN0Text "EPSORBIT " 1 == #[4, 7, 2048] &&
  planeArr == (lineNums ((baseText.splitOn "\n[cover]")[1]!) "plane " 2).map (· - 1) &&
  planeAArr == invArr ((lineNums coverN0Text "PLANEPERM a " 2).map (· - 1)) &&
  planeBArr == invArr ((lineNums coverN0Text "PLANEPERM b " 2).map (· - 1))

@[expose] def tauOK (tabs : Array Table) : Bool :=
  ap tabs[tauReg]! 0 == 1479 && ap tabs[tauReg]! 1479 == 0

@[expose] def epsInvOK (tabs : Array Table) : Bool :=
  allIn 0 11 fun j => invoOK degree tabs[epsReg j]!

@[expose] def commOK (P Q : Table) : Bool :=
  allIn 0 degree fun x => ap P (ap Q x) == ap Q (ap P x)

@[expose] def epsCommOK (tabs : Array Table) : Bool :=
  allIn 0 11 fun i => allIn 0 i fun j => commOK tabs[epsReg i]! tabs[epsReg j]!

@[expose] def epsPlaneOK (tabs : Array Table) : Bool :=
  allIn 0 11 fun j => allIn 0 24 fun i => ap tabs[epsReg j]! planeArr[i]! == planeArr[i]!

@[expose] def abPlaneOK (tabs : Array Table) : Bool :=
  allIn 0 24 fun i => ap tabs[aReg]! planeArr[i]! == planeArr[planeAArr[i]!]! &&
    ap tabs[bReg]! planeArr[i]! == planeArr[planeBArr[i]!]!

structure PairTree where
  xs : Array Nat
  ys : Array Nat
  par : Array Nat
  lab : Array Nat

@[expose] def epsTreeData (tabs : Array Table) (p q : Nat) : PairTree := Id.run do
  let mut xs : Array Nat := #[p]
  let mut ys : Array Nat := #[q]
  let mut par : Array Nat := #[0]
  let mut lab : Array Nat := #[0]
  for k in [1:2048] do
    let j := ((List.range 11).find? fun j => (k >>> j) &&& 1 == 1).getD 0
    let h := k - (1 <<< j)
    let T := tabs[epsReg j]!
    xs := xs.push (ap T xs[h]!)
    ys := ys.push (ap T ys[h]!)
    par := par.push h
    lab := lab.push j
  return ⟨xs, ys, par, lab⟩

@[expose] def pairTreeOK (tabs : Array Table) (T : PairTree) (p q m : Nat) : Bool :=
  T.xs.size == m && T.ys.size == m && T.par.size == m && T.lab.size == m && 0 < m &&
    T.xs[0]! == p && T.ys[0]! == q &&
    allIn 0 m (fun k => decide (T.xs[k]! < degree) && decide (T.ys[k]! < degree)) &&
    allIn 1 m (fun k => decide (T.par[k]! < k) && decide (T.lab[k]! < 11) &&
      T.xs[k]! == ap tabs[epsReg T.lab[k]!]! T.xs[T.par[k]!]! &&
      T.ys[k]! == ap tabs[epsReg T.lab[k]!]! T.ys[T.par[k]!]!) &&
    allIn 0 m (fun i => allIn 0 i (fun j => T.xs[i]! != T.xs[j]! || T.ys[i]! != T.ys[j]!))

@[expose] def epsTreeOK (tabs : Array Table) : Bool :=
  pairTreeOK tabs (epsTreeData tabs 3 6) 3 6 2048

@[expose] def zpLetters : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 9, 10]

@[expose] def zpTreeOK (gs : Array Table) : Bool :=
  let T := CFSG.Perm.Native.treeBFS degree 1479 gs zpLetters
  T.pts.size == 31671 && CFSG.Perm.Native.treeOK degree 1479 T gs zpLetters

@[expose] def objOKAt (run : Array Table × Bool) (gs : Array Table) : Bool :=
  run.2 && run.1.size == 59 && progOK 59 (objProg ()) && dataOK () && tauOK run.1 &&
    epsInvOK run.1 && epsCommOK run.1 && epsPlaneOK run.1 && abPlaneOK run.1 &&
    epsTreeOK run.1 && gs.size == 22 && zpTreeOK gs && tripleCheck ()

@[expose] def objOK (_ : Unit := ()) : Bool := objOKAt (objRun ()) (genTabs ())

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
