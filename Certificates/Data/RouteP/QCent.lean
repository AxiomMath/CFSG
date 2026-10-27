module

public import Certificates.Data.RouteP.Geom
public import Certificates.Data.RouteP.Q0Planes

public section

namespace CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native

open CFSG.Sporadic.Th.Native
open CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Geom.Native

set_option compiler.extract_closed false

@[expose] def qcentCount (p : Nat → Bool) : Nat → Nat → Nat
  | 0, acc => acc
  | n + 1, acc => qcentCount p n (if p n then acc + 1 else acc)

@[expose] def qcentEps : Nat := 8

@[expose] def qcentRoot : Nat := 749820

@[expose] def qcentGens (tabs : Array Table) : Array Table :=
  let gs := planeLetters tabs
  let gsInv := gs.map (invT degree)
  let dws := planeDWords ()
  let u := planeUWord ()
  let v := planeVWord ()
  (Array.range planeGenCount).map fun s => planeGenTab gs gsInv (planeGenWord dws u v s)

@[expose] def qcentCheck (tau t13 : Table) (G0 : CFSG.Perm.Native.Tree) (G : Array Table)
    (T : CFSG.Perm.Native.Tree) : Bool :=
  let n0 := G0.pts.size
  qcentCount (fun k => ap t13 (ap G0.pts k) == ap G0.pts k) n0 0 == 3511 &&
  qcentCount (fun k => ap t13 (ap tau (ap G0.pts k)) == ap tau (ap G0.pts k)) n0 0 == 695 &&
  G.size == planeGenCount && T.pts.size == 693 &&
  CFSG.Perm.Native.treeOK degree qcentRoot T G (Array.range planeGenCount) && !memTree T 99705 &&
  allIn 0 n0 fun k =>
    let a := ap tau (ap G0.pts k)
    !(memTree G0 a && ap t13 a == a) || a == 99705 || memTree T a

@[expose] def qcentOKAt (objs gs : Array Table) : Bool :=
  let G := qcentGens objs
  qcentCheck objs[tauReg]! objs[epsReg qcentEps]! (geomTrees gs)[1]! G
    (CFSG.Perm.Native.treeBFS degree qcentRoot G (Array.range planeGenCount))

@[expose] def qcentOK (_ : Unit := ()) : Bool := qcentOKAt (objRun ()).1 (genTabs ())

end CFSG.EvenSporadicStandard.TwoFi22.DS81.RouteP.Model.Native
