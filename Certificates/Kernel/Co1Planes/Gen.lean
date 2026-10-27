module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.RankThree.PartOne.SPOR.Co1PlanesData
public import CFSG.Assembly.Defs

namespace CertificateChecks.KernelCo1Planes.Gen

open CFSG.KC.Eval CFSG.Sporadic.Co1Schreier.Native CFSG.RankThree.PartOne.SPOR

public meta def dagA : List Rows × List Rows × Bool := dag co1PlaneBase co1PlaneADerivs

public meta def dagC : List Rows × List Rows × Bool := dag co1PlaneBase co1PlaneCDerivs

public meta def dagB : List Rows × List Rows × Bool := dag co1PlaneBase co1PlaneBDerivs

meta def encL (l : Int) : Nat := if 0 < l then 2 * l.toNat else 2 * (-l).toNat + 1

meta def wordsV (ws : List (List Int)) : Val :=
  .list (ws.toArray.map fun w => .list (w.toArray.map fun l => .nat (encL l)))

public meta def planesStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "planesStep: expected no arguments"
  if !dagA.2.2 || !dagC.2.2 || !dagB.2.2 then throw "planesStep: inverse checks"
  return #[(`KWA, wordsV co1PlaneADerivs), (`KWC, wordsV co1PlaneCDerivs),
    (`KWB, wordsV co1PlaneBDerivs)]

end CertificateChecks.KernelCo1Planes.Gen
