module

public meta import Lean
public meta import CFSG.Certificates.Kernel.Common.Eval
public meta import CFSG.LocalAnalysis.EvenSporadicStandard.Induction.Rows.Co1CentData
public import CFSG.Assembly.Defs

namespace CertificateChecks.KernelCo1B.Cent27207

open CFSG.KC.Eval CFSG.EvenSporadicStandard.Co1Cent CFSG.Sporadic.Co1Schreier.Native
  CFSG.EvenSporadicStandard.Induction.AutBound.Spin CFSG.EvenSporadicStandard.Co1Pair
  CFSG.Sporadic.SmallF2.Native

public meta def packA (X : Array Nat) : Nat :=
  (List.range 24).foldl (fun acc i => acc ||| ((X.getD i 0 % 2 ^ 24) <<< (24 * i))) 0

public meta def centStep (args : Array Val) : Except String (Array (Lean.Name × Val)) := do
  if args.size != 0 then throw "centStep: expected no arguments"
  let D := centData
  let A := D.A
  let pk := fun (X : Array Nat) => Val.nat (packA X)
  let pl := fun (L : List (Array Nat)) => Val.list (L.toArray.map pk)
  let enc := fun (j : Int) => if 0 ≤ j then 2 * j.toNat else 2 * (-j).toNat + 1
  return #[(`SW, .list (sWords.toArray.map fun w => .list (w.toArray.map fun j => .nat (enc j)))),
    (`X, pk cpX), (`XI, pk (inv cpX)), (`Y, pk cpY), (`YI, pk (inv cpY)),
    (`RS, pl sRows), (`RIS, pl sInv), (`AK, pl A), (`ATK, pl (A.map (transposeRows 24))),
    (`bK, .list (D.b.toArray.map .nat)), (`CP, pk D.C), (`LP, pk D.lam), (`WC, pk D.wcolsArr),
    (`PP, pk D.Pp), (`CX, pl ((List.range 64).map cx)), (`A1, pk aR)]

end CertificateChecks.KernelCo1B.Cent27207
