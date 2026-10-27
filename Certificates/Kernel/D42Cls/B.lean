module

public import Certificates.Data.Kernel.D42Cls
public import Certificates.Kernel.D4Plane.Checks
import CFSG.Certificates.Kernel.Common.JsonGz
import CFSG.Certificates.Kernel.Common.Repo
import CFSG.Certificates.Kernel.Common.EachTrue

public section

#kc_repo #kc_json_gz CFSG.KD.D42B "Certificates/Kernel/D42Cls/data/b.json.gz" 240468
  3373446758161264876 (N : Nat) (n : Nat) (T : List Nat) (TW : List Nat) (DP : Nat) (Vm : Nat)
  (sW : List (List Nat)) (kW : List Nat) (rows : List (List (Nat × Nat × Nat × List Nat)))
  (CR : List (List (Nat × Nat × Nat))) (W1 : List (Nat × Nat × Nat)) (W2 : List (Nat × Nat × Nat))
  (roots : List (List Nat × List Nat × Nat × List Nat × List Nat))

namespace CFSG.KD.D42B

open CFSG.KC.D42Cls CFSG.KC.D4PlaneP CFSG.KD.D4Plane

theorem shapeOK : (N == 648 && T.length == 11 && TW.length == 11 && rows.length == 11 &&
    CR.length == 8 && roots.length == 600) = true := by decide +kernel

#kc_each CFSG.KD.D42B dc3brw
  (fun j => rowsOK N T TW DP Vm (sW.map (wordP ls)) rows j) 0 11

#kc_each CFSG.KD.D42B dc3bcr (fun i => crOK T CR i) 0 8

theorem w1OK : wOK TW W1 0 = true := by decide +kernel

theorem w2OK : wOK TW W2 1 = true := by decide +kernel

#kc_each CFSG.KD.D42B dc3brt
  (fun j => rootsOK ls (wordP ls kW) Vm N (wordP ls [14, 16, 17]) (wordP ls [15, 12, 15, 5])
    (sW.map (wordP ls)) (sW.map fun w => wordP ls w.reverse) CR W1 W2 roots j) 0 38

theorem classOK' : classOK (wordP ls kW) n N (sW.map (wordP ls))
    (sW.map fun w => wordP ls w.reverse) roots = true := by decide +kernel

theorem rowsNeg : rowsOK N (T.set 0 (T.getD 0 0 ^^^ 2)) TW DP Vm (sW.map (wordP ls)) rows 0 =
    false := by decide +kernel

theorem crNeg : crOK (T.set 3 (T.getD 3 0 ^^^ 8)) CR 0 = false := by decide +kernel

theorem keyNeg : rootsOK ls (wordP ls kW) Vm N (wordP ls [14, 16, 17]) (wordP ls [15, 12, 15, 5])
    (sW.map (wordP ls)) (sW.map fun w => wordP ls w.reverse) CR W1 W2
    ((roots.take 1).map fun rt => (rt.1, rt.2.1, rt.2.2.1 + 1, rt.2.2.2)) 0 = false := by
  decide +kernel

theorem stabNeg : rootsOK ls (wordP ls kW) Vm N (wordP ls [14, 16, 17]) (wordP ls [15, 12, 15, 5])
    (sW.map (wordP ls)) (sW.map fun w => wordP ls w.reverse) CR W1 W2
    ((roots.take 1).map fun rt => (rt.1, rt.2.1.drop 1, rt.2.2)) 0 = false := by
  decide +kernel

theorem genNeg : rootsOK ls (wordP ls kW) Vm N (wordP ls [14, 16, 17]) (wordP ls [15, 12, 15, 5])
    (sW.map (wordP ls)) (sW.map fun w => wordP ls w.reverse) CR W1 W2
    (((roots.filter fun rt => !rt.2.2.2.1.isEmpty).take 1).map fun rt =>
      (rt.1, rt.2.1, rt.2.2.1, rt.2.2.2.1.drop 1, rt.2.2.2.2)) 0 = false := by
  decide +kernel

theorem classNeg : classOK (wordP ls kW) (n + 1) N (sW.map (wordP ls))
    (sW.map fun w => wordP ls w.reverse) roots = false := by
  decide +kernel

end CFSG.KD.D42B

end
