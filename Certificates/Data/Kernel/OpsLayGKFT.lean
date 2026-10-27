module

public import Certificates.Data.Kernel.OpsLayGKF
public import Certificates.Data.Kernel.OpsLayT

public section

namespace CFSG.KC.OpsLayGKF

open CFSG.SectionRank.Native CFSG.GH74.Generic.Fusion CFSG.GH74.KGroups.J3 CFSG.KC.LQT
  CFSG.KC.OpsLayK CFSG.KC.OpsV4

@[expose] noncomputable def gkfFusKT (c : Lay) (A B : Nat) (D : FusData) : Bool :=
  progOK D.nregs D.prog && [D.o0, D.o1, D.o2, D.o3].all (decide <| · < D.nregs) &&
    D.tests.all (decide <| · < c.d) &&
    (List.range 15).all (fun k => decide (D.n1s.getD k 0 < 65536) &&
      decide (D.n2s.getD k 0 < 65536)) &&
    runCT c D.prog (initRT c A B D.nregs) fun T => gkfG (opsL c) (powK c) D (getRD c.ONE T)

end CFSG.KC.OpsLayGKF

end
