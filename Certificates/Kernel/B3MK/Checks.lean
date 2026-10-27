module

public import Certificates.Kernel.B3MK.Data
public import Certificates.Kernel.WEMK.Data

set_option maxRecDepth 100000
set_option Elab.async false

public section

namespace CFSG.KD.B3MK

open Certificates.WEMK Certificates.B3MK

theorem n4_vw : ((CFSG.KD.WEMK.N4.V.map fun q => toW (mat 4 q)) == N4.VW &&
    Nat.beq N4.x0 CFSG.KD.WEMK.N4.x0) = true := by
  decide +kernel

theorem n4_gens : (N4.J == [27] && Nat.blt N4.u0 40 && Nat.beq (lenL N4.VW) 40 && [N4.r0, N4.r2, N4.r3, N4.u] ==
    [N4.VW.getD 0 0, N4.VW.getD N4.x0 0, N4.VW.getD 27 0, N4.VW.getD N4.u0 0]) = true := by
  decide +kernel

theorem n4_chains : chainsOK N4.r0 N4.r2 N4.J N4.VW = true := by
  decide +kernel

theorem n4_len : (Nat.beq (lenL N4.E) 384 && Nat.beq (lenL N4.par) 384 && Nat.blt N4.i0 384 &&
    Nat.beq (getE N4.Ep N4.i0) idW) = true := by
  decide +kernel

theorem n4_close : elemsOK N4.Ep N4.Tp 384 [N4.r0, N4.r2, N4.r3, N4.u] N4.E = true := by
  decide +kernel

theorem n4_tree : treeOK N4.Tp N4.Dp 384 N4.i0 N4.par = true := by
  decide +kernel

theorem n4_incr : incrL N4.E 0 = true := by
  decide +kernel

theorem n4_mw : mwOK N4.Ep 384 N4.r0 N4.r2 N4.r3 N4.u N4.VW N4.mw = true := by
  decide +kernel

theorem en4_vw : ((CFSG.KD.WEMK.EN4.V.map fun q => toW (mat 4 q)) == EN4.VW &&
    Nat.beq EN4.x0 CFSG.KD.WEMK.EN4.x0) = true := by
  decide +kernel

theorem en4_gens : (EN4.J == [36, 47, 55] && EN4.wab == [[19, 24], [10, 15], [4, 7]] &&
    Nat.beq (lenL EN4.VW) 60 && [EN4.r0, EN4.r2] == [EN4.VW.getD 0 0, EN4.VW.getD EN4.x0 0] &&
    EN4.r3s == EN4.J.map (EN4.VW.getD · 0) && EN4.sas == EN4.wab.map (fun w => EN4.VW.getD (w.getD 0 0) 0) &&
    EN4.sbs == EN4.wab.map (fun w => EN4.VW.getD (w.getD 1 0) 0)) = true := by
  decide +kernel

theorem en4_chains : chainsOK EN4.r0 EN4.r2 EN4.J EN4.VW = true := by
  decide +kernel

theorem en4_c0 : ck51 EN4.r0 EN4.r2 (EN4.r3s.getD 0 0) (EN4.Hs.getD 0 []) (EN4.Hps.getD 0 0) (EN4.Tps.getD 0 0)
    (EN4.i0s.getD 0 0) (EN4.sas.getD 0 0) (EN4.sbs.getD 0 0) = true := by
  decide +kernel

theorem en4_c1 : ck51 EN4.r0 EN4.r2 (EN4.r3s.getD 1 0) (EN4.Hs.getD 1 []) (EN4.Hps.getD 1 0) (EN4.Tps.getD 1 0)
    (EN4.i0s.getD 1 0) (EN4.sas.getD 1 0) (EN4.sbs.getD 1 0) = true := by
  decide +kernel

theorem en4_c2 : ck51 EN4.r0 EN4.r2 (EN4.r3s.getD 2 0) (EN4.Hs.getD 2 []) (EN4.Hps.getD 2 0) (EN4.Tps.getD 2 0)
    (EN4.i0s.getD 2 0) (EN4.sas.getD 2 0) (EN4.sbs.getD 2 0) = true := by
  decide +kernel

end CFSG.KD.B3MK

end
