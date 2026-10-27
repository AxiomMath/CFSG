module

public import Certificates.Kernel.AutJ2Vtx.Chains
public import Certificates.Kernel.AutJ2Vtx.Tbl
import CFSG.Certificates.Kernel.Common.Harness

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelAJC

open CFSG.KC.Enum CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.KS.SporSch.MOC CertificateChecks.KernelAJV

@[expose] noncomputable def cjK (c q : Nat) : Nat :=
  pcomp 315 9 (mask 9) (pcomp 315 9 (mask 9) (AJT c) (AJT q)) (AJI c)

theorem kNmW : (List.range 4).all (fun a => (List.range 4).all fun b =>
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) AJQ2.LR AJQ2.TRI AJQ2.BP 1 0
      (cjK ([0, 1, 2, 6].getD a 0) ([8, 9, 10, 11].getD b 0))) = true := by quickRfl

theorem kNmX1 : (List.range 4).all (fun a => (List.range 4).all fun b =>
    siftK 315 9 (mask 9) (315 * 9) (pidn 315 9) AJQ1.LR AJQ1.TRI AJQ1.BP 2 0
      (cjK ([0, 1, 2, 7].getD a 0) ([14, 15, 16, 17].getD b 0))) = true := by quickRfl

end CertificateChecks.KernelAJC

end
