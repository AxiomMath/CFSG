module

public import Certificates.Kernel.Co2Smith.CosetElemK
public import Certificates.Kernel.Co2Smith.ArcData
public import Certificates.Kernel.Co2Smith.LabK
public import Certificates.Data.Kernel.Co2Smith.Pts
public import Certificates.Data.Kernel.Co1F2

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCo2Smith

open CFSG.KC.Co2InvS CFSG.KC.Co2Smith CFSG.Sporadic.Co2Smith.Native CFSG.KC.Co2R3

@[expose] noncomputable def letK : Bool :=
  glCzLet.all (fun k => commK (LP k) zK) &&
    glC0Let.all (fun k => commK (LP k) alK && commK (LP k) gaK) && commK uK zK

@[expose] noncomputable def ordK : Bool :=
  eqK (powK alK 3) IDP && eqK (mulV gaK gaK) IDP && eqK (cjK gaK alK) (mulV alK alK) &&
    mapsK alK 0 1753 && mapsK gaK 0 2294

@[expose] noncomputable def ptK : Bool :=
  (List.range 11).all (fun k => mapsK (LP k) 80 80) && eqK (mulV uK uK) IDP &&
    mapsK uK 80 1172 && mapsK vK 80 1348 && mapsK v1K 80 582 && eqK (mulV v1K v1K) IDP

@[expose] noncomputable def cValK : Bool :=
  Nat.beq (at12 cP 80) 0 && Nat.beq (at12 cP 1172) 3 && Nat.beq (at12 cP 582) 1

@[expose] noncomputable def arcK : Bool :=
  bindVK (KernelSporSch.Co2M.PV 0) (AP 0) (CFSG.KC.Co1F2.trK 22 alK) &&
    bindVK (KernelSporSch.Co2M.PV 0) (AP 1) (CFSG.KC.Co1F2.trK 22 gaK) &&
    bindVK (KernelSporSch.Co2M.PV 0) (AP 2) (CFSG.KC.Co1F2.trK 22 zK)

@[expose] noncomputable def elGenK : Bool :=
  glNWords.all (fun w => w.all (· < 22) && mapsK (wK LP w) 80 80 && mapsK (wK LP w) 1172 1172) &&
    glMWords.all fun w => w.all (· < 22) && mapsK (wK LP w) 80 80 && mapsK (wK LP w) 582 582

theorem let_k : letK = true := by decide +kernel

theorem ord_k : ordK = true := by decide +kernel

theorem pt_k : ptK = true := by decide +kernel

theorem cVal_k : cValK = true := by decide +kernel

theorem arc_k : arcK = true := by decide +kernel

theorem gen_k : elGenK = true := by decide +kernel

end CertificateChecks.KernelCo2Smith
