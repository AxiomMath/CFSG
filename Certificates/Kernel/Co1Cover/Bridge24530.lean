module

public import Certificates.Kernel.Co1Cover.Bridge
public import Certificates.Kernel.Co1Cover.E24530
public import CFSG.LocalAnalysis.EvenSporadicStandard.TwoCo1.ECoreInputs
import CFSG.Certificates.Kernel.Co1FixCount

public section

namespace CertificateChecks.KernelCo1Cover.ECore

open CFSG.KC.Co1F2 CFSG.EvenSporadicStandard.TwoCo1 CFSG.Sporadic.Co1.InvNative
  CertificateChecks.KernelCo1Cover

theorem eRowsA_eq : eRowsA = unpackR 24 EAP := by
  have hx : eMaskA = 3 := rfl
  rw [eRowsA, epsRows_eq, hx, eprod_sound lenE eA_ok]

theorem eRowsC_eq : eRowsC = unpackR 24 ECP := by
  have hx : eMaskC = 1 := rfl
  rw [eRowsC, epsRows_eq, hx, eprod_sound lenE eC_ok]

theorem facts24530 :
    (orderIs eRowsA 2 = true)
    ∧ (CFSG.Sporadic.Co1.Module.countsOK eRowsA 65536 30720 = true)
    ∧ (orderIs eRowsC 2 = true)
    ∧ (CFSG.Sporadic.Co1.Module.countsOK eRowsC 4096 2048 = true) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rw [eRowsA_eq]
    exact orderIs_sound eA_order
  · obtain ⟨h1, h2⟩ := CFSG.KC.Co1Fix.fixK_sound fixA_ok
    rw [CFSG.Sporadic.Co1.Module.countsOK, eRowsA_eq, tr_sound trA_ok, qRows_eq, tr_sound trQ_ok,
      h1, h2]
    rfl
  · rw [eRowsC_eq]
    exact orderIs_sound eC_order
  · obtain ⟨h1, h2⟩ := CFSG.KC.Co1Fix.fixK_sound fixC_ok
    rw [CFSG.Sporadic.Co1.Module.countsOK, eRowsC_eq, tr_sound trC_ok, qRows_eq, tr_sound trQ_ok,
      h1, h2]
    rfl

end CertificateChecks.KernelCo1Cover.ECore

end
