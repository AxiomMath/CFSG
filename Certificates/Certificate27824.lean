module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWDef
public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TS16RWIso
import CFSG.Certificates.Kernel.Fin76bOm.AutESound
import Certificates.Certificate24606
import Certificates.Kernel.Fin76bOm.AutEChk
import Certificates.Kernel.Fin76bOm.UGlue

public section

namespace Certificates

open CFSG.EvenSporadicStandard.Fin76b CFSG.EvenSporadicStandard.Fin76b.W16 CFSG.KC.Fin76bU
  CFSG.KS.EAut CertificateChecks.KernelC24608

private theorem rhoInvArr_eq_RH : ∀ k < 32, rhoInvArr[k]! = fldU 5 RH k := by
  decide +kernel

open CFSG.EvenSporadicStandard.Fin76b.W16 in
theorem certificate27824 : ∀ a < 32, ∀ b < 32, rhoInvArr[mulE0 a b]! = mulEJ3 rhoInvArr[a]! rhoInvArr[b]! := by
  refine fun a ha b hb => ?_
  obtain ⟨-, hmul, -⟩ := eAEIsoU_spec ch24608Iso
  have h2 := tblU_of j2U_tbl
  have h3 := tblU_of j3U_tbl
  have hab : mulE0 a b < 32 := h2 a ha b hb ▸ mU_lt J2U.P a b
  rw [rhoInvArr_eq_RH _ hab, rhoInvArr_eq_RH a ha, rhoInvArr_eq_RH b hb, ← h2 a ha b hb,
    hmul a ha b hb, h3 _ (fldU_lt 5 RH a) _ (fldU_lt 5 RH b)]

end Certificates
