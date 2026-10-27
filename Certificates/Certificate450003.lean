module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Co3Std.CentT.O8OuterCheck
public import Certificates.Kernel.OmegaEight.Bridge3009
public import Certificates.Kernel.OmegaEight.Outer450003K
public import Certificates.Certificate3119

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelO8

open CFSG.KC.Enum CFSG.KC.O8 CFSG.KS CFSG.KS.Raw CFSG.KS.Prim CFSG.EvenSmallLie.OmegaEight
  CFSG.Monster.B.Co2.Native CFSG.EvenSporadicStandard.Co3Std.CentT

theorem outer_arr {i : Nat} (hi : i ∈ [3, 4]) {a : Nat} (ha : a < 5) :
    o8OuterCentArr i a = unpack 360 9 (outerK i a) ∧ cn (outerK i a) = true := by
  have h := List.all_eq_true.1 kOuter i hi
  simp only [bAnd_iff] at h
  rcases a with _ | k
  · exact ⟨idA_eq, cn_pid⟩
  · have hk := allN_spec h.1 k (by omega)
    simp only [bAnd_iff] at hk
    have e1 : o8OuterCentArr i (k + 1) = omegaW ((cent0Words.getD i []).getD k []) := rfl
    have e2 : outerK i (k + 1) = wO ((cent0Words.getD i []).getD k []) := rfl
    rw [e1, e2]
    exact ⟨omegaW_eq hk.1, e2 ▸ hk.2⟩

theorem o8OuterCent_k : o8OuterCentCheck () = true := by
  unfold o8OuterCentCheck
  rw [List.all_eq_true]
  intro i hi
  have h := List.all_eq_true.1 kOuter i hi
  simp only [bAnd_iff] at h
  simp only [List.all_eq_true, List.mem_range]
  intro a ha b hb
  obtain ⟨ea, ca⟩ := outer_arr hi ha
  obtain ⟨eb, cb⟩ := outer_arr hi (by omega : b < 5)
  rw [ea, eb, eqA_pc ca cb]
  exact not_beq_of (allN_spec (allN_spec h.2 a ha) b hb)

end CertificateChecks.KernelO8

namespace Certificates

open CertificateChecks

open CFSG.EvenSporadicStandard.Co3Std.CentT in
theorem certificate450003 : o8OuterCentCheck () = true :=
  KernelO8.o8OuterCent_k

end Certificates
