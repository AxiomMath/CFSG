module

public import CFSG.Quasithin.H13.U3SixNormInputs

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.U3 Matrix

namespace CertificateChecks.Batch17004

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.U3 Matrix

private theorem tc_closed_0 : id6 ∈ tc ∧ ∀ e ∈ tc, ∀ c ∈ [u6c 0, u6c 1, u6c 2], mul6 e c ∈ tc := by
  decide +kernel

private theorem dc_mul_self_1 : mul6 dc dc = id6 := by
  decide +kernel

private theorem dc_conj_2 : ∀ i : Fin 5, mul6 (mul6 dc (u6c i)) dc = wordMat (dWords i) := by
  decide +kernel

private theorem dc_not_mem_tc_3 : dc ∉ tc := by
  decide +kernel

private theorem fixed_abs_only_4 : ∀ c < 64, vapp (u6c 0) c = c → vapp (u6c 1) c = c → vapp (u6c 2) c = c →
    c = 0 ∨ c = 15 := by
  decide +kernel

end CertificateChecks.Batch17004

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.U3 Matrix in
theorem certificate17004 : (
 id6 ∈ tc ∧ ∀ e ∈ tc, ∀ c ∈ [u6c 0, u6c 1, u6c 2], mul6 e c ∈ tc 
)
    ∧ (
 mul6 dc dc = id6 
)
    ∧ (
 ∀ i : Fin 5, mul6 (mul6 dc (u6c i)) dc = wordMat (dWords i) 
)
    ∧ (
 dc ∉ tc 
)
    ∧ (
 ∀ c < 64, vapp (u6c 0) c = c → vapp (u6c 1) c = c → vapp (u6c 2) c = c →
    c = 0 ∨ c = 15 
) := by
  exact ⟨@CertificateChecks.Batch17004.tc_closed_0, @CertificateChecks.Batch17004.dc_mul_self_1, @CertificateChecks.Batch17004.dc_conj_2, @CertificateChecks.Batch17004.dc_not_mem_tc_3, @CertificateChecks.Batch17004.fixed_abs_only_4⟩

end Certificates
