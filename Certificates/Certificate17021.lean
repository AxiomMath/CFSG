module

public import CFSG.Quasithin.H13.U3SixProfileInputs
public import CFSG.Quasithin.H13.U3SixNormInputs

public section

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.U3 CFSG.Quasithin.SteinbergCB Matrix Module

namespace CertificateChecks.Batch17021

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.U3 CFSG.Quasithin.SteinbergCB Matrix Module

private theorem s0c_spec_0 :  s0c.length = 64 ∧ s0m 0 = id6 ∧ (∀ k < 64, canon6 (s0m k) = true) ∧
    s0c.Nodup  := by
  decide +kernel

private theorem s0tab_spec_1 :  ∀ i < 64, ∀ j < 64, tab i j < 64 ∧ mul6 (s0m i) (s0m j) = s0m (tab i j)  := by
  decide +kernel

private theorem s0c_closed_2 :  ∀ e ∈ s0c, ∀ c ∈ [u6c 0, u6c 1, u6c 2, dc], mul6 e c ∈ s0c  := by
  decide +kernel

private theorem tab_zero_3 :  ∀ i < 64, tab i 0 = i  := by
  decide +kernel

private theorem eaMasks_spec_4 :  1 ∈ eaMasks ∧ ∀ m ∈ eaMasks, m.testBit 0 = true  := by
  decide +kernel

private theorem eaMasks_ext_5 :  ∀ m ∈ eaMasks, ∀ i < 64, m.testBit i = false → tab i i = 0 →
    (∀ j < 64, m.testBit j = true → tab i j = tab j i) → extMask m i ∈ eaMasks  := by
  decide +kernel

private theorem ofMask_one_6 :  ofMask 1 = {0}  := by
  decide +kernel

private theorem eaMasks_class_7 :  ∀ m ∈ eaMasks, m = 1 ∨ (eaGood.any fun x => x.1 == m) ∨
    (eaFail.any fun x => x.1 == m)  := by
  decide +kernel

private theorem eaFail_ok_8 :  ∀ x ∈ eaFail, failOK x = true  := by
  decide +kernel

private theorem eaGood_ok_9 :  ∀ x ∈ eaGood, goodOK x = true  := by
  decide +kernel

private theorem invol_rank_10 :  ∀ k < 64, k ≠ 0 → tab k k = 0 → 4 ≤ rangeCard k  := by
  decide +kernel

end CertificateChecks.Batch17021

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.U3 CFSG.Quasithin.SteinbergCB Matrix Module in
theorem certificate17021 : (
 s0c.length = 64 ∧ s0m 0 = id6 ∧ (∀ k < 64, canon6 (s0m k) = true) ∧
    s0c.Nodup 
)
    ∧ (
 ∀ i < 64, ∀ j < 64, tab i j < 64 ∧ mul6 (s0m i) (s0m j) = s0m (tab i j) 
)
    ∧ (
 ∀ e ∈ s0c, ∀ c ∈ [u6c 0, u6c 1, u6c 2, dc], mul6 e c ∈ s0c 
)
    ∧ (
 ∀ i < 64, tab i 0 = i 
)
    ∧ (
 1 ∈ eaMasks ∧ ∀ m ∈ eaMasks, m.testBit 0 = true 
)
    ∧ (
 ∀ m ∈ eaMasks, ∀ i < 64, m.testBit i = false → tab i i = 0 →
    (∀ j < 64, m.testBit j = true → tab i j = tab j i) → extMask m i ∈ eaMasks 
)
    ∧ (
 ofMask 1 = {0} 
)
    ∧ (
 ∀ m ∈ eaMasks, m = 1 ∨ (eaGood.any fun x => x.1 == m) ∨
    (eaFail.any fun x => x.1 == m) 
)
    ∧ (
 ∀ x ∈ eaFail, failOK x = true 
)
    ∧ (
 ∀ x ∈ eaGood, goodOK x = true 
)
    ∧ (
 ∀ k < 64, k ≠ 0 → tab k k = 0 → 4 ≤ rangeCard k 
) := by
  exact ⟨@CertificateChecks.Batch17021.s0c_spec_0, @CertificateChecks.Batch17021.s0tab_spec_1, @CertificateChecks.Batch17021.s0c_closed_2, @CertificateChecks.Batch17021.tab_zero_3, @CertificateChecks.Batch17021.eaMasks_spec_4, @CertificateChecks.Batch17021.eaMasks_ext_5, @CertificateChecks.Batch17021.ofMask_one_6, @CertificateChecks.Batch17021.eaMasks_class_7, @CertificateChecks.Batch17021.eaFail_ok_8, @CertificateChecks.Batch17021.eaGood_ok_9, @CertificateChecks.Batch17021.invol_rank_10⟩

end Certificates
