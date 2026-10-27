module

public import CFSG.Quasithin.Vol2.Ch5Sec2M23G0DataInputs

public section

set_option maxRecDepth 400000

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.ComponentClassification.WittDesign
open CFSG.Sporadic.Mathieu CFSG.Quasithin.Asc94

namespace CertificateChecks.Batch7056

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.ComponentClassification.WittDesign
open CFSG.Sporadic.Mathieu CFSG.Quasithin.Asc94

theorem m22Bt3_spec_0 :
    (m22Bt3 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (m22Bt3 : Equiv.Perm (Fin 22)) 1 = 1 ∧
      PresHex m22Bt3 ∧ m22Bt3 ^ 3 = 1 ∧ m22Bt3 ≠ 1 := by
  decide +kernel

theorem m22Inv1_spec_1 :
    (m22Inv1 : Equiv.Perm (Fin 22)) 0 = 0 ∧
      (m22Inv1 : Equiv.Perm (Fin 22)) 1 = 1 ∧ ¬ PresHex m22Inv1 ∧ m22Inv1 * m22Inv1 = 1 ∧
      m22Inv1 * m22Bt3 * m22Inv1 * m22Bt3 = 1 := by
  decide +kernel

theorem m22Fix19_inv_spec_2 :
    m22Fix19 * m22Fix19 = 1 ∧ m22Fix19 * m22Bt3 * m22Fix19 * m22Bt3 = 1 := by
  decide +kernel

end CertificateChecks.Batch7056

namespace Certificates

open CertificateChecks

open CFSG CFSG.Quasithin CFSG.Quasithin.H13 CFSG.ComponentClassification.WittDesign in
open CFSG.Sporadic.Mathieu CFSG.Quasithin.Asc94 in
theorem certificate7056 :
    ((m22Bt3 : Equiv.Perm (Fin 22)) 0 = 0 ∧ (m22Bt3 : Equiv.Perm (Fin 22)) 1 = 1 ∧
       PresHex m22Bt3 ∧ m22Bt3 ^ 3 = 1 ∧ m22Bt3 ≠ 1)
    ∧ ((m22Inv1 : Equiv.Perm (Fin 22)) 0 = 0 ∧
       (m22Inv1 : Equiv.Perm (Fin 22)) 1 = 1 ∧ ¬ PresHex m22Inv1 ∧ m22Inv1 * m22Inv1 = 1 ∧
       m22Inv1 * m22Bt3 * m22Inv1 * m22Bt3 = 1)
    ∧ (m22Fix19 * m22Fix19 = 1 ∧ m22Fix19 * m22Bt3 * m22Fix19 * m22Bt3 = 1) :=
  ⟨CertificateChecks.Batch7056.m22Bt3_spec_0, CertificateChecks.Batch7056.m22Inv1_spec_1, CertificateChecks.Batch7056.m22Fix19_inv_spec_2⟩

end Certificates
