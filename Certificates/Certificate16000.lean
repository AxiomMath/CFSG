
module

public import Certificates.Certificate16000Base
import all Certificates.Certificate16000Base


public section

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv
  CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.TwoA.Census

namespace CertificateChecks.Batch16000

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv
  CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.TwoA.Census

end CertificateChecks.Batch16000

namespace Certificates

open CertificateChecks

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv
  CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.TwoA.Census in
theorem certificate16000 : (
    ∀ e < 2, ∀ l < 16, affineFns[affIdx e l]! = #[e, l]
  ) ∧ (
    ∀ j < 16,
      translationLabels[j]! < 16 ∧ transArr translationLabels[j]! = octPerms[j]!
  ) ∧ (
    octPerms.size = 16
  ) ∧ (
    affMask 0 0 = 0
  ) ∧ (
    affMask 1 0 = 16776960
  ) ∧ (
    ∀ e < 2, ∀ l < 16, ∀ x < 8, (affMask e l).testBit x = false
  ) ∧ (
    ∀ e < 2, ∀ l < 16, ∀ x < 24, 8 ≤ x →
      (affMask e l).testBit x = decide ((e + popc 4 (l &&& affineLabel[x]!)) % 2 = 1)
  ) ∧ (
    ∀ e < 2, ∀ l < 16, ∀ e' < 2, ∀ l' < 16,
      affMask e l ^^^ affMask e' l' = affMask (e ^^^ e') (l ^^^ l')
  ) ∧ (
    ∀ e < 2, ∀ l < 16, ∀ e' < 2, ∀ l' < 16,
      (affMask e l == affMask e' l') = (e == e' && l == l')
  ) ∧ (
    ∀ i < 32, bvec 24 shortCode[i]! ∈ C
  ) ∧ (
    ∀ e < 2, ∀ l < 16, affMask e l < 2 ^ 24
  ) ∧ (
    bvec 24 (affMask 1 0) = Code.Ω + bvec 24 255
  ) ∧ (
    ∀ e < 2, ∀ l < 16, affIdx e l < 32
  ) ∧ (
    ∀ j < 16, PermArr octPerms[j]! = true ∧ AutArr octPerms[j]!
  ) ∧ (
    ∀ t < 16, ∀ x < 8, (transArr t)[x]! = x
  ) ∧ (
    ∀ t < 16, ∀ x < 24, 8 ≤ x →
      8 ≤ (transArr t)[x]! ∧ affineLabel[(transArr t)[x]!]! = affineLabel[x]! ^^^ t
  ) ∧ (
    ∀ t < 16, ∀ t' < 16,
      amul (transArr t') (transArr t) = transArr (t ^^^ t')
  ) ∧ (
    transArr 0 = idArr
  ) ∧ (
    ∀ t < 16, ∀ t' < 16, transArr t = transArr t' → t = t'
  ) ∧ (
    ∀ t < 16, ∀ e < 2, ∀ l < 16, ∀ x < 24,
      (affMask e l).testBit (transArr t)[x]! = (affMask (e ^^^ par4 (l &&& t)) l).testBit x
  ) ∧ (
    ∀ t < 16, par4 (0 &&& t) = 0
  ) ∧ (
    ∀ l < 16, par4 (l &&& 0) = 0
  ) ∧ (
    ∀ t < 16, (∀ l < 16, par4 (l &&& t) = 0) → t = 0
  ) ∧ (
    ∀ l < 16, (∀ t < 16, par4 (l &&& t) = 0) → l = 0
  ) ∧ (
    ∀ i < 32,
      signRowsOK shortCode[i]! signRows[i]! = true ∧ fixZRows signRows[i]! = true
  ) ∧ (
    ∀ j < 16,
      permRowsOK octPerms[j]! transRows[j]! = true ∧ fixZRows transRows[j]! = true
  ) := by
  exact ⟨CertificateChecks.Batch16000.affineFns_spec_0, CertificateChecks.Batch16000.translationLabels_spec_1,
    CertificateChecks.Batch16000.octPerms_size_2, CertificateChecks.Batch16000.affMask_zero_3, CertificateChecks.Batch16000.affMask_one_zero_4,
    CertificateChecks.Batch16000.affMask_J_5, CertificateChecks.Batch16000.affMask_affine_6, CertificateChecks.Batch16000.affMask_xor_7,
    CertificateChecks.Batch16000.affMask_beq_8, CertificateChecks.Batch16000.shortCode_mem_C_9, CertificateChecks.Batch16000.affMask_lt_10,
    CertificateChecks.Batch16000.bvec_affMask_one_zero_11, CertificateChecks.Batch16000.affIdx_lt_12, CertificateChecks.Batch16000.octPerms_perm_13,
    CertificateChecks.Batch16000.transArr_fixJ_14, CertificateChecks.Batch16000.transArr_translate_15, CertificateChecks.Batch16000.transArr_mul_16,
    CertificateChecks.Batch16000.transArr_zero_17, CertificateChecks.Batch16000.transArr_inj_18, CertificateChecks.Batch16000.transArr_sign_19,
    CertificateChecks.Batch16000.par4_zero_left_20, CertificateChecks.Batch16000.par4_zero_right_21, CertificateChecks.Batch16000.par4_sep_right_22,
    CertificateChecks.Batch16000.par4_sep_left_23, CertificateChecks.Batch16000.signRows_ok_24, CertificateChecks.Batch16000.transRows_ok_25⟩

end Certificates
