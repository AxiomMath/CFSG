
module

public import CFSG.Monster.B.TwoA.Co2Inv.KerDataInputs
public import CFSG.Monster.B.TwoA.Census.PermBFS
public import CFSG.Monster.B.TwoA.Co2Inv.RowsInputs
public import Certificates.Certificate3026

@[expose] public section

open CFSG CFSG.Monster CFSG.Monster.B CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Co2Inv
  CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert CFSG.Monster.B.TwoA.Census

namespace CertificateChecks.Batch16000

private theorem affineFns_spec_0 : ∀ e < 2, ∀ l < 16, affineFns[affIdx e l]! = #[e, l] := by
  decide +kernel

private theorem translationLabels_spec_1 : ∀ j < 16,
    translationLabels[j]! < 16 ∧ transArr translationLabels[j]! = octPerms[j]! := by
  decide +kernel

private theorem octPerms_size_2 : octPerms.size = 16 := by
  decide +kernel

private theorem affMask_zero_3 : affMask 0 0 = 0 := by
  decide +kernel

private theorem affMask_one_zero_4 : affMask 1 0 = 16776960 := by
  decide +kernel

private theorem affMask_J_5 : ∀ e < 2, ∀ l < 16, ∀ x < 8, (affMask e l).testBit x = false := by
  decide +kernel

private theorem affMask_affine_6 : ∀ e < 2, ∀ l < 16, ∀ x < 24, 8 ≤ x →
    (affMask e l).testBit x = decide ((e + popc 4 (l &&& affineLabel[x]!)) % 2 = 1) := by
  decide +kernel

private theorem affMask_xor_7 : ∀ e < 2, ∀ l < 16, ∀ e' < 2, ∀ l' < 16,
    affMask e l ^^^ affMask e' l' = affMask (e ^^^ e') (l ^^^ l') := by
  decide +kernel

private theorem affMask_beq_8 : ∀ e < 2, ∀ l < 16, ∀ e' < 2, ∀ l' < 16,
    (affMask e l == affMask e' l') = (e == e' && l == l') := by
  decide +kernel

private theorem shortCode_mem_C_9 : ∀ i < 32, bvec 24 shortCode[i]! ∈ C := by
  decide +kernel

private theorem affMask_lt_10 : ∀ e < 2, ∀ l < 16, affMask e l < 2 ^ 24 := by
  decide +kernel

private theorem bvec_affMask_one_zero_11 : bvec 24 (affMask 1 0) = Code.Ω + bvec 24 255 := by
  decide +kernel

private theorem affIdx_lt_12 : ∀ e < 2, ∀ l < 16, affIdx e l < 32 := by
  decide +kernel

private theorem octPerms_perm_13 : ∀ j < 16, PermArr octPerms[j]! = true ∧ AutArr octPerms[j]! := by
  decide +kernel

private theorem transArr_fixJ_14 : ∀ t < 16, ∀ x < 8, (transArr t)[x]! = x := by
  decide +kernel

private theorem transArr_translate_15 : ∀ t < 16, ∀ x < 24, 8 ≤ x →
    8 ≤ (transArr t)[x]! ∧ affineLabel[(transArr t)[x]!]! = affineLabel[x]! ^^^ t := by
  decide +kernel

private theorem transArr_mul_16 : ∀ t < 16, ∀ t' < 16,
    amul (transArr t') (transArr t) = transArr (t ^^^ t') := by
  decide +kernel

private theorem transArr_zero_17 : transArr 0 = idArr := by
  decide +kernel

private theorem transArr_inj_18 : ∀ t < 16, ∀ t' < 16, transArr t = transArr t' → t = t' := by
  decide +kernel

private theorem transArr_sign_19 : ∀ t < 16, ∀ e < 2, ∀ l < 16, ∀ x < 24,
    (affMask e l).testBit (transArr t)[x]! = (affMask (e ^^^ par4 (l &&& t)) l).testBit x := by
  decide +kernel

private theorem par4_zero_left_20 : ∀ t < 16, par4 (0 &&& t) = 0 := by
  decide +kernel

private theorem par4_zero_right_21 : ∀ l < 16, par4 (l &&& 0) = 0 := by
  decide +kernel

private theorem par4_sep_right_22 : ∀ t < 16, (∀ l < 16, par4 (l &&& t) = 0) → t = 0 := by
  decide +kernel

private theorem par4_sep_left_23 : ∀ l < 16, (∀ t < 16, par4 (l &&& t) = 0) → l = 0 := by
  decide +kernel

private theorem signRows_ok_24 : ∀ i < 32,
    signRowsOK shortCode[i]! signRows[i]! = true ∧ fixZRows signRows[i]! = true := by
  decide +kernel

private theorem transRows_ok_25 : ∀ j < 16,
    permRowsOK octPerms[j]! transRows[j]! = true ∧ fixZRows transRows[j]! = true := by
  decide +kernel

end CertificateChecks.Batch16000

namespace Certificates

end Certificates
