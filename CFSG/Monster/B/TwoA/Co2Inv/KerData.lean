
module


public import Certificates.Certificate16000

public section

namespace CFSG.Monster.B.TwoA.Co2Inv

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.B.Co2 CFSG.Monster.VisCert
  CFSG.Monster.B.TwoA.Census

theorem affineFns_spec :
    ∀ e < 2, ∀ l < 16, affineFns[affIdx e l]! = #[e, l] :=
  Certificates.certificate16000.1

theorem translationLabels_spec : ∀ j < 16,
    translationLabels[j]! < 16 ∧ transArr translationLabels[j]! = octPerms[j]! :=
  Certificates.certificate16000.2.1

theorem translationLabels_lt
    (j : ℕ) (hj : j < 16) : translationLabels[j]! < 16 :=
  (translationLabels_spec j hj).1

theorem octPerms_size : octPerms.size = 16 :=
  Certificates.certificate16000.2.2.1

theorem affMask_zero : affMask 0 0 = 0 :=
  Certificates.certificate16000.2.2.2.1

theorem affMask_one_zero : affMask 1 0 = 16776960 :=
  Certificates.certificate16000.2.2.2.2.1

theorem affMask_J :
    ∀ e < 2, ∀ l < 16, ∀ x < 8, (affMask e l).testBit x = false :=
  Certificates.certificate16000.2.2.2.2.2.1

theorem affMask_affine : ∀ e < 2, ∀ l < 16, ∀ x < 24, 8 ≤ x →
    (affMask e l).testBit x = decide ((e + popc 4 (l &&& affineLabel[x]!)) % 2 = 1) :=
  Certificates.certificate16000.2.2.2.2.2.2.1

theorem affMask_xor : ∀ e < 2, ∀ l < 16, ∀ e' < 2, ∀ l' < 16,
    affMask e l ^^^ affMask e' l' = affMask (e ^^^ e') (l ^^^ l') :=
  Certificates.certificate16000.2.2.2.2.2.2.2.1

theorem affMask_beq : ∀ e < 2, ∀ l < 16, ∀ e' < 2, ∀ l' < 16,
    (affMask e l == affMask e' l') = (e == e' && l == l') :=
  Certificates.certificate16000.2.2.2.2.2.2.2.2.1

theorem affMask_inj
    {e l e' l' : ℕ} (he : e < 2) (hl : l < 16) (he' : e' < 2) (hl' : l' < 16)
    (h : affMask e l = affMask e' l') : e = e' ∧ l = l' := by
  have := affMask_beq e he l hl e' he' l' hl'
  rw [h, beq_self_eq_true, eq_comm, Bool.and_eq_true, beq_iff_eq, beq_iff_eq] at this
  exact this

theorem shortCode_mem_C : ∀ i < 32, bvec 24 shortCode[i]! ∈ C :=
  Certificates.certificate16000.2.2.2.2.2.2.2.2.2.1

theorem affMask_lt : ∀ e < 2, ∀ l < 16, affMask e l < 2 ^ 24 :=
  Certificates.certificate16000.2.2.2.2.2.2.2.2.2.2.1

theorem bvec_affMask_one_zero :
    bvec 24 (affMask 1 0) = Code.Ω + bvec 24 255 :=
  Certificates.certificate16000.2.2.2.2.2.2.2.2.2.2.2.1

theorem affIdx_lt : ∀ e < 2, ∀ l < 16, affIdx e l < 32 :=
  Certificates.certificate16000.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem octPerms_perm :
    ∀ j < 16, PermArr octPerms[j]! = true ∧ AutArr octPerms[j]! :=
  Certificates.certificate16000.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem transArr_fixJ : ∀ t < 16, ∀ x < 8, (transArr t)[x]! = x :=
  Certificates.certificate16000.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem transArr_translate : ∀ t < 16, ∀ x < 24, 8 ≤ x →
    8 ≤ (transArr t)[x]! ∧ affineLabel[(transArr t)[x]!]! = affineLabel[x]! ^^^ t :=
  Certificates.certificate16000.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem transArr_mul : ∀ t < 16, ∀ t' < 16,
    amul (transArr t') (transArr t) = transArr (t ^^^ t') :=
  Certificates.certificate16000.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem transArr_zero : transArr 0 = idArr :=
  Certificates.certificate16000.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem transArr_inj :
    ∀ t < 16, ∀ t' < 16, transArr t = transArr t' → t = t' :=
  Certificates.certificate16000.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem transArr_sign : ∀ t < 16, ∀ e < 2, ∀ l < 16, ∀ x < 24,
    (affMask e l).testBit (transArr t)[x]! = (affMask (e ^^^ par4 (l &&& t)) l).testBit x :=
  Certificates.certificate16000.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem par4_zero_left : ∀ t < 16, par4 (0 &&& t) = 0 :=
  Certificates.certificate16000.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem par4_zero_right : ∀ l < 16, par4 (l &&& 0) = 0 :=
  Certificates.certificate16000.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem par4_sep_right :
    ∀ t < 16, (∀ l < 16, par4 (l &&& t) = 0) → t = 0 :=
  Certificates.certificate16000.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem par4_sep_left :
    ∀ l < 16, (∀ t < 16, par4 (l &&& t) = 0) → l = 0 :=
  Certificates.certificate16000.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem signRows_ok : ∀ i < 32,
    signRowsOK shortCode[i]! signRows[i]! = true ∧ fixZRows signRows[i]! = true :=
  Certificates.certificate16000.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.1

theorem transRows_ok : ∀ j < 16,
    permRowsOK octPerms[j]! transRows[j]! = true ∧ fixZRows transRows[j]! = true :=
  Certificates.certificate16000.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2.2

end CFSG.Monster.B.TwoA.Co2Inv
