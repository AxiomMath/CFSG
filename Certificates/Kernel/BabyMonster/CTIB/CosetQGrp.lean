module

public import Certificates.Kernel.BabyMonster.CTIB.CosetQLin

public section

namespace CertificateChecks.KernelBM.CTIB.CosetQ

open CFSG.KC.BM CFSG.KC.BM.CosetQ CFSG.Monster.B.CTIB.Native CertificateChecks.KernelBM.CTIB

set_option exponentiation.threshold 1024

variable {G : Array ℕ}

theorem QC.ext' {a b : QC G} (h : a.1 = b.1) : a = b := Subtype.ext h

@[expose] def mkQ (n : ℕ) (h : n < 2 ^ 23) : QC G := ⟨n, h⟩

theorem mkQ_val {n : ℕ} (h : n < 2 ^ 23) : (mkQ (G := G) n h).1 = n := rfl

@[expose] def homOf (G A : Array ℕ) (hA : RelOK G A) : QC G →* QC G where
  toFun a := mkQ (autApply G A a.1) (autApply_lt _ _ _)
  map_one' := QC.ext' (by
    rw [mkQ_val, QC.one_val]
    exact autApply_zero G A)
  map_mul' a b := QC.ext' (by
    rw [mkQ_val, QC.mul_val, QC.mul_val, mkQ_val, mkQ_val]
    exact autApply_mul hA a.1 b.1)

theorem homOf_val {A : Array ℕ} (hA : RelOK G A) (a : QC G) :
    (homOf G A hA a).1 = autApply G A a.1 := rfl

@[expose] def piQ (a : QC G) : ℕ := a.1 % 2 ^ 22

theorem piQ_lt (a : QC G) : piQ a < 2 ^ 22 := Nat.mod_lt _ (Nat.two_pow_pos 22)

theorem piQ_bit (a : QC G) {i : ℕ} (hi : i < 22) : (piQ a).testBit i = a.1.testBit i := by
  rw [piQ, Nat.testBit_mod_two_pow, decide_eq_true hi, Bool.true_and]

theorem piQ_mul (a b : QC G) : piQ (a * b) = piQ a ^^^ piQ b := by
  apply Nat.eq_of_testBit_eq
  intro i
  simp only [piQ, QC.mul_val, Nat.testBit_mod_two_pow, Nat.testBit_xor]
  by_cases hi : i < 22
  · rw [decide_eq_true hi, qmul_bit G _ _ hi]
    simp
  · simp [hi]

theorem piQ_one : piQ (1 : QC G) = 0 := by
  rw [piQ, QC.one_val, Nat.zero_mod]

theorem xor_cancel_of {x y : ℕ} (h : x ^^^ y = 0) : x = y := by
  have : x = (x ^^^ y) ^^^ y := by rw [Nat.xor_assoc, Nat.xor_self, Nat.xor_zero]
  rw [this, h, Nat.zero_xor]

theorem piQ_inv (a : QC G) : piQ a⁻¹ = piQ a := by
  have h := piQ_mul a⁻¹ a
  rw [inv_mul_cancel, piQ_one] at h
  exact xor_cancel_of h.symm

theorem piQ_hom {A : Array ℕ} (hA : RelOK G A) (a : QC G) :
    piQ (homOf G A hA a) = mv G A (piQ a) := by
  rw [piQ, homOf_val, piQ, mv_mod]
  rfl

@[expose] def xQ : QC G := ⟨2 ^ 22, by decide⟩

theorem xQ_bit {i : ℕ} (hi : i < 22) : (xQ : QC G).1.testBit i = false :=
  Nat.testBit_two_pow_of_ne (by omega)

theorem corr_x_left (a : ℕ) : corr G (2 ^ 22) a = false := by
  rw [corr_congr G (a' := 0) (b' := a) (fun j hj => by
    rw [Nat.testBit_two_pow_of_ne (by omega), Nat.zero_testBit]) fun _ _ => rfl, corr_zero_left]

theorem corr_x_right (a : ℕ) : corr G a (2 ^ 22) = false := by
  rw [corr_congr G (a' := a) (b' := 0) (fun _ _ => rfl) fun j hj => by
    rw [Nat.testBit_two_pow_of_ne (by omega), Nat.zero_testBit], corr_zero_right]

theorem xQ_comm (a : QC G) : xQ * a = a * xQ := by
  refine QC.ext' ?_
  rw [QC.mul_val, QC.mul_val]
  refine code_ext (qmul_lt _ _ _) (qmul_lt _ _ _) (fun i hi => ?_) ?_
  · rw [qmul_bit G _ _ hi, qmul_bit G _ _ hi, Bool.xor_comm]
  · rw [qmul_bit22, qmul_bit22]
    change ((Nat.testBit (2 ^ 22) 22 ^^ _) ^^ corr G (2 ^ 22) a.1) =
      ((_ ^^ Nat.testBit (2 ^ 22) 22) ^^ corr G a.1 (2 ^ 22))
    rw [corr_x_left, corr_x_right, Bool.xor_comm (Nat.testBit (2 ^ 22) 22)]

theorem xQ_sq : (xQ : QC G) * xQ = 1 := by
  refine QC.ext' ?_
  rw [QC.mul_val, QC.one_val]
  refine code_ext (qmul_lt _ _ _) (by decide) (fun i hi => ?_) ?_
  · rw [qmul_bit G _ _ hi, Bool.xor_self, Nat.zero_testBit]
  · rw [qmul_bit22, Bool.xor_self, Bool.false_xor, Nat.zero_testBit]
    exact corr_x_left _

theorem xQ_inv : (xQ : QC G)⁻¹ = xQ := inv_eq_of_mul_eq_one_right xQ_sq

theorem piQ_x : piQ (xQ : QC G) = 0 := by
  rw [piQ]
  exact Nat.mod_self _

theorem hom_x {A : Array ℕ} (hA : RelOK G A) : homOf G A hA xQ = xQ :=
  QC.ext' (by rw [homOf_val]; exact autApply_x G A)

theorem eq_or_x {a b : QC G} (h : piQ a = piQ b) : a = b ∨ a = b * xQ := by
  have hb : ∀ i < 22, a.1.testBit i = b.1.testBit i := fun i hi => by
    rw [← piQ_bit a hi, ← piQ_bit b hi, h]
  by_cases h22 : a.1.testBit 22 = b.1.testBit 22
  · exact Or.inl (QC.ext' (code_ext a.2 b.2 hb h22))
  · refine Or.inr (QC.ext' ?_)
    rw [QC.mul_val]
    refine code_ext a.2 (qmul_lt _ _ _) (fun i hi => ?_) ?_
    · rw [qmul_bit G _ _ hi, hb i hi]
      change _ = (_ ^^ Nat.testBit (2 ^ 22) i)
      rw [Nat.testBit_two_pow_of_ne (by omega), Bool.xor_false]
    · rw [qmul_bit22]
      change _ = ((_ ^^ Nat.testBit (2 ^ 22) 22) ^^ corr G b.1 (2 ^ 22))
      rw [corr_x_right, Nat.testBit_two_pow_self, Bool.xor_false]
      cases ha : a.1.testBit 22 <;> cases hb' : b.1.testBit 22 <;> simp_all

@[expose] def ofV (v : ℕ) (hv : v < 2 ^ 22) : QC G := ⟨v, lt_trans hv (by decide)⟩

theorem piQ_ofV {v : ℕ} (hv : v < 2 ^ 22) : piQ (ofV (G := G) v hv) = v := Nat.mod_eq_of_lt hv

@[expose] def eK (m : ℕ) (hm : m < 22) : QC G :=
  ofV (2 ^ m) (Nat.pow_lt_pow_right (by decide) hm)

theorem eK_sq {m : ℕ} (hm : m < 22) : (eK (G := G) m hm) * eK m hm = 1 := by
  refine QC.ext' ?_
  rw [QC.mul_val, QC.one_val]
  refine code_ext (qmul_lt _ _ _) (by decide) (fun i hi => ?_) ?_
  · rw [qmul_bit G _ _ hi, Bool.xor_self, Nat.zero_testBit]
  · rw [qmul_bit22, Bool.xor_self, Bool.false_xor, Nat.zero_testBit]
    change corr G (2 ^ m) (2 ^ m) = false
    rw [corr_two_pow G hm hm]
    simp [gam]

theorem eK_inv {m : ℕ} (hm : m < 22) : (eK (G := G) m hm)⁻¹ = eK m hm :=
  inv_eq_of_mul_eq_one_right (eK_sq hm)

theorem gen_induct (P : QC G → Prop) (h1 : P 1) (hx : P xQ)
    (hm : ∀ a, ∀ m (hm : m < 22), P a → P (a * eK m hm)) (y : QC G) : P y := by
  have hI : ∀ s < 22, (arrOf (id32 22)).getD s 0 = 2 ^ s := by
    have : ∀ s < 22, fld32 (id32 22) s = 2 ^ s := by decide +kernel
    exact fun s hs => by rw [arrOf_getD _ hs, this s hs]
  have key : ∀ m ≤ 22, P (mkQ (autApplyN G (arrOf (id32 22)) y.1 m) (autApplyN_lt _ _ _ _)) := by
    intro m
    induction m with
    | zero =>
      intro _
      by_cases h22 : y.1.testBit 22
      · have e : mkQ (G := G) (autApplyN G (arrOf (id32 22)) y.1 0) (autApplyN_lt _ _ _ _) = xQ := by
          refine QC.ext' ?_
          rw [mkQ_val, autApplyN.eq_1, ite_eq_left h22]
          rfl
        rw [e]
        exact hx
      · have e : mkQ (G := G) (autApplyN G (arrOf (id32 22)) y.1 0) (autApplyN_lt _ _ _ _) = 1 := by
          refine QC.ext' ?_
          rw [mkQ_val, autApplyN.eq_1, ite_eq_right h22, QC.one_val]
        rw [e]
        exact h1
    | succ m ih =>
      intro hm22
      have hP := ih (by omega)
      by_cases hb : y.1.testBit m
      · have e : mkQ (G := G) (autApplyN G (arrOf (id32 22)) y.1 (m + 1)) (autApplyN_lt _ _ _ _) =
            mkQ (autApplyN G (arrOf (id32 22)) y.1 m) (autApplyN_lt _ _ _ _) * eK m (by omega) := by
          refine QC.ext' ?_
          rw [mkQ_val, autApplyN.eq_2, ite_eq_left hb, QC.mul_val, mkQ_val, hI m (by omega)]
          rfl
        rw [e]
        exact hm _ m _ hP
      · have e : mkQ (G := G) (autApplyN G (arrOf (id32 22)) y.1 (m + 1)) (autApplyN_lt _ _ _ _) =
            mkQ (autApplyN G (arrOf (id32 22)) y.1 m) (autApplyN_lt _ _ _ _) := by
          refine QC.ext' ?_
          rw [mkQ_val, mkQ_val, autApplyN.eq_2, ite_eq_right hb]
        rw [e]
        exact hP
  have hP := key 22 (Nat.le_refl 22)
  have e : mkQ (G := G) (autApplyN G (arrOf (id32 22)) y.1 22) (autApplyN_lt _ _ _ _) = y := by
    refine QC.ext' ?_
    rw [mkQ_val]
    exact autApply_id G y.2
  rwa [e] at hP

theorem hom_ext' {φ ψ : QC G →* QC G} (hx : φ xQ = ψ xQ)
    (he : ∀ m (hm : m < 22), φ (eK m hm) = ψ (eK m hm)) (y : QC G) : φ y = ψ y :=
  gen_induct (fun a => φ a = ψ a) (by rw [map_one, map_one]) hx
    (fun a m hm h => by rw [map_mul, map_mul, h, he m hm]) y

@[expose] def cjQ (φ : QC G →* QC G) (e n : QC G) : QC G := φ e⁻¹ * n * e

theorem cjQ_mul (φ : QC G →* QC G) (e f n : QC G) : cjQ φ (e * f) n = cjQ φ f (cjQ φ e n) := by
  simp only [cjQ, mul_inv_rev, map_mul, mul_assoc]

theorem cjQ_one (φ : QC G →* QC G) (n : QC G) : cjQ φ 1 n = n := by
  simp [cjQ]

theorem cjQ_x {φ : QC G →* QC G} (hφ : φ xQ = xQ) (n : QC G) : cjQ φ xQ n = n := by
  rw [cjQ, xQ_inv, hφ, xQ_comm, mul_assoc, xQ_sq, mul_one]

theorem cjQ_mulx (φ : QC G →* QC G) (e n : QC G) : cjQ φ e (n * xQ) = cjQ φ e n * xQ := by
  simp only [cjQ, mul_assoc]
  rw [xQ_comm e]

theorem piQ_cjQ {A : Array ℕ} (hA : RelOK G A) (e n : QC G) :
    piQ (cjQ (homOf G A hA) e n) = piQ n ^^^ (mv G A (piQ e) ^^^ piQ e) := by
  rw [cjQ, piQ_mul, piQ_mul, map_inv, piQ_inv, piQ_hom]
  ac_rfl

@[expose] def invQ (φ : QC G →* QC G) (W n : QC G) : Prop := W * φ n * n = 1

theorem conj_one_iff (e y : QC G) : e⁻¹ * y * e = 1 ↔ y = 1 := by
  constructor
  · intro h
    have := congrArg (fun z => e * z * e⁻¹) h
    simpa [mul_assoc] using this
  · intro h
    rw [h, mul_one, inv_mul_cancel]

theorem invQ_cj {φ : QC G →* QC G} (hsq : ∀ y, φ (φ y) = y) {W : QC G} (hW : ∀ y, W * y = y * W)
    (e n : QC G) : invQ φ W (cjQ φ e n) ↔ invQ φ W n := by
  unfold invQ
  have h1 : φ (cjQ φ e n) = e⁻¹ * φ n * φ e := by rw [cjQ, map_mul, map_mul, hsq]
  have key : W * φ (cjQ φ e n) * cjQ φ e n = e⁻¹ * (W * φ n * n) * e := by
    rw [h1, cjQ, map_inv]
    calc W * (e⁻¹ * φ n * φ e) * ((φ e)⁻¹ * n * e)
        = W * e⁻¹ * φ n * (φ e * (φ e)⁻¹) * n * e := by simp only [mul_assoc]
      _ = W * e⁻¹ * φ n * n * e := by rw [mul_inv_cancel, mul_one]
      _ = e⁻¹ * W * φ n * n * e := by rw [hW e⁻¹]
      _ = e⁻¹ * (W * φ n * n) * e := by simp only [mul_assoc]
  rw [key, conj_one_iff]

theorem invQ_x {φ : QC G →* QC G} (hφ : φ xQ = xQ) (W n : QC G) :
    invQ φ W (n * xQ) ↔ invQ φ W n := by
  unfold invQ
  have e : W * φ (n * xQ) * (n * xQ) = W * φ n * n * (xQ * xQ) := by
    rw [map_mul, hφ]
    simp only [mul_assoc]
    rw [← mul_assoc xQ n xQ, xQ_comm n, mul_assoc n xQ xQ]
  rw [e, xQ_sq, mul_one]

theorem conjK_eq (hG : SymG G) {AP : ℕ} (hA : RelOK G (arrOf AP)) (e n : QC G) :
    conjK (loOf G) AP e.1 n.1 = (cjQ (homOf G (arrOf AP) hA) e n).1 := by
  unfold conjK qinvK
  simp only [mulQ_loOf G hG, autQ_loOf G hG]
  rw [cjQ, QC.mul_val, QC.mul_val, homOf_val, QC.inv_val]
  rw [qinvG, qmul_assoc G e.1 e.1 e.1,
    qmul_assoc G (autApply G (arrOf AP) (qmul G e.1 (qmul G e.1 e.1))) n.1 e.1]

theorem qconj_eq {A : Array ℕ} (hA : RelOK G A) (hwf : ∀ i < 22, A.getD i 0 < 2 ^ 23) {m : ℕ}
    (hm : m < 22) (n : QC G) : qconj G A m n.1 = (cjQ (homOf G A hA) (eK m hm) n).1 := by
  rw [cjQ, eK_inv, QC.mul_val, QC.mul_val, homOf_val]
  unfold qconj
  change qmul G (A.getD m 0) (qmul G n.1 (2 ^ m)) = qmul G (qmul G (autApply G A (2 ^ m)) n.1) (2 ^ m)
  rw [autApply_two_pow G A hm (hwf m hm), qmul_assoc]

theorem isInv_iff {A : Array ℕ} (hA : RelOK G A) (W n : QC G) :
    isInv G A W.1 n.1 = true ↔ invQ (homOf G A hA) W n := by
  unfold isInv invQ
  rw [beq_iff_eq, mul_assoc]
  constructor
  · intro h
    apply QC.ext'
    rw [QC.mul_val, QC.mul_val, homOf_val, QC.one_val]
    exact h
  · intro h
    have := congrArg Subtype.val h
    rwa [QC.mul_val, QC.mul_val, homOf_val, QC.one_val] at this

theorem isInvK_eq (hG : SymG G) (AP w n : ℕ) :
    isInvK (loOf G) AP w n = isInv G (arrOf AP) w n := by
  unfold isInvK isInv
  simp only [mulQ_loOf G hG, autQ_loOf G hG]
  apply Bool.eq_iff_iff.2
  rw [beq_true, beq_iff_eq]

end CertificateChecks.KernelBM.CTIB.CosetQ

end
