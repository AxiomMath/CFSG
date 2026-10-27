module

public import CFSG.Quasithin.Background.HF1607M22
public import CFSG.Quasithin.Background.HFCode22

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code

variable {V : Type*} [CommGroup V] {L M : Subgroup (MulAut V)}

theorem psiC22_mul_apply (a b : ↥mog22plus) (w : W10) :
    psiC22 (a * b) w = psiC22 a (psiC22 b w) := by
  rw [map_mul]
  rfl

theorem psiC22_inv_apply (a : ↥mog22plus) (w : W10) : psiC22 a⁻¹ (psiC22 a w) = w := by
  rw [← psiC22_mul_apply, inv_mul_cancel, map_one]
  rfl

theorem psiC22_apply_inv (a : ↥mog22plus) (w : W10) : psiC22 a (psiC22 a⁻¹ w) = w := by
  rw [← psiC22_mul_apply, mul_inv_cancel, map_one]
  rfl

theorem psiC22_one_apply (w : W10) : psiC22 1 w = w := by
  rw [map_one]
  rfl

theorem code22_card_le_two
    [Finite V] (hLM : IsOver L M) (h : MathieuCode22 L ⊤ ⊥) {Y : Subgroup (MulAut V)}
    (hYM : Y ≤ M) (hY3 : Nat.card Y = 3) (hY6 : rkIdx (fixV Y) = 6) {A : Subgroup (MulAut V)}
    (hAC : A ≤ M ⊓ centSub (fixV Y)) (hAe : IsElemAbelian2 A) : Nat.card A ≤ 2 := by
  have : Finite (MulAut V) := finite_mulAut V
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨y, hyY, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
    by_contra hno
    push Not at hno
    have hbot : Y = ⊥ := (Subgroup.eq_bot_iff_forall Y).2 hno
    rw [hbot, Subgroup.card_bot] at hY3
    norm_num at hY3
  have hyo : orderOf y = 3 := by
    have hd : orderOf y ∣ 3 := by
      rw [← hY3]
      exact Subgroup.orderOf_dvd_natCard Y hyY
    rcases (Nat.dvd_prime (by norm_num)).1 hd with h1 | h1
    · exact absurd (orderOf_eq_one_iff.1 h1) hy1
    · exact h1
  have hYeq : Y = Subgroup.zpowers y := by
    symm
    apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hyY)
    rw [Nat.card_zpowers, hyo, hY3]
  subst hYeq
  obtain ⟨e, he⟩ := code22_std h
  have hMR : ∀ x ∈ M, congrHom e x ∈ psiC22.range := fun x hx =>
    map_le_rangeC22 hLM he ((Subgroup.zpowers_le).2 hx) ⟨x, Subgroup.mem_zpowers x, rfl⟩
  set φ3 := T22s3.toSub mog22plus (T22s3.mem_mog22plus T22s3_ok.2.2) with hφ3
  have hsyl3 := card_T22sp (T := T22s3) (by norm_num : Nat.Prime 3) (n := 2) T22s3_ok.2.1
    (by norm_num : (887040 : ℕ) = 3 ^ 2 * 98560) (by norm_num)
  obtain ⟨g, s, -, hgs⟩ := exists_conj_elemModel psiC22 rhoC10_mog22plus_injective φ3
    (T22s3.toSub_injective _ _) hsyl3 e (hMR y (hYM (Subgroup.mem_zpowers y))) hyo
  set e1 := twistEquiv e psiC22 g with he1
  have hy1' : ∀ v, e1 (y v) = psiC22 (φ3 s) (e1 v) := apply_of_congrHom_eq hgs
  have hact : ∀ m : ℕ, psiC22 (φ3 s) (toW 10 m) = toW 10 (actC10 (T22s3.arr s) m) :=
    fun m => rhoC10_toW mog22plus le_rfl _ (T22s3.hasArr_toSub _ _ s) m
  have hX1 : ∀ m < 2 ^ 10, (MaskCoords.ofEquiv e1).vm m ∈ fixV (Subgroup.zpowers y) ↔
      actC10 (T22s3.arr s) m = m := by
    intro m hm
    rw [mem_fixV_zpowers_iff, MaskCoords.ofEquiv_vm]
    have h1 : e1 (y (e1.symm (toW 10 m))) = toW 10 (actC10 (T22s3.arr s) m) := by
      rw [hy1', MulEquiv.apply_symm_apply, hact m]
    have h2 : y (e1.symm (toW 10 m)) = e1.symm (toW 10 (actC10 (T22s3.arr s) m)) := by
      rw [← h1, MulEquiv.symm_apply_apply]
    rw [h2]
    constructor
    · intro h3
      exact toW_inj (actC10_lt _ _) hm (e1.symm.injective h3)
    · intro h3
      rw [h3]
  have hcard : Nat.card (fixV (Subgroup.zpowers y)) = (codeFixArr10 (T22s3.arr s)).length :=
    (MaskCoords.ofEquiv e1).card_eq _ _ fun m hm => (hX1 m hm).trans (by simp)
  have h16 : (codeFixArr10 (T22s3.arr s)).length = 2 ^ 4 := by
    have hr := (MaskCoords.ofEquiv e1).rkIdx_of_card hcard
    have hpow := card_eq_two_pow (MaskCoords.ofEquiv e1).sq_eq_one (fixV (Subgroup.zpowers y))
    rw [hcard] at hpow
    rw [hY6, hpow, Nat.log_pow (by norm_num)] at hr
    rw [hpow, show rk ↥(fixV (Subgroup.zpowers y)) = 4 by omega]
  obtain ⟨hA, -, hAok, hApair, hAconj⟩ := Certificates.certificate7238.2 s h16
  obtain ⟨σh, hσhA, hσh⟩ := exists_of_inAutOK hAok
  have hσhP : σh ∈ stabPair01 := by
    simp only [Bool.or_eq_true, Bool.and_eq_true, beq_iff_eq] at hApair
    rcases hApair with ⟨h0', h1'⟩ | ⟨h0', h1'⟩
    · exact Or.inl ⟨Fin.ext ((hσh 0).trans h0'), Fin.ext ((hσh 1).trans h1')⟩
    · exact Or.inr ⟨Fin.ext ((hσh 0).trans h0'), Fin.ext ((hσh 1).trans h1')⟩
  set a : ↥mog22plus := ⟨σh, hσhA, hσhP⟩ with ha
  set σ0 : ↥mog22plus := a * φ3 s * a⁻¹ with hσ0def
  have h0 : HasArr (σ0 : Equiv.Perm (Fin 24)) s0Arr22 := by
    have hc : ∀ i < 24, hA[(T22s3.arr s)[i]!]! = s0Arr22[hA[i]!]! := by
      intro i hi
      have := List.all_eq_true.1 hAconj i (List.mem_range.2 hi)
      simpa using this
    have hs : HasArr ((φ3 s : ↥mog22plus) : Equiv.Perm (Fin 24)) (T22s3.arr s) :=
      T22s3.hasArr_toSub _ _ s
    intro j
    have hj : σh (σh⁻¹ j) = j := by simp
    have hσ0j : (σ0 : Equiv.Perm (Fin 24)) j =
        σh ((φ3 s : Equiv.Perm (Fin 24)) (σh⁻¹ j)) := rfl
    rw [hσ0j, hσh, hs, hc _ (σh⁻¹ j).2, ← hσh (σh⁻¹ j), hj]
  have hσ0apply : ∀ w, psiC22 σ0 w = psiC22 a (psiC22 (φ3 s) (psiC22 a⁻¹ w)) := fun w => by
    rw [hσ0def, psiC22_mul_apply, psiC22_mul_apply]
  have hs3 : φ3 s ^ 3 = 1 := by
    have hso : orderOf (φ3 s) = 3 :=
      (orderOf_injective psiC22 rhoC10_mog22plus_injective (φ3 s)).symm.trans
        ((congrArg orderOf hgs.symm).trans ((orderOf_injective _ (congrHom_injective e1) y).trans
          hyo))
    rw [← hso, pow_orderOf_eq_one]
  have hk_of : ∀ x ∈ M, ∃ k : ↥mog22plus, ∀ v, e1 (x v) = psiC22 k (e1 v) := by
    intro x hxM
    obtain ⟨k, hk⟩ := hMR x hxM
    refine ⟨g * k * g⁻¹, fun v => ?_⟩
    have hx0 : ∀ v, e (x v) = psiC22 k (e v) := apply_of_congrHom_eq hk.symm
    show psiC22 g (e (x v)) = psiC22 (g * k * g⁻¹) (psiC22 g (e v))
    rw [hx0, psiC22_mul_apply, psiC22_mul_apply, psiC22_inv_apply]
  have key : ∀ x ∈ A, ∀ k : ↥mog22plus, (∀ v, e1 (x v) = psiC22 k (e1 v)) →
      ((a * k * a⁻¹ : ↥mog22plus) : Equiv.Perm (Fin 24)) 0 = 0 → k = 1 := by
    intro x hxA k hk hτ0
    have hxC := (hAC hxA).2
    have hfixτ : ∀ w, psiC22 σ0 w = w → psiC22 (a * k * a⁻¹) w = w := by
      intro w hw
      set w' := psiC22 a⁻¹ w with hw'
      have hsw : psiC22 (φ3 s) w' = w' := by
        have := congrArg (psiC22 a⁻¹) ((hσ0apply w).symm.trans hw)
        rwa [psiC22_inv_apply] at this
      have hv : y (e1.symm w') = e1.symm w' := by
        apply e1.injective
        rw [hy1', MulEquiv.apply_symm_apply, hsw]
      have hxv : x (e1.symm w') = e1.symm w' :=
        mem_centSub.1 hxC _ (mem_fixV_zpowers_iff.2 hv)
      have hkw : psiC22 k w' = w' := by
        have := hk (e1.symm w')
        rw [hxv, MulEquiv.apply_symm_apply] at this
        exact this.symm
      rw [psiC22_mul_apply, psiC22_mul_apply, ← hw', hkw, hw', psiC22_apply_inv]
    obtain ⟨j, hj⟩ := Subgroup.mem_zpowers_iff.1 (mem_zpowers_s0_22 h0 hτ0 hfixτ)
    have hk2 : k * k = 1 := by
      apply rhoC10_mog22plus_injective
      refine MulEquiv.ext fun w => ?_
      have hx2 : x * x = 1 := by rw [← sq]; exact hAe.2 x hxA
      have hxx : x (x (e1.symm w)) = e1.symm w := by
        show (x * x) (e1.symm w) = e1.symm w
        rw [hx2]
        rfl
      calc psiC22 (k * k) w = psiC22 k (psiC22 k (e1 (e1.symm w))) := by
            rw [psiC22_mul_apply, MulEquiv.apply_symm_apply]
        _ = psiC22 k (e1 (x (e1.symm w))) := by rw [← hk (e1.symm w)]
        _ = e1 (x (x (e1.symm w))) := by rw [← hk (x (e1.symm w))]
        _ = w := by rw [hxx, MulEquiv.apply_symm_apply]
        _ = psiC22 1 w := (psiC22_one_apply w).symm
    have hτ3 : (a * k * a⁻¹) ^ 3 = 1 := by
      rw [← hj, ← zpow_natCast, ← zpow_mul, mul_comm, zpow_mul, zpow_natCast, hσ0def,
        conj_pow, hs3, mul_one, mul_inv_cancel, one_zpow]
    have hτ2 : (a * k * a⁻¹) ^ 2 = 1 := by
      rw [conj_pow, sq, hk2, mul_one, mul_inv_cancel]
    have hτ1 : a * k * a⁻¹ = 1 := by
      have : a * k * a⁻¹ = (a * k * a⁻¹) ^ 3 * ((a * k * a⁻¹) ^ 2)⁻¹ := by group
      rw [this, hτ3, hτ2, inv_one, mul_one]
    calc k = a⁻¹ * (a * k * a⁻¹) * a := by group
      _ = 1 := by rw [hτ1]; group
  choose kOf hkOf using fun x : ↥A => hk_of x.1 (hAC x.2).1
  have hτ01 : ∀ x : ↥A, ((a * kOf x * a⁻¹ : ↥mog22plus) : Equiv.Perm (Fin 24)) 0 = 0 ∨
      ((a * kOf x * a⁻¹ : ↥mog22plus) : Equiv.Perm (Fin 24)) 0 = 1 := by
    intro x
    rcases (a * kOf x * a⁻¹).2.2 with ⟨h1, -⟩ | ⟨h1, -⟩
    · exact Or.inl h1
    · exact Or.inr h1
  have hinj : Function.Injective fun x : ↥A =>
      decide (((a * kOf x * a⁻¹ : ↥mog22plus) : Equiv.Perm (Fin 24)) 0 = 0) := by
    intro x x' hxx'
    have hiff := decide_eq_decide.1 hxx'
    have hk' : ∀ v, e1 ((x.1 * x'.1⁻¹) v) = psiC22 (kOf x * (kOf x')⁻¹) (e1 v) := by
      intro v
      have h1 : e1 v = psiC22 (kOf x') (e1 (x'.1⁻¹ v)) := by
        have := hkOf x' (x'.1⁻¹ v)
        have hv : x'.1 (x'.1⁻¹ v) = v := by
          show (x'.1 * x'.1⁻¹) v = v
          rw [mul_inv_cancel]
          rfl
        rwa [hv] at this
      have h2 : e1 (x'.1⁻¹ v) = psiC22 (kOf x')⁻¹ (e1 v) := by
        rw [h1, psiC22_inv_apply]
      show e1 (x.1 (x'.1⁻¹ v)) = _
      rw [hkOf x, h2, psiC22_mul_apply]
    have hτ0 : ((a * (kOf x * (kOf x')⁻¹) * a⁻¹ : ↥mog22plus) : Equiv.Perm (Fin 24)) 0 = 0 := by
      have e2 : a * (kOf x * (kOf x')⁻¹) * a⁻¹ =
          (a * kOf x * a⁻¹) * (a * kOf x' * a⁻¹)⁻¹ := by group
      rw [e2, Subgroup.coe_mul, Subgroup.coe_inv, Equiv.Perm.mul_apply]
      rcases hτ01 x' with h' | h'
      · have hx0 : ((a * kOf x * a⁻¹ : ↥mog22plus) : Equiv.Perm (Fin 24)) 0 = 0 :=
          hiff.2 h'
        rw [show ((a * kOf x' * a⁻¹ : ↥mog22plus) : Equiv.Perm (Fin 24))⁻¹ 0 = 0 from by
          rw [Equiv.Perm.inv_eq_iff_eq, h'], hx0]
      · have hx1 : ((a * kOf x * a⁻¹ : ↥mog22plus) : Equiv.Perm (Fin 24)) 0 = 1 := by
          rcases hτ01 x with h'' | h''
          · exfalso
            have := hiff.1 h''
            rw [h'] at this
            exact absurd this (by decide)
          · exact h''
        have hx'1 : ((a * kOf x' * a⁻¹ : ↥mog22plus) : Equiv.Perm (Fin 24)) 1 = 0 := by
          rcases (a * kOf x' * a⁻¹).2.2 with ⟨h3, -⟩ | ⟨-, h3⟩
          · rw [h'] at h3
            exact absurd h3 (by decide)
          · exact h3
        have hx1' : ((a * kOf x * a⁻¹ : ↥mog22plus) : Equiv.Perm (Fin 24)) 1 = 0 := by
          rcases (a * kOf x * a⁻¹).2.2 with ⟨h3, -⟩ | ⟨-, h3⟩
          · rw [hx1] at h3
            exact absurd h3 (by decide)
          · exact h3
        rw [show ((a * kOf x' * a⁻¹ : ↥mog22plus) : Equiv.Perm (Fin 24))⁻¹ 0 = 1 from by
          rw [Equiv.Perm.inv_eq_iff_eq, hx'1], hx1']
    have hk1 := key _ (A.mul_mem x.2 (A.inv_mem x'.2)) _ hk' hτ0
    have : x.1 = x'.1 := by
      have hxx : x.1 * x'.1⁻¹ = 1 := by
        refine MulEquiv.ext fun v => e1.injective ?_
        rw [hk', hk1, psiC22_one_apply, MulAut.one_apply]
      exact mul_inv_eq_one.1 hxx
    exact Subtype.ext this
  calc Nat.card A ≤ Nat.card Bool := Nat.card_le_card_of_injective _ hinj
    _ = 2 := by simp

theorem code22_h1607
    [Finite V] (hLM : IsOver L M) (h : MathieuCode22 L ⊤ ⊥) {s : ℕ} (hs : s = 2 ∨ s = 3)
    {A Y : Subgroup (MulAut V)} (hAM : A ≤ M) (hYM : Y ≤ M) (hAe : IsElemAbelian2 A)
    (hAc : Nat.card A = 2 ^ (2 * s)) (hYc : Nat.card Y = 3) :
    rkIdx (fixV (A ⊔ Y)) ≠ 2 * (s + 1) := by
  rcases hs with rfl | rfl
  · intro h6
    have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
    obtain ⟨y, hyY, hy1⟩ : ∃ y ∈ Y, y ≠ 1 := by
      by_contra hno
      push Not at hno
      have hbot : Y = ⊥ := (Subgroup.eq_bot_iff_forall Y).2 hno
      rw [hbot, Subgroup.card_bot] at hYc
      norm_num at hYc
    have hyo : orderOf y = 3 := by
      have hd : orderOf y ∣ 3 := by
        rw [← hYc]
        exact Subgroup.orderOf_dvd_natCard Y hyY
      rcases (Nat.dvd_prime (by norm_num)).1 hd with h1 | h1
      · exact absurd (orderOf_eq_one_iff.1 h1) hy1
      · exact h1
    have hYeq : Y = Subgroup.zpowers y := by
      symm
      apply Subgroup.eq_of_le_of_card_ge ((Subgroup.zpowers_le).2 hyY)
      rw [Nat.card_zpowers, hyo, hYc]
    have hY6 : 6 ≤ rkIdx (fixV Y) := by
      rw [hYeq]
      exact code22_odd_le hLM h (hYM hyY) (by norm_num) (by norm_num) hyo
    have hle : fixV (A ⊔ Y) ≤ fixV Y := fun v hv x hx => hv x (le_sup_right (b := Y) hx)
    have hle' := rkIdx_le_rkIdx_of_le hle
    have hY6' : rkIdx (fixV Y) = 6 := by omega
    have heq : fixV (A ⊔ Y) = fixV Y := by
      apply Subgroup.eq_of_le_of_card_ge hle
      obtain ⟨e, -⟩ := code22_std h
      set c := MaskCoords.ofEquiv e
      have h1 := rk_add_rkIdx (fixV (A ⊔ Y))
      have h2 := rk_add_rkIdx (fixV Y)
      rw [card_eq_two_pow c.sq_eq_one, card_eq_two_pow c.sq_eq_one]
      apply Nat.pow_le_pow_right (by norm_num)
      omega
    have hAC : A ≤ M ⊓ centSub (fixV Y) := by
      intro x hx
      refine ⟨hAM hx, mem_centSub.2 fun v hv => ?_⟩
      rw [← heq] at hv
      exact hv x (le_sup_left (a := A) hx)
    have := code22_card_le_two hLM h hYM hYc hY6' hAC hAe
    rw [hAc] at this
    norm_num at this
  · exfalso
    have := code22_card_le hLM h hAM hAe hAc
    omega

end CFSG.Quasithin.H.Mathieu
