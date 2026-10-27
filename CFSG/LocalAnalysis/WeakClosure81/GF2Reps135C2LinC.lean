module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2LinB

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {W : Type} [CommGroup W] [Finite W] {L : Subgroup (MulAut W)} {t : MulAut W}

theorem w135c2_dichotomy (hW : ∀ w : W, w ^ 2 = 1) (hirr : IsIrrOn L ⊤ ⊥)
    (htN : ∀ g ∈ L, t * g * t⁻¹ ∈ L) (ht2 : orderOf t = 2) :
    ∃ k d : ℕ, 1 ≤ k ∧ Nat.card ↥(LEnd L) = 2 ^ k ∧ rk W = k * d ∧
      ((∃ r : ℕ, 1 ≤ r ∧ E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) = k * r) ∨
        (Even k ∧ rk W = 2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)))) := by
  obtain ⟨k, hk1, hk⟩ := w135c2_lend_card hW hirr
  obtain ⟨d, hd⟩ := w135c2_rk_eq_mul hW hirr hk
  obtain ⟨σ, hσ2, hσ⟩ := w135c2_exists_sigma htN ht2
  by_cases hid : ∀ φ, σ φ = φ
  · exact ⟨k, d, hk1, hk, hd, Or.inl (w135c2_linear hW hirr ht2 hk σ hσ hid)⟩
  · obtain ⟨φ, hφ⟩ := not_forall.mp hid
    exact ⟨k, d, hk1, hk, hd,
      Or.inr (w135c2_semilinear hW hirr ht2 hk σ hσ hσ2 ⟨φ, hφ⟩)⟩

theorem w135c2_one_lt_dim (hW : ∀ w : W, w ^ 2 = 1) (hirr : IsIrrOn L ⊤ ⊥)
    (hnab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) {k d : ℕ} (hk : Nat.card ↥(LEnd L) = 2 ^ k)
    (hd : rk W = k * d) : 2 ≤ d := by
  classical
  have hd0 : d ≠ 0 := by
    intro hd0
    have hnt : Nontrivial W := by
      rw [← not_subsingleton_iff_nontrivial]
      intro hss
      have htop : (⊤ : Subgroup W) = ⊥ := by
        ext w
        rw [Subgroup.mem_bot]
        exact ⟨fun _ => Subsingleton.elim w 1, fun _ => Subgroup.mem_top w⟩
      exact (bot_lt_iff_ne_bot.mp hirr.1) htop
    have hlt : 1 < Nat.card W := Finite.one_lt_card
    rw [w135_card_eq_two_pow_rk hW, hd, hd0, mul_zero, pow_zero] at hlt
    exact absurd hlt (lt_irrefl 1)
  by_contra hlt2
  have hd1 : d = 1 := by omega
  have hcardEq : Nat.card (Additive W) = Nat.card ↥(LEnd L) := by
    rw [Nat.card_congr Additive.toMul, w135_card_eq_two_pow_rk hW, hd, hd1, mul_one, hk]
  letI : Field ↥(LEnd L) := (w135c2_lend_isField hW hirr).toField
  letI : Module ↥(LEnd L) (Additive W) := Module.compHom (Additive W) (LEnd L).subtype
  haveI : Finite ↥(LEnd L) := by
    haveI : Finite (AddMonoid.End (Additive W)) := DFunLike.finite _
    infer_instance
  have htwo : 2 ≤ Nat.card ↥(LEnd L) := by
    have := Finite.one_lt_card (α := ↥(LEnd L))
    omega
  haveI : Module.Finite ↥(LEnd L) (Additive W) := Module.Finite.of_finite
  have hfinrank : Module.finrank ↥(LEnd L) (Additive W) = 1 := by
    refine Nat.pow_right_injective htwo ?_
    change Nat.card ↥(LEnd L) ^ Module.finrank ↥(LEnd L) (Additive W) =
      Nat.card ↥(LEnd L) ^ 1
    rw [pow_one, ← Module.natCard_eq_pow_finrank (K := ↥(LEnd L)) (V := Additive W)]
    exact hcardEq
  have hlin : ∀ g ∈ L, ∃ c : ↥(LEnd L), ∀ w : Additive W,
      (MulEquiv.toAdditive g) w = c.1 w := by
    intro g hg
    let gA : Additive W ≃+ Additive W := MulEquiv.toAdditive g
    let gL : Additive W →ₗ[↥(LEnd L)] Additive W :=
      { toFun := gA
        map_add' := gA.map_add
        map_smul' := fun c w => by
          show gA (c.1 w) = c.1 (gA w)
          exact (c.2 g hg w).symm }
    obtain ⟨c, hc, -⟩ := LinearMap.existsUnique_eq_smul_id_of_finrank_eq_one hfinrank gL
    refine ⟨c, fun w => ?_⟩
    have h := DFunLike.congr_fun hc w
    have h2 : (c • (LinearMap.id : Additive W →ₗ[↥(LEnd L)] Additive W)) w = c.1 w := by
      rw [LinearMap.smul_apply, LinearMap.id_apply]
      rfl
    rw [h2] at h
    simpa [gL, gA] using h
  obtain ⟨a, ha, b, hb, hab⟩ := hnab
  refine hab ?_
  obtain ⟨ca, hca⟩ := hlin a ha
  obtain ⟨cb, hcb⟩ := hlin b hb
  apply MulEquiv.ext
  intro x
  refine Additive.ofMul.injective ?_
  have hfun : Additive.ofMul ((a * b) x) = Additive.ofMul ((b * a) x) := by
    calc Additive.ofMul ((a * b) x)
        = (MulEquiv.toAdditive a) ((MulEquiv.toAdditive b) (Additive.ofMul x)) := by
          show Additive.ofMul ((a * b) x) = Additive.ofMul (a (b x))
          rw [MulAut.mul_apply]
      _ = ca.1 ((MulEquiv.toAdditive b) (Additive.ofMul x)) := hca _
      _ = ca.1 (cb.1 (Additive.ofMul x)) := by rw [hcb (Additive.ofMul x)]
      _ = ((ca * cb : ↥(LEnd L)).1) (Additive.ofMul x) := by
          rw [Subring.coe_mul]
          rfl
      _ = ((cb * ca : ↥(LEnd L)).1) (Additive.ofMul x) := by rw [mul_comm]
      _ = cb.1 (ca.1 (Additive.ofMul x)) := by
          rw [Subring.coe_mul]
          rfl
      _ = cb.1 ((MulEquiv.toAdditive a) (Additive.ofMul x)) := by
          rw [hca (Additive.ofMul x)]
      _ = (MulEquiv.toAdditive b) ((MulEquiv.toAdditive a) (Additive.ofMul x)) :=
          (hcb _).symm
      _ = Additive.ofMul ((b * a) x) := by
          show Additive.ofMul (b (a x)) = Additive.ofMul ((b * a) x)
          rw [MulAut.mul_apply]
  exact hfun

theorem w135c2_range (hW : ∀ w : W, w ^ 2 = 1) (hirr : IsIrrOn L ⊤ ⊥)
    (hnab : ∃ a ∈ L, ∃ b ∈ L, a * b ≠ b * a) (htN : ∀ g ∈ L, t * g * t⁻¹ ∈ L)
    (ht2 : orderOf t = 2) (hm : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) ≤ 3) {A : ℕ} (hA : 3 ≤ A)
    (hgen : rk W ≤ A * E3.mQuot ⊤ (fixV (Subgroup.zpowers t))) :
    ∃ k d : ℕ, Nat.card ↥(LEnd L) = 2 ^ k ∧ rk W = k * d ∧
      ((k = 1 ∧ d ≤ 3 * A) ∨ ((k = 2 ∨ k = 3) ∧ d ≤ A)) := by
  obtain ⟨k, d, hk1, hk, hd, hcase⟩ := w135c2_dichotomy hW hirr htN ht2
  refine ⟨k, d, hk, hd, ?_⟩
  rcases hcase with ⟨r, hr1, hr⟩ | ⟨heven, hrk⟩
  ·
    have hk_le : k ≤ 3 := by
      calc k = k * 1 := (mul_one k).symm
        _ ≤ k * r := Nat.mul_le_mul_left k hr1
        _ = E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := hr.symm
        _ ≤ 3 := hm
    have hdAr : d ≤ A * r := by
      have h : k * d ≤ k * (A * r) := by
        calc k * d = rk W := hd.symm
          _ ≤ A * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := hgen
          _ = A * (k * r) := by rw [hr]
          _ = k * (A * r) := by ring
      exact Nat.le_of_mul_le_mul_left h (by omega)
    by_cases hk1' : k = 1
    · left
      have hmr : E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) = r := by
        rw [hr, hk1', one_mul]
      refine ⟨hk1', ?_⟩
      calc d ≤ A * r := hdAr
        _ = A * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by rw [hmr]
        _ ≤ A * 3 := Nat.mul_le_mul_left A hm
        _ = 3 * A := by ring
    · right
      have hk2 : 2 ≤ k := by omega
      refine ⟨by omega, ?_⟩
      have hr1' : r = 1 := by
        have hkr : k * r ≤ 3 := by rw [← hr]; exact hm
        by_contra hrne
        have hr2 : 2 ≤ r := by omega
        have h4 : 4 ≤ k * r := by
          have := Nat.mul_le_mul hk2 hr2
          simpa using this
        omega
      calc d ≤ A * r := hdAr
        _ = A := by rw [hr1', mul_one]
  ·
    have hd2 : 2 ≤ d := w135c2_one_lt_dim hW hirr hnab hk hd
    have hkd6 : k * d ≤ 6 := by
      calc k * d = rk W := hd.symm
        _ = 2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := hrk
        _ ≤ 2 * 3 := Nat.mul_le_mul_left 2 hm
        _ = 6 := by norm_num
    have hk_le : k ≤ 3 := by nlinarith [hd2, hk1, hkd6]
    have hk2 : k = 2 := by
      obtain ⟨s, hs⟩ := heven
      omega
    refine Or.inr ⟨Or.inl hk2, ?_⟩
    have hdm : d = E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := by
      have h : k * d = 2 * E3.mQuot ⊤ (fixV (Subgroup.zpowers t)) := hd ▸ hrk
      rw [hk2] at h
      omega
    omega

end CFSG.LocalAnalysis.WeakClosure81
