module

public import CFSG.Assembly.LowTwoRankDefs

public section

namespace CFSG.RankThree.GF2n.Smith81.OrthTN

section Action

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]

@[expose] def tensorAct (g : Matrix (Fin 2) (Fin 2) K) (o : W → W) (p : W × W) : W × W :=
  (g 0 0 • o p.1 + g 0 1 • o p.2, g 1 0 • o p.1 + g 1 1 • o p.2)

end Action

section Normalizer

variable {K : Type*} [Field K] {W : Type*} [AddCommGroup W] [Module K W]

private theorem fixed_row (r₀ r₁ : K) (hr : r₀ ≠ 0 ∨ r₁ ≠ 0) (p : W × W)
    (h : r₀ • p.1 + r₁ • p.2 = 0) : ∃ w : W, p = (r₁ • w, (-r₀) • w) := by
  by_cases h0 : r₀ = 0
  · have h1 : r₁ ≠ 0 := hr.resolve_left (not_not.mpr h0)
    subst h0
    have h2 : p.2 = 0 := by
      have : r₁ • p.2 = 0 := by simpa using h
      exact (smul_eq_zero.mp this).resolve_left h1
    refine ⟨r₁⁻¹ • p.1, ?_⟩
    ext
    · simp [smul_smul, h1]
    · simp [h2]
  · refine ⟨(-r₀)⁻¹ • p.2, ?_⟩
    have h3 : p.1 = (-(r₀⁻¹ * r₁)) • p.2 := by
      have : r₀ • p.1 = -(r₁ • p.2) := eq_neg_of_add_eq_zero_left h
      calc p.1 = r₀⁻¹ • (r₀ • p.1) := by simp [smul_smul, h0]
        _ = (-(r₀⁻¹ * r₁)) • p.2 := by rw [this]; simp [smul_smul, neg_smul]
    ext
    · simp only [smul_smul]
      rw [h3]
      congr 1
      field_simp
    · simp [smul_smul, h0]

theorem fixed_tensorAct_subset (g : Matrix (Fin 2) (Fin 2) K) (hg : g ≠ 1) :
    ∃ c : Fin 2 → K, ∀ p : W × W, tensorAct g (fun w => w) p = p → ∃ w : W,
      p = (c 0 • w, c 1 • w) := by
  by_cases hrow : g 0 0 - 1 ≠ 0 ∨ g 0 1 ≠ 0
  · refine ⟨![g 0 1, -(g 0 0 - 1)], fun p hp => ?_⟩
    have h : (g 0 0 - 1) • p.1 + g 0 1 • p.2 = 0 := by
      have := congrArg Prod.fst hp
      simp only [tensorAct] at this
      rw [sub_smul, one_smul, sub_add_eq_add_sub, this, sub_self]
    simpa using fixed_row _ _ hrow p h
  · push Not at hrow
    have hrow1 : g 1 0 ≠ 0 ∨ g 1 1 - 1 ≠ 0 := by
      by_contra hcon
      push Not at hcon
      apply hg
      ext i j
      fin_cases i <;> fin_cases j <;> simp [sub_eq_zero.mp hrow.1, hrow.2, hcon.1,
        sub_eq_zero.mp hcon.2]
    refine ⟨![g 1 1 - 1, -(g 1 0)], fun p hp => ?_⟩
    have h : g 1 0 • p.1 + (g 1 1 - 1) • p.2 = 0 := by
      have := congrArg Prod.snd hp
      simp only [tensorAct] at this
      rw [sub_smul, one_smul, add_sub_assoc', this, sub_self]
    simpa using fixed_row _ _ hrow1 p h

private def slL (c : Fin 2 → K) : W →ₗ[K] W × W :=
  (c 0 • LinearMap.id).prod (c 1 • LinearMap.id)

private theorem slL_apply (c : Fin 2 → K) (w : W) : slL c w = (c 0 • w, c 1 • w) := rfl

private theorem exists_lin_of_slice [Nontrivial W] (f : W →ₗ[K] W × W)
    (hf : Function.Injective f)
    (h : ∃ c : Fin 2 → K, ∀ w, ∃ w', f w = (c 0 • w', c 1 • w')) :
    ∃ (c : Fin 2 → K) (A : W →ₗ[K] W), (c 0 ≠ 0 ∨ c 1 ≠ 0) ∧
      ∀ w, f w = (c 0 • A w, c 1 • A w) := by
  obtain ⟨c, hc⟩ := h
  have hne : c 0 ≠ 0 ∨ c 1 ≠ 0 := by
    by_contra hcon
    push Not at hcon
    obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
    obtain ⟨w', hw'⟩ := hc w₀
    have : f w₀ = f 0 := by
      rw [hw', hcon.1, hcon.2, map_zero]
      simp
    exact hw₀ (hf this)
  have hker : LinearMap.ker (slL (W := W) c) = ⊥ := by
    rw [LinearMap.ker_eq_bot]
    intro u v huv
    simp only [slL_apply, Prod.mk.injEq] at huv
    rcases hne with h0 | h1
    · exact smul_right_injective W h0 huv.1
    · exact smul_right_injective W h1 huv.2
  obtain ⟨r, hr⟩ := LinearMap.exists_leftInverse_of_injective (slL (W := W) c) hker
  refine ⟨c, r.comp f, hne, fun w => ?_⟩
  obtain ⟨w', hw'⟩ := hc w
  have hr' : r (slL c w') = w' := LinearMap.congr_fun hr w'
  have : (r.comp f) w = w' := by
    rw [LinearMap.comp_apply, hw']
    exact hr'
  rw [this]
  exact hw'

private theorem cramer_aux {a b c d e f : K} (hD : a * d - c * b ≠ 0) :
    ∃ μ₀ μ₁ : K, e = μ₀ * a + μ₁ * c ∧ f = μ₀ * b + μ₁ * d := by
  obtain ⟨D, hDe⟩ : ∃ D : K, D = a * d - c * b := ⟨_, rfl⟩
  rw [← hDe] at hD
  refine ⟨(e * d - c * f) / D, (a * f - e * b) / D, ?_, ?_⟩
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD, hDe]
    ring
  · rw [div_mul_eq_mul_div, div_mul_eq_mul_div, ← add_div, eq_div_iff hD, hDe]
    ring

private theorem indep_aux {c₀ c₁ : Fin 2 → K} (hD : c₀ 0 * c₁ 1 - c₁ 0 * c₀ 1 ≠ 0) {u v : W}
    (h0 : c₀ 0 • u + c₁ 0 • v = 0) (h1 : c₀ 1 • u + c₁ 1 • v = 0) : u = 0 ∧ v = 0 := by
  constructor
  · have : (c₀ 0 * c₁ 1 - c₁ 0 * c₀ 1) • u = 0 := by
      have e : (c₀ 0 * c₁ 1 - c₁ 0 * c₀ 1) • u =
          c₁ 1 • (c₀ 0 • u + c₁ 0 • v) - c₁ 0 • (c₀ 1 • u + c₁ 1 • v) := by module
      rw [e, h0, h1]
      simp
    exact (smul_eq_zero.mp this).resolve_left hD
  · have : (c₀ 0 * c₁ 1 - c₁ 0 * c₀ 1) • v = 0 := by
      have e : (c₀ 0 * c₁ 1 - c₁ 0 * c₀ 1) • v =
          c₀ 0 • (c₀ 1 • u + c₁ 1 • v) - c₀ 1 • (c₀ 0 • u + c₁ 0 • v) := by module
      rw [e, h0, h1]
      simp
    exact (smul_eq_zero.mp this).resolve_left hD

private theorem det_ne_zero_aux [Nontrivial W] (T : (W × W) ≃ₗ[K] (W × W))
    (c₀ c₁ : Fin 2 → K) (A B : W →ₗ[K] W) (hc₀ : c₀ 0 ≠ 0 ∨ c₀ 1 ≠ 0)
    (hT : ∀ x y, T (x, y) = (c₀ 0 • A x + c₁ 0 • B y, c₀ 1 • A x + c₁ 1 • B y)) :
    c₀ 0 * c₁ 1 - c₁ 0 * c₀ 1 ≠ 0 := by
  intro hD
  have key : ∀ q : W × W, c₀ 1 • q.1 = c₀ 0 • q.2 := by
    intro q
    obtain ⟨⟨x, y⟩, rfl⟩ := T.surjective q
    rw [hT]
    have e : c₀ 1 • (c₀ 0 • A x + c₁ 0 • B y) - c₀ 0 • (c₀ 1 • A x + c₁ 1 • B y)
        = (c₀ 1 * c₁ 0 - c₀ 0 * c₁ 1) • B y := by module
    have h0 : c₀ 1 * c₁ 0 - c₀ 0 * c₁ 1 = 0 := by linear_combination -hD
    rw [h0, zero_smul] at e
    exact sub_eq_zero.mp e
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
  have k1 := key (w₀, 0)
  have k2 := key (0, w₀)
  simp only [smul_zero] at k1 k2
  rcases hc₀ with h | h
  · exact hw₀ ((smul_eq_zero.mp k2.symm).resolve_left h)
  · exact hw₀ ((smul_eq_zero.mp k1).resolve_left h)

theorem slices_eq_tensorAct [Nontrivial W] (T : (W × W) ≃ₗ[K] (W × W))
    (h₀ : ∃ c : Fin 2 → K, ∀ w : W, ∃ w' : W, T (w, 0) = (c 0 • w', c 1 • w'))
    (h₁ : ∃ c : Fin 2 → K, ∀ w : W, ∃ w' : W, T (0, w) = (c 0 • w', c 1 • w'))
    (h₂ : ∃ c : Fin 2 → K, ∀ w : W, ∃ w' : W, T (w, w) = (c 0 • w', c 1 • w')) :
    ∃ (h : Matrix (Fin 2) (Fin 2) K) (o : W ≃ₗ[K] W), IsUnit h.det ∧
      ∀ p, T p = tensorAct h (fun w => o w) p := by
  obtain ⟨c₀, A, hc₀, hA⟩ := exists_lin_of_slice (T.toLinearMap ∘ₗ LinearMap.inl K W W)
    (T.injective.comp (LinearMap.inl_injective)) h₀
  obtain ⟨c₁, B, hc₁, hB⟩ := exists_lin_of_slice (T.toLinearMap ∘ₗ LinearMap.inr K W W)
    (T.injective.comp (LinearMap.inr_injective)) h₁
  obtain ⟨c₂, C, hc₂, hC⟩ := exists_lin_of_slice
    (T.toLinearMap ∘ₗ LinearMap.prod LinearMap.id LinearMap.id)
    (T.injective.comp fun a b hab => congrArg Prod.fst hab) h₂
  replace hA : ∀ w, T (w, 0) = (c₀ 0 • A w, c₀ 1 • A w) := hA
  replace hB : ∀ w, T (0, w) = (c₁ 0 • B w, c₁ 1 • B w) := hB
  replace hC : ∀ w, T (w, w) = (c₂ 0 • C w, c₂ 1 • C w) := hC
  have hT : ∀ x y, T (x, y) = (c₀ 0 • A x + c₁ 0 • B y, c₀ 1 • A x + c₁ 1 • B y) := by
    intro x y
    have : (x, y) = (x, 0) + (0, y) := by simp
    rw [this, map_add, hA, hB]
    simp [Prod.mk_add_mk]
  have hD := det_ne_zero_aux T c₀ c₁ A B hc₀ hT
  obtain ⟨μ₀, μ₁, e0, e1⟩ := cramer_aux (e := c₂ 0) (f := c₂ 1) hD
  have hAC : ∀ w, A w = μ₀ • C w ∧ B w = μ₁ • C w := by
    intro w
    have hw := hT w w
    rw [hC w] at hw
    have hw0 := congrArg Prod.fst hw
    have hw1 := congrArg Prod.snd hw
    simp only at hw0 hw1
    have h0 : c₀ 0 • (A w - μ₀ • C w) + c₁ 0 • (B w - μ₁ • C w) = 0 := by
      have : c₀ 0 • (A w - μ₀ • C w) + c₁ 0 • (B w - μ₁ • C w) =
          (c₀ 0 • A w + c₁ 0 • B w) - (μ₀ * c₀ 0 + μ₁ * c₁ 0) • C w := by module
      rw [this, ← e0, ← hw0]
      simp
    have h1 : c₀ 1 • (A w - μ₀ • C w) + c₁ 1 • (B w - μ₁ • C w) = 0 := by
      have : c₀ 1 • (A w - μ₀ • C w) + c₁ 1 • (B w - μ₁ • C w) =
          (c₀ 1 • A w + c₁ 1 • B w) - (μ₀ * c₀ 1 + μ₁ * c₁ 1) • C w := by module
      rw [this, ← e1, ← hw1]
      simp
    obtain ⟨hu, hv⟩ := indep_aux hD h0 h1
    exact ⟨sub_eq_zero.mp hu, sub_eq_zero.mp hv⟩
  have hμ₀ : μ₀ ≠ 0 := by
    intro h0
    obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
    have : T (w₀, 0) = 0 := by
      rw [hT, (hAC w₀).1, h0]
      simp
    exact hw₀ (congrArg Prod.fst (T.injective (this.trans (map_zero T).symm)))
  have hμ₁ : μ₁ ≠ 0 := by
    intro h0
    obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
    have : T (0, w₀) = 0 := by
      rw [hT, (hAC w₀).2, h0]
      simp
    exact hw₀ (congrArg Prod.snd (T.injective (this.trans (map_zero T).symm)))
  have hBA : ∀ w, B w = (μ₁ / μ₀) • A w := by
    intro w
    obtain ⟨h1, h2⟩ := hAC w
    rw [h2, h1, smul_smul, div_mul_cancel₀ _ hμ₀]
  set κ : K := μ₁ / μ₀ with hκ
  have hκ0 : κ ≠ 0 := div_ne_zero hμ₁ hμ₀
  set h : Matrix (Fin 2) (Fin 2) K := !![c₀ 0, κ * c₁ 0; c₀ 1, κ * c₁ 1] with hh
  have hTA : ∀ p : W × W, T p = tensorAct h (fun w => A w) p := by
    rintro ⟨x, y⟩
    rw [hT, hBA]
    simp [tensorAct, hh, smul_smul, mul_comm]
  have hdet : h.det = κ * (c₀ 0 * c₁ 1 - c₁ 0 * c₀ 1) := by
    rw [hh, Matrix.det_fin_two_of]
    ring
  have hunit : IsUnit h.det := by
    rw [hdet]
    exact (mul_ne_zero hκ0 hD).isUnit
  have hAinj : Function.Injective A := by
    rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
    intro w hw
    have : T (w, 0) = 0 := by
      rw [hT, hw]
      simp
    exact congrArg Prod.fst (T.injective (this.trans (map_zero T).symm))
  have hAsurj : Function.Surjective A := by
    intro v
    obtain ⟨⟨x, y⟩, hxy⟩ := T.surjective (h 0 0 • v, h 1 0 • v)
    refine ⟨x, ?_⟩
    rw [hTA] at hxy
    have e0 := congrArg Prod.fst hxy
    have e1 := congrArg Prod.snd hxy
    simp only [tensorAct] at e0 e1
    have hdet0 : h 0 0 * h 1 1 - h 0 1 * h 1 0 ≠ 0 := by
      rw [← Matrix.det_fin_two]
      exact hunit.ne_zero
    have lhs : (h 0 0 * h 1 1 - h 0 1 * h 1 0) • A x =
        h 1 1 • (h 0 0 • A x + h 0 1 • A y) - h 0 1 • (h 1 0 • A x + h 1 1 • A y) := by module
    have rhs : (h 0 0 * h 1 1 - h 0 1 * h 1 0) • v =
        h 1 1 • (h 0 0 • v) - h 0 1 • (h 1 0 • v) := by module
    have hfin : (h 0 0 * h 1 1 - h 0 1 * h 1 0) • A x = (h 0 0 * h 1 1 - h 0 1 * h 1 0) • v := by
      rw [lhs, rhs, e0, e1]
    exact smul_right_injective W hdet0 hfin
  refine ⟨h, LinearEquiv.ofBijective A ⟨hAinj, hAsurj⟩, hunit, fun p => ?_⟩
  rw [hTA]
  rfl

private theorem slice_of_conj [Nontrivial W] (T : (W × W) ≃ₗ[K] (W × W))
    (t : Matrix (Fin 2) (Fin 2) K)
    (hT : ∃ t' : Matrix (Fin 2) (Fin 2) K, ∀ p,
      T (tensorAct t (fun w => w) p) = tensorAct t' (fun w => w) (T p))
    (hnot : ∃ p₀ : W × W, tensorAct t (fun w => w) p₀ ≠ p₀) :
    ∃ c : Fin 2 → K, ∀ p : W × W, tensorAct t (fun w => w) p = p →
      ∃ w : W, T p = (c 0 • w, c 1 • w) := by
  obtain ⟨t', ht'⟩ := hT
  have hne : t' ≠ 1 := by
    rintro rfl
    obtain ⟨p₀, hp₀⟩ := hnot
    apply hp₀
    apply T.injective
    rw [ht' p₀]
    simp [tensorAct]
  obtain ⟨c, hc⟩ := fixed_tensorAct_subset (W := W) t' hne
  refine ⟨c, fun p hp => hc (T p) ?_⟩
  rw [← ht' p, hp]

theorem normalizer_slice [Nontrivial W] (T : (W × W) ≃ₗ[K] (W × W))
    (hT : ∀ g : Matrix (Fin 2) (Fin 2) K, g.det = 1 → ∃ g' : Matrix (Fin 2) (Fin 2) K,
      g'.det = 1 ∧ ∀ p, T (tensorAct g (fun w => w) p) = tensorAct g' (fun w => w) (T p)) :
    ∃ (h : Matrix (Fin 2) (Fin 2) K) (o : W ≃ₗ[K] W), IsUnit h.det ∧
      ∀ p, T p = tensorAct h (fun w => o w) p := by
  obtain ⟨w₀, hw₀⟩ := exists_ne (0 : W)
  have sub : ∀ t : Matrix (Fin 2) (Fin 2) K, t.det = 1 →
      (∃ p₀ : W × W, tensorAct t (fun w => w) p₀ ≠ p₀) →
      ∃ c : Fin 2 → K, ∀ p : W × W, tensorAct t (fun w => w) p = p →
        ∃ w : W, T p = (c 0 • w, c 1 • w) := by
    intro t hdet hnot
    obtain ⟨t', -, ht'⟩ := hT t hdet
    exact slice_of_conj T t ⟨t', ht'⟩ hnot
  obtain ⟨c₀, hc₀⟩ := sub !![1, 1; 0, 1] (by simp [Matrix.det_fin_two_of])
    ⟨(0, w₀), by simp [tensorAct, hw₀]⟩
  obtain ⟨c₁, hc₁⟩ := sub !![1, 0; 1, 1] (by simp [Matrix.det_fin_two_of])
    ⟨(w₀, 0), by simp [tensorAct, hw₀]⟩
  obtain ⟨c₂, hc₂⟩ := sub !![2, -1; 1, 0] (by simp [Matrix.det_fin_two_of])
    ⟨(w₀, 0), by simp [tensorAct, hw₀]⟩
  refine slices_eq_tensorAct T ⟨c₀, fun w => hc₀ (w, 0) ?_⟩ ⟨c₁, fun w => hc₁ (0, w) ?_⟩
    ⟨c₂, fun w => hc₂ (w, w) ?_⟩
  · simp [tensorAct]
  · simp [tensorAct]
  · simp [tensorAct]
    module

end Normalizer

end CFSG.RankThree.GF2n.Smith81.OrthTN
