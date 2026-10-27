module

public import CFSG.LocalAnalysis.WeakClosure81.W183PglGrp

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Matrix

abbrev W183PglVec : Type := Multiplicative (Fin 3 → ZMod 2)

section Module

variable {I : Type} [CommGroup I]

private theorem w183Pgl_exists_axis_vec :
    ∀ v : Fin 3 → ZMod 2, v ≠ 0 → ∃ f : Fin 3 → ZMod 2, f ≠ 0 ∧ f ⬝ᵥ v = 0 := by
  decide +kernel

private theorem w183Pgl_exists_dual_one :
    ∀ f : Fin 3 → ZMod 2, f ≠ 0 → ∃ w : Fin 3 → ZMod 2, f ⬝ᵥ w = 1 := by
  decide +kernel

private theorem w183Pgl_cross_ne_zero :
    ∀ v w : Fin 3 → ZMod 2, v ≠ 0 → w ≠ 0 → v ≠ w →
      (![v 1 * w 2 - v 2 * w 1, v 2 * w 0 - v 0 * w 2, v 0 * w 1 - v 1 * w 0] :
        Fin 3 → ZMod 2) ≠ 0 := by
  decide +kernel

private theorem w183Pgl_cross_dot :
    ∀ v w : Fin 3 → ZMod 2,
      (![v 1 * w 2 - v 2 * w 1, v 2 * w 0 - v 0 * w 2, v 0 * w 1 - v 1 * w 0] :
        Fin 3 → ZMod 2) ⬝ᵥ v = 0 ∧
      (![v 1 * w 2 - v 2 * w 1, v 2 * w 0 - v 0 * w 2, v 0 * w 1 - v 1 * w 0] :
        Fin 3 → ZMod 2) ⬝ᵥ w = 0 := by
  decide +kernel

private theorem w183Pgl_exists_common_axis (v w : Fin 3 → ZMod 2) (hv : v ≠ 0) (hw : w ≠ 0)
    (hvw : v ≠ w) : ∃ f : Fin 3 → ZMod 2, f ≠ 0 ∧ f ⬝ᵥ v = 0 ∧ f ⬝ᵥ w = 0 :=
  ⟨_, w183Pgl_cross_ne_zero v w hv hw hvw, (w183Pgl_cross_dot v w).1, (w183Pgl_cross_dot v w).2⟩

private theorem w183Pgl_add_ne_zero : ∀ v w : Fin 3 → ZMod 2, v ≠ w → v + w ≠ 0 := by
  decide +kernel

private theorem w183Pgl_add_cancel : ∀ u u' : Fin 3 → ZMod 2, u' + (u + u') = u := by
  decide +kernel

set_option synthInstance.maxSize 4096 in
private theorem w183Pgl_two_func_vec : ∀ f₁ f₂ : Fin 3 → ZMod 2, f₁ ≠ 0 → f₂ ≠ 0 → f₁ ≠ f₂ →
    (∃ w : Fin 3 → ZMod 2, f₁ ⬝ᵥ w = 1 ∧ f₂ ⬝ᵥ w = 0) ∧
    (∃ w : Fin 3 → ZMod 2, f₁ ⬝ᵥ w = 0 ∧ f₂ ⬝ᵥ w = 1) := by
  decide +kernel

@[expose] def W183PglFixed (σ : GL (Fin 3) (ZMod 2) →* MulAut I) : Subgroup I where
  carrier := {i | ∀ g, σ g i = i}
  mul_mem' := fun {a b} ha hb g => by rw [map_mul, ha g, hb g]
  one_mem' := fun g => map_one _
  inv_mem' := fun {a} ha g => by rw [map_inv, ha g]

@[expose] def W183PglQuad (σ : GL (Fin 3) (ZMod 2) →* MulAut I) (x y : GL (Fin 3) (ZMod 2)) :
    Prop :=
  ∀ a b : GL (Fin 3) (ZMod 2), (a = x ∨ a = y ∨ a = x * y) → (b = x ∨ b = y ∨ b = x * y) →
    ∀ i : I, σ b (σ a i * i⁻¹) = σ a i * i⁻¹

theorem w183Pgl_quad_comp_tau {σ : GL (Fin 3) (ZMod 2) →* MulAut I} {x y : GL (Fin 3) (ZMod 2)}
    (h : W183PglQuad σ (w183PglTau x) (w183PglTau y)) :
    W183PglQuad (σ.comp w183PglTau.toMonoidHom) x y := by
  intro a b ha hb i
  have key : ∀ c : GL (Fin 3) (ZMod 2), (c = x ∨ c = y ∨ c = x * y) →
      (w183PglTau c = w183PglTau x ∨ w183PglTau c = w183PglTau y ∨
        w183PglTau c = w183PglTau x * w183PglTau y) := by
    rintro c (rfl | rfl | rfl)
    · exact Or.inl rfl
    · exact Or.inr (Or.inl rfl)
    · exact Or.inr (Or.inr (map_mul _ _ _))
  exact h _ _ (key a ha) (key b hb) i

theorem w183Pgl_axis_trivial (σ : GL (Fin 3) (ZMod 2) →* MulAut I)
    (π : I →* W183PglVec) (hπ : Function.Surjective π)
    (hπσ : ∀ (g : GL (Fin 3) (ZMod 2)) (i : I), Multiplicative.toAdd (π (σ g i)) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd (π i))
    (hker : ∀ i : I, π i = 1 → ∀ g, σ g i = i) {x y : GL (Fin 3) (ZMod 2)}
    {f u u' : Fin 3 → ZMod 2} (hf : f ≠ 0) (hu : u ≠ 0) (hu' : u' ≠ 0) (huu' : u ≠ u')
    (hfu : f ⬝ᵥ u = 0) (hfu' : f ⬝ᵥ u' = 0)
    (hx : (x : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 + vecMulVec u f)
    (hy : (y : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 + vecMulVec u' f) (hq : W183PglQuad σ x y) :
    ∀ i : I, f ⬝ᵥ Multiplicative.toAdd (π i) = 0 → σ x i = i := by
  obtain ⟨w₀, hw₀⟩ := w183Pgl_exists_dual_one f hf
  obtain ⟨x₀, hx₀⟩ := hπ (Multiplicative.ofAdd w₀)
  have hfx₀ : f ⬝ᵥ Multiplicative.toAdd (π x₀) = 1 := by
    rw [hx₀]
    exact hw₀
  have hxy : ((x * y : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
      1 + vecMulVec (u + u') f := by
    rw [Units.val_mul, hx, hy, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, Matrix.vecMulVec_mul_vecMulVec, hfu', zero_smul]
    ext a b
    simp [vecMulVec_apply, add_mul]
    ring
  have hπy : π (σ y x₀ * x₀⁻¹) = Multiplicative.ofAdd u' := by
    rw [map_mul, map_inv]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, hπσ, hy, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.vecMulVec_mulVec, hfx₀]
    simp
  have hπxy : π (σ (x * y) x₀ * x₀⁻¹) = Multiplicative.ofAdd (u + u') := by
    rw [map_mul, map_inv]
    apply Multiplicative.toAdd.injective
    rw [toAdd_mul, toAdd_inv, hπσ, hxy, Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.vecMulVec_mulVec, hfx₀]
    simp
  have hq1 : σ x (σ y x₀ * x₀⁻¹) = σ y x₀ * x₀⁻¹ :=
    hq y x (Or.inr (Or.inl rfl)) (Or.inl rfl) x₀
  have hq2 : σ x (σ (x * y) x₀ * x₀⁻¹) = σ (x * y) x₀ * x₀⁻¹ :=
    hq (x * y) x (Or.inr (Or.inr rfl)) (Or.inl rfl) x₀
  have key : ∀ j i : I, σ x j = j → π i = π j → σ x i = i := by
    intro j i hj hij
    have hk : π (i * j⁻¹) = 1 := by rw [map_mul, map_inv, hij, mul_inv_cancel]
    have h := hker _ hk x
    rw [map_mul, map_inv, hj] at h
    exact mul_right_cancel h
  intro i hi
  rcases w183Pgl_ker_span hf hu hu' huu' hfu hfu' hi with h0 | h1 | h2 | h3
  · refine key 1 i (map_one _) ?_
    rw [map_one]
    apply Multiplicative.toAdd.injective
    simpa using h0
  · refine key ((σ y x₀ * x₀⁻¹) * (σ (x * y) x₀ * x₀⁻¹)) i (by rw [map_mul, hq1, hq2]) ?_
    rw [map_mul, hπy, hπxy]
    apply Multiplicative.toAdd.injective
    rw [h1]
    simpa using (w183Pgl_add_cancel u u').symm
  · refine key (σ y x₀ * x₀⁻¹) i hq1 ?_
    rw [hπy]
    apply Multiplicative.toAdd.injective
    simpa using h2
  · refine key (σ (x * y) x₀ * x₀⁻¹) i hq2 ?_
    rw [hπxy]
    apply Multiplicative.toAdd.injective
    simpa using h3

theorem w183Pgl_all_trivial (σ : GL (Fin 3) (ZMod 2) →* MulAut I)
    (π : I →* W183PglVec) (hπ : Function.Surjective π)
    (hπσ : ∀ (g : GL (Fin 3) (ZMod 2)) (i : I), Multiplicative.toAdd (π (σ g i)) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd (π i))
    (hker : ∀ i : I, π i = 1 → ∀ g, σ g i = i) {x y : GL (Fin 3) (ZMod 2)}
    (hxy : W183PglAxis x y) (hq : W183PglQuad σ x y) :
    ∀ (f u : Fin 3 → ZMod 2) (t : GL (Fin 3) (ZMod 2)), f ≠ 0 → u ≠ 0 → f ⬝ᵥ u = 0 →
      (t : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 + vecMulVec u f →
        ∀ i : I, f ⬝ᵥ Multiplicative.toAdd (π i) = 0 → σ t i = i := by
  obtain ⟨f₀, u₀, u₀', hf₀, hu₀, hu₀', hu₀u, hfu₀, hfu₀', hx, hy⟩ := hxy
  intro f u t hf hu hfu ht i hi
  have hax := w183Pgl_axis_trivial σ π hπ hπσ hker hf₀ hu₀ hu₀' hu₀u hfu₀ hfu₀' hx hy hq
  obtain ⟨g, hg1, hg2⟩ := w183Pgl_flag_transitive hu₀ hf₀ hfu₀ hu hf hfu
  have htx : t = g * x * g⁻¹ := by
    apply Units.ext
    rw [ht, Units.val_mul, Units.val_mul, hx, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one,
      Units.mul_inv, Matrix.mul_vecMulVec, Matrix.vecMulVec_mul, hg1, hg2]
  have h1 : f₀ ⬝ᵥ Multiplicative.toAdd (π (σ g⁻¹ i)) = 0 := by
    rw [hπσ, Matrix.dotProduct_mulVec, hg2]
    exact hi
  have h2 := hax (σ g⁻¹ i) h1
  rw [htx, map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, h2, ← MulAut.mul_apply,
    ← map_mul, mul_inv_cancel, map_one]
  rfl

theorem w183Pgl_delta_const (σ : GL (Fin 3) (ZMod 2) →* MulAut I)
    (π : I →* W183PglVec) (hπ : Function.Surjective π)
    (hπσ : ∀ (g : GL (Fin 3) (ZMod 2)) (i : I), Multiplicative.toAdd (π (σ g i)) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd (π i))
    (htriv : ∀ (f u : Fin 3 → ZMod 2) (t : GL (Fin 3) (ZMod 2)), f ≠ 0 → u ≠ 0 → f ⬝ᵥ u = 0 →
      (t : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 + vecMulVec u f →
        ∀ i : I, f ⬝ᵥ Multiplicative.toAdd (π i) = 0 → σ t i = i)
    {f₁ f₂ u : Fin 3 → ZMod 2} {t₁ t₂ : GL (Fin 3) (ZMod 2)} (hf₁ : f₁ ≠ 0) (hf₂ : f₂ ≠ 0)
    (hu : u ≠ 0) (hf₁u : f₁ ⬝ᵥ u = 0) (hf₂u : f₂ ⬝ᵥ u = 0)
    (ht₁ : (t₁ : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 + vecMulVec u f₁)
    (ht₂ : (t₂ : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 + vecMulVec u f₂) {i₁ i₂ : I}
    (h₁ : f₁ ⬝ᵥ Multiplicative.toAdd (π i₁) = 1) (h₂ : f₂ ⬝ᵥ Multiplicative.toAdd (π i₂) = 1) :
    σ t₁ i₁ * i₁⁻¹ = σ t₂ i₂ * i₂⁻¹ := by
  have hB : ∀ (f : Fin 3 → ZMod 2) (t : GL (Fin 3) (ZMod 2)), f ≠ 0 → f ⬝ᵥ u = 0 →
      (t : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 + vecMulVec u f → ∀ i j : I,
        f ⬝ᵥ Multiplicative.toAdd (π i) = 1 → f ⬝ᵥ Multiplicative.toAdd (π j) = 1 →
          σ t i * i⁻¹ = σ t j * j⁻¹ := by
    intro f t hf hfu ht i j hi hj
    have hz : f ⬝ᵥ Multiplicative.toAdd (π (i * j⁻¹)) = 0 := by
      rw [map_mul, map_inv, toAdd_mul, toAdd_inv, dotProduct_add, dotProduct_neg, hi, hj]
      decide
    have h := htriv f u t hf hu hfu ht _ hz
    rw [map_mul, map_inv] at h
    have h' : σ t i = (i * j⁻¹) * σ t j := mul_inv_eq_iff_eq_mul.1 h
    calc σ t i * i⁻¹ = ((i * j⁻¹) * σ t j) * i⁻¹ := by rw [← h']
      _ = σ t j * j⁻¹ := by
        rw [mul_comm (i * j⁻¹ * σ t j) i⁻¹, ← mul_assoc, ← mul_assoc, inv_mul_cancel, one_mul,
          mul_comm]
  by_cases hff : f₁ = f₂
  · subst hff
    have htt : t₁ = t₂ := Units.ext (ht₁.trans ht₂.symm)
    subst htt
    exact hB f₁ t₁ hf₁ hf₁u ht₁ i₁ i₂ h₁ h₂
  ·
    have hf₃ : f₁ + f₂ ≠ 0 := fun h => hff (by
      have : f₁ = -f₂ := eq_neg_of_add_eq_zero_left h
      rw [this]; funext a; exact (CharTwo.neg_eq (f₂ a)))
    have hf₃u : (f₁ + f₂) ⬝ᵥ u = 0 := by rw [add_dotProduct, hf₁u, hf₂u, add_zero]
    have ht₃ : ((t₁ * t₂ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
        1 + vecMulVec u (f₁ + f₂) := by
      rw [Units.val_mul, ht₁, ht₂, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
        Matrix.one_mul, Matrix.mul_one, Matrix.vecMulVec_mul_vecMulVec, hf₁u, zero_smul]
      rw [show vecMulVec u (0 : Fin 3 → ZMod 2) = 0 from by ext a b; simp [vecMulVec_apply]]
      ext a b
      simp [vecMulVec_apply, mul_add]
      ring
    have hP : ∀ i : I, σ (t₁ * t₂) i * i⁻¹ = (σ t₁ i * i⁻¹) * (σ t₂ i * i⁻¹) := by
      intro i
      have hδ : f₁ ⬝ᵥ Multiplicative.toAdd (π (σ t₂ i * i⁻¹)) = 0 := by
        rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hπσ, ht₂, Matrix.add_mulVec,
          Matrix.one_mulVec, Matrix.vecMulVec_mulVec]
        simp [dotProduct_smul, hf₁u]
      have h2 := htriv f₁ u t₁ hf₁ hu hf₁u ht₁ _ hδ
      have e1 : σ t₁ (σ t₂ i) = (σ t₂ i * i⁻¹) * σ t₁ i := by
        calc σ t₁ (σ t₂ i) = σ t₁ ((σ t₂ i * i⁻¹) * i) := by rw [inv_mul_cancel_right]
          _ = σ t₁ (σ t₂ i * i⁻¹) * σ t₁ i := map_mul _ _ _
          _ = (σ t₂ i * i⁻¹) * σ t₁ i := by rw [h2]
      rw [map_mul, MulAut.mul_apply, e1]
      ac_rfl
    obtain ⟨⟨w₀, hw₀1, hw₀2⟩, ⟨w₁, hw₁1, hw₁2⟩⟩ := w183Pgl_two_func_vec f₁ f₂ hf₁ hf₂ hff
    obtain ⟨i₀, hi₀⟩ := hπ (Multiplicative.ofAdd w₀)
    obtain ⟨i₀', hi₀'⟩ := hπ (Multiplicative.ofAdd w₁)
    have hi₀1 : f₁ ⬝ᵥ Multiplicative.toAdd (π i₀) = 1 := by rw [hi₀]; exact hw₀1
    have hi₀2 : f₂ ⬝ᵥ Multiplicative.toAdd (π i₀) = 0 := by rw [hi₀]; exact hw₀2
    have hi₁1 : f₁ ⬝ᵥ Multiplicative.toAdd (π i₀') = 0 := by rw [hi₀']; exact hw₁1
    have hi₁2 : f₂ ⬝ᵥ Multiplicative.toAdd (π i₀') = 1 := by rw [hi₀']; exact hw₁2
    have hd2 : σ t₂ i₀ = i₀ := htriv f₂ u t₂ hf₂ hu hf₂u ht₂ _ hi₀2
    have hd1 : σ t₁ i₀' = i₀' := htriv f₁ u t₁ hf₁ hu hf₁u ht₁ _ hi₁1
    have hA : σ t₁ i₀ * i₀⁻¹ = σ (t₁ * t₂) i₀ * i₀⁻¹ := by
      rw [hP, hd2, mul_inv_cancel, mul_one]
    have hC : σ t₂ i₀' * i₀'⁻¹ = σ (t₁ * t₂) i₀' * i₀'⁻¹ := by
      rw [hP, hd1, mul_inv_cancel, one_mul]
    have h3 := hB (f₁ + f₂) (t₁ * t₂) hf₃ hf₃u ht₃ i₀ i₀'
      (by rw [add_dotProduct, hi₀1, hi₀2, add_zero]) (by rw [add_dotProduct, hi₁1, hi₁2, zero_add])
    calc σ t₁ i₁ * i₁⁻¹ = σ t₁ i₀ * i₀⁻¹ := hB f₁ t₁ hf₁ hf₁u ht₁ i₁ i₀ h₁ hi₀1
      _ = σ t₂ i₀' * i₀'⁻¹ := by rw [hA, hC, h3]
      _ = σ t₂ i₂ * i₂⁻¹ := hB f₂ t₂ hf₂ hf₂u ht₂ i₀' i₂ hi₁2 h₂

theorem w183Pgl_delta_add (σ : GL (Fin 3) (ZMod 2) →* MulAut I) (π : I →* W183PglVec)
    (hπσ : ∀ (g : GL (Fin 3) (ZMod 2)) (i : I), Multiplicative.toAdd (π (σ g i)) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd (π i))
    (htriv : ∀ (f u : Fin 3 → ZMod 2) (t : GL (Fin 3) (ZMod 2)), f ≠ 0 → u ≠ 0 → f ⬝ᵥ u = 0 →
      (t : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 + vecMulVec u f →
        ∀ i : I, f ⬝ᵥ Multiplicative.toAdd (π i) = 0 → σ t i = i)
    {f u u' : Fin 3 → ZMod 2} {t t' t'' : GL (Fin 3) (ZMod 2)} (hf : f ≠ 0) (hu : u ≠ 0)
    (hu' : u' ≠ 0) (huu' : u ≠ u') (hfu : f ⬝ᵥ u = 0) (hfu' : f ⬝ᵥ u' = 0)
    (ht : (t : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 + vecMulVec u f)
    (ht' : (t' : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 + vecMulVec u' f)
    (ht'' : (t'' : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 + vecMulVec (u + u') f) {i : I}
    (hi : f ⬝ᵥ Multiplicative.toAdd (π i) = 1) :
    σ t'' i * i⁻¹ = (σ t i * i⁻¹) * (σ t' i * i⁻¹) := by
  have htt : t'' = t * t' := by
    apply Units.ext
    rw [Units.val_mul, ht, ht', ht'', Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
      Matrix.one_mul, Matrix.mul_one, Matrix.vecMulVec_mul_vecMulVec, hfu', zero_smul]
    rw [show vecMulVec u (0 : Fin 3 → ZMod 2) = 0 from by ext a b; simp [vecMulVec_apply]]
    ext a b
    simp [vecMulVec_apply, add_mul]
    ring
  have hδ : f ⬝ᵥ Multiplicative.toAdd (π (σ t' i * i⁻¹)) = 0 := by
    rw [map_mul, map_inv, toAdd_mul, toAdd_inv, hπσ, ht', Matrix.add_mulVec, Matrix.one_mulVec,
      Matrix.vecMulVec_mulVec, hi]
    simp [hfu']
  have h2 := htriv f u t hf hu hfu ht _ hδ
  have e1 : σ t (σ t' i) = (σ t' i * i⁻¹) * σ t i := by
    calc σ t (σ t' i) = σ t ((σ t' i * i⁻¹) * i) := by rw [inv_mul_cancel_right]
      _ = σ t (σ t' i * i⁻¹) * σ t i := map_mul _ _ _
      _ = (σ t' i * i⁻¹) * σ t i := by rw [h2]
  rw [htt, map_mul, MulAut.mul_apply, e1]
  ac_rfl

theorem w183Pgl_exists_section (hI : ∀ x : I, x ^ 2 = 1) (σ : GL (Fin 3) (ZMod 2) →* MulAut I)
    (π : I →* W183PglVec) (hπ : Function.Surjective π)
    (hπσ : ∀ (g : GL (Fin 3) (ZMod 2)) (i : I), Multiplicative.toAdd (π (σ g i)) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd (π i))
    (hker : ∀ i : I, π i = 1 → ∀ g, σ g i = i)
    (htriv : ∀ (f u : Fin 3 → ZMod 2) (t : GL (Fin 3) (ZMod 2)), f ≠ 0 → u ≠ 0 → f ⬝ᵥ u = 0 →
      (t : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 + vecMulVec u f →
        ∀ i : I, f ⬝ᵥ Multiplicative.toAdd (π i) = 0 → σ t i = i) :
    ∃ s : W183PglVec →* I, (∀ v, π (s v) = v) ∧
      ∀ (g : GL (Fin 3) (ZMod 2)) (v : W183PglVec),
        s (Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd v)) =
          σ g (s v) := by
  classical
  have hflag : ∀ v : Fin 3 → ZMod 2, v ≠ 0 → ∃ (f : Fin 3 → ZMod 2) (t : GL (Fin 3) (ZMod 2))
      (i : I), f ≠ 0 ∧ f ⬝ᵥ v = 0 ∧
        (t : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 + vecMulVec v f ∧
          f ⬝ᵥ Multiplicative.toAdd (π i) = 1 := by
    intro v hv
    obtain ⟨f, hf, hfv⟩ := w183Pgl_exists_axis_vec v hv
    obtain ⟨t, ht⟩ := w183Pgl_transvection_exists v f hfv
    obtain ⟨w, hw⟩ := w183Pgl_exists_dual_one f hf
    obtain ⟨i, hi⟩ := hπ (Multiplicative.ofAdd w)
    exact ⟨f, t, i, hf, hfv, ht, by rw [hi]; exact hw⟩
  choose! F T X hF hFv hT hX using hflag
  let m : (Fin 3 → ZMod 2) → I := fun v => if v = 0 then 1 else σ (T v) (X v) * (X v)⁻¹
  have hm0 : m 0 = 1 := by simp [m]
  have hmv : ∀ v : Fin 3 → ZMod 2, v ≠ 0 → m v = σ (T v) (X v) * (X v)⁻¹ := fun v hv => by
    simp [m, hv]
  have hm : ∀ (v f : Fin 3 → ZMod 2) (t : GL (Fin 3) (ZMod 2)) (i : I), v ≠ 0 → f ≠ 0 →
      f ⬝ᵥ v = 0 → (t : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 + vecMulVec v f →
        f ⬝ᵥ Multiplicative.toAdd (π i) = 1 → σ t i * i⁻¹ = m v := by
    intro v f t i hv hf hfv ht hi
    rw [hmv v hv]
    exact w183Pgl_delta_const σ π hπ hπσ htriv hf (hF v hv) hv hfv (hFv v hv) ht (hT v hv) hi
      (hX v hv)
  have hπm : ∀ v : Fin 3 → ZMod 2, π (m v) = Multiplicative.ofAdd v := by
    intro v
    by_cases hv : v = 0
    · rw [hv, hm0, map_one]
      rfl
    · rw [hmv v hv, map_mul, map_inv]
      apply Multiplicative.toAdd.injective
      rw [toAdd_mul, toAdd_inv, hπσ, hT v hv, Matrix.add_mulVec, Matrix.one_mulVec,
        Matrix.vecMulVec_mulVec, hX v hv]
      simp
  have hadd : ∀ v w : Fin 3 → ZMod 2, m (v + w) = m v * m w := by
    intro v w
    by_cases hv : v = 0
    · rw [hv, hm0, zero_add, one_mul]
    by_cases hw : w = 0
    · rw [hw, hm0, add_zero, mul_one]
    by_cases hvw : v = w
    · subst hvw
      have h2 : v + v = 0 := funext fun j => CharTwo.add_self_eq_zero (v j)
      rw [h2, hm0, ← sq]
      exact (hI (m v)).symm
    · obtain ⟨f, hf, hfv, hfw⟩ := w183Pgl_exists_common_axis v w hv hw hvw
      have hfvw : f ⬝ᵥ (v + w) = 0 := by rw [dotProduct_add, hfv, hfw, add_zero]
      obtain ⟨t, ht⟩ := w183Pgl_transvection_exists v f hfv
      obtain ⟨t', ht'⟩ := w183Pgl_transvection_exists w f hfw
      obtain ⟨t'', ht''⟩ := w183Pgl_transvection_exists (v + w) f hfvw
      obtain ⟨w₀, hw₀⟩ := w183Pgl_exists_dual_one f hf
      obtain ⟨i, hi⟩ := hπ (Multiplicative.ofAdd w₀)
      have hfi : f ⬝ᵥ Multiplicative.toAdd (π i) = 1 := by rw [hi]; exact hw₀
      have hvw0 : v + w ≠ 0 := w183Pgl_add_ne_zero v w hvw
      rw [← hm (v + w) f t'' i hvw0 hf hfvw ht'' hfi, ← hm v f t i hv hf hfv ht hfi,
        ← hm w f t' i hw hf hfw ht' hfi]
      exact w183Pgl_delta_add σ π hπσ htriv hf hv hw hvw hfv hfw ht ht' ht'' hfi
  let s : W183PglVec →* I :=
    { toFun := fun v => m (Multiplicative.toAdd v)
      map_one' := by simpa using hm0
      map_mul' := fun a b => by simpa using hadd (Multiplicative.toAdd a) (Multiplicative.toAdd b) }
  refine ⟨s, fun v => ?_, fun g v => ?_⟩
  · have := hπm (Multiplicative.toAdd v)
    simpa [s] using this
  · have hcc : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := Units.mul_inv g
    have hcc' : ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *
        (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 := Units.inv_mul g
    have hconj : ∀ (u f : Fin 3 → ZMod 2) (t : GL (Fin 3) (ZMod 2)),
        (t : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 1 + vecMulVec u f →
          ((g * t * g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) =
            1 + vecMulVec ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ u)
              (f ᵥ* ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) := by
      intro u f t ht
      rw [Units.val_mul, Units.val_mul, ht, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hcc,
        Matrix.mul_vecMulVec, Matrix.vecMulVec_mul]
    have hgi : ∀ w : Fin 3 → ZMod 2, (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w = 0 → w = 0 :=
      fun w hw => by
        have := congrArg (fun z =>
          ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ z) hw
        simpa [Matrix.mulVec_mulVec, hcc'] using this
    have hgl : ∀ f' : Fin 3 → ZMod 2,
        f' ᵥ* ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) = 0 → f' = 0 :=
      fun f' hf' => by
        have := congrArg (fun z => z ᵥ* (g : Matrix (Fin 3) (Fin 3) (ZMod 2))) hf'
        simpa [Matrix.vecMul_vecMul, hcc'] using this
    have hdotg : ∀ f' w : Fin 3 → ZMod 2,
        (f' ᵥ* ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2))) ⬝ᵥ
          ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ w) = f' ⬝ᵥ w := fun f' w => by
      rw [← Matrix.dotProduct_mulVec, Matrix.mulVec_mulVec, hcc', Matrix.one_mulVec]
    change m ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd v) =
      σ g (m (Multiplicative.toAdd v))
    generalize Multiplicative.toAdd v = u
    by_cases hu : u = 0
    · rw [hu, Matrix.mulVec_zero, hm0, map_one]
    · have hgu : (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ u ≠ 0 := fun h => hu (hgi u h)
      have hgf : F u ᵥ* ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)) ≠ 0 :=
        fun h => hF u hu (hgl _ h)
      have key := hm ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ u)
        (F u ᵥ* ((g⁻¹ : GL (Fin 3) (ZMod 2)) : Matrix (Fin 3) (Fin 3) (ZMod 2)))
        (g * T u * g⁻¹) (σ g (X u)) hgu hgf (by rw [hdotg]; exact hFv u hu)
        (hconj u (F u) (T u) (hT u hu)) (by rw [hπσ, hdotg]; exact hX u hu)
      have e1 : σ (g * T u * g⁻¹) (σ g (X u)) = σ g (σ (T u) (X u)) := by
        have h1 : σ g⁻¹ (σ g (X u)) = X u := by
          rw [← MulAut.mul_apply, ← map_mul, inv_mul_cancel, map_one]
          rfl
        rw [map_mul, map_mul, MulAut.mul_apply, MulAut.mul_apply, h1]
      rw [← key, hmv u hu, e1, map_mul, map_inv]

theorem w183Pgl_natural_inj (hI : ∀ x : I, x ^ 2 = 1) (σ : GL (Fin 3) (ZMod 2) →* MulAut I)
    (π : I →* W183PglVec) (hπ : Function.Surjective π)
    (hπσ : ∀ (g : GL (Fin 3) (ZMod 2)) (i : I), Multiplicative.toAdd (π (σ g i)) =
      (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ Multiplicative.toAdd (π i))
    (hker : ∀ i : I, π i = 1 → ∀ g, σ g i = i)
    (hgen : ∀ i : I, i ∈ Subgroup.closure
      {x : I | ∃ (g : GL (Fin 3) (ZMod 2)) (j : I), x = σ g j * j⁻¹})
    {x y : GL (Fin 3) (ZMod 2)} (hxy : W183PglAxis x y) (hq : W183PglQuad σ x y) :
    Function.Injective π := by
  have htriv := w183Pgl_all_trivial σ π hπ hπσ hker hxy hq
  obtain ⟨s, hs1, hs2⟩ := w183Pgl_exists_section hI σ π hπ hπσ hker htriv
  have hS : {x : I | ∃ (g : GL (Fin 3) (ZMod 2)) (j : I), x = σ g j * j⁻¹} ⊆
      (s.range : Set I) := by
    rintro x ⟨g, j, rfl⟩
    set v := π j with hv
    have hc : π ((s v)⁻¹ * j) = 1 := by
      rw [map_mul, map_inv, hs1, hv, inv_mul_cancel]
    have hfix := hker _ hc g
    have e1 : σ g j = σ g (s v) * ((s v)⁻¹ * j) := by
      calc σ g j = σ g (s v * ((s v)⁻¹ * j)) := by rw [mul_inv_cancel_left]
        _ = σ g (s v) * σ g ((s v)⁻¹ * j) := map_mul _ _ _
        _ = σ g (s v) * ((s v)⁻¹ * j) := by rw [hfix]
    refine ⟨Multiplicative.ofAdd ((g : Matrix (Fin 3) (Fin 3) (ZMod 2)) *ᵥ
      Multiplicative.toAdd v) * v⁻¹, ?_⟩
    rw [map_mul, map_inv, hs2, e1]
    group
  have hle : ∀ i : I, i ∈ s.range := fun i =>
    (Subgroup.closure_le s.range).2 hS (hgen i)
  intro i₁ i₂ h
  obtain ⟨v₁, rfl⟩ := hle i₁
  obtain ⟨v₂, rfl⟩ := hle i₂
  rw [hs1, hs1] at h
  rw [h]

end Module

end CFSG.LocalAnalysis.WeakClosure81

end
