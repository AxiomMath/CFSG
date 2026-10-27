module

public import CFSG.RankThree.GF2n.Smith81.S81VGeomD2a
public import CFSG.RankThree.GF2n.Smith81.S81VGeomD3a

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {F : Type} [Field F] {σ : F ≃+* F} {a b : Fin 3 → Fin 6 → F} {θ : F}

@[expose] def v3 (a b : Fin 3 → Fin 6 → F) (θ : F) : Fin 6 → F := a 0 + θ • b 0 + a 1 + θ • b 1

@[expose] def rr (a b : Fin 3 → Fin 6 → F) (θ : F) : Fin 6 → F := a 0 + θ • b 0 + a 2 + θ • b 2

@[expose] def X3 (σ : F ≃+* F) (a b : Fin 3 → Fin 6 → F) (θ : F) :
    Set (Submodule F (Fin 6 → F)) :=
  {Submodule.span F {b 1, rr a b θ, b 0 + b 2}, Submodule.span F {b 1, rr a b θ, a 0 + σ θ • b 2}}

@[expose] def genSet (σ : F ≃+* F) (a b : Fin 3 → Fin 6 → F) (θ : F) :
    Set (Submodule F (Fin 6 → F)) :=
  recipeSet σ (a 0) (a 1) (b 1) (a 2) (b 2) θ ∪ recipeSet σ (b 0) (a 1) (b 1) (a 2) (b 2) θ ∪
    recipeSet σ (v3 a b θ) (a 2) (b 2) (a 0 + a 1) (b 1 + (σ θ)⁻¹ • a 0) θ ∪ X3 σ a b θ

private theorem frameBA (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (i j : Fin 3) :
    herm σ (b i) (a j) = if i = j then 1 else 0 := by
  rw [herm_conj σ hσ (a j) (b i), hf.ab j i]
  by_cases h : i = j
  · subst h
    simp
  · simp [h, Ne.symm h]

private theorem six_finite_ncard {α : Type*} (x1 x2 x3 x4 x5 x6 : α) :
    ({x1, x2, x3, x4, x5, x6} : Set α).Finite ∧ ({x1, x2, x3, x4, x5, x6} : Set α).ncard ≤ 6 := by
  refine ⟨Set.toFinite _, ?_⟩
  have h5 := Set.ncard_insert_le x5 ({x6} : Set α)
  have h4 := Set.ncard_insert_le x4 ({x5, x6} : Set α)
  have h3 := Set.ncard_insert_le x3 ({x4, x5, x6} : Set α)
  have h2 := Set.ncard_insert_le x2 ({x3, x4, x5, x6} : Set α)
  have h1 := Set.ncard_insert_le x1 ({x2, x3, x4, x5, x6} : Set α)
  have h6 := Set.ncard_singleton x6
  omega

private theorem union_finite_ncard {α : Type*} {s t : Set α} {m n : ℕ}
    (hs : s.Finite ∧ s.ncard ≤ m) (ht : t.Finite ∧ t.ncard ≤ n) :
    (s ∪ t).Finite ∧ (s ∪ t).ncard ≤ m + n :=
  ⟨hs.1.union ht.1, (Set.ncard_union_le s t).trans (Nat.add_le_add hs.2 ht.2)⟩

private theorem recipeSet_finite_ncard (σ : F ≃+* F) (p u₁ w₁ u₂ w₂ : Fin 6 → F) (θ : F) :
    (recipeSet σ p u₁ w₁ u₂ w₂ θ).Finite ∧ (recipeSet σ p u₁ w₁ u₂ w₂ θ).ncard ≤ 6 := by
  unfold recipeSet
  exact six_finite_ncard _ _ _ _ _ _

private theorem X3_finite_ncard (σ : F ≃+* F) (a b : Fin 3 → Fin 6 → F) (θ : F) :
    (X3 σ a b θ).Finite ∧ (X3 σ a b θ).ncard ≤ 2 := by
  unfold X3
  refine ⟨Set.toFinite _, ?_⟩
  have h := Set.ncard_insert_le (Submodule.span F {b 1, rr a b θ, b 0 + b 2})
    ({Submodule.span F {b 1, rr a b θ, a 0 + σ θ • b 2}} : Set (Submodule F (Fin 6 → F)))
  rw [Set.ncard_singleton] at h
  omega

theorem recipe0 [CharP F 2] (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (hθ : θ + σ θ ≠ 0) :
    Recipe σ (a 0) (a 1) (b 1) (a 2) (b 2) θ where
  p0 := by
    intro h0
    have h := hf.ab 0 0
    simp [h0] at h
  pp := hf.aa 0 0
  pu₁ := hf.aa 0 1
  pw₁ := by simp [hf.ab]
  pu₂ := hf.aa 0 2
  pw₂ := by simp [hf.ab]
  u₁u₁ := hf.aa 1 1
  w₁w₁ := hf.bb 1 1
  u₂u₂ := hf.aa 2 2
  w₂w₂ := hf.bb 2 2
  u₁u₂ := hf.aa 1 2
  u₁w₂ := by simp [hf.ab]
  w₁u₂ := by simp [frameBA hσ hf]
  w₁w₂ := hf.bb 1 2
  u₁w₁ := by simp [hf.ab]
  u₂w₂ := by simp [hf.ab]
  θ0 := hθ

theorem recipe1 [CharP F 2] (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (hθ : θ + σ θ ≠ 0) :
    Recipe σ (b 0) (a 1) (b 1) (a 2) (b 2) θ where
  p0 := by
    intro h0
    have h := frameBA hσ hf 0 0
    simp [h0] at h
  pp := hf.bb 0 0
  pu₁ := by simp [frameBA hσ hf]
  pw₁ := hf.bb 0 1
  pu₂ := by simp [frameBA hσ hf]
  pw₂ := hf.bb 0 2
  u₁u₁ := hf.aa 1 1
  w₁w₁ := hf.bb 1 1
  u₂u₂ := hf.aa 2 2
  w₂w₂ := hf.bb 2 2
  u₁u₂ := hf.aa 1 2
  u₁w₂ := by simp [hf.ab]
  w₁u₂ := by simp [frameBA hσ hf]
  w₁w₂ := hf.bb 1 2
  u₁w₁ := by simp [hf.ab]
  u₂w₂ := by simp [hf.ab]
  θ0 := hθ

theorem recipe2 [CharP F 2] (hσ : ∀ c, σ (σ c) = c) (hf : Frame σ a b) (hθ : θ + σ θ ≠ 0) :
    Recipe σ (v3 a b θ) (a 2) (b 2) (a 0 + a 1) (b 1 + (σ θ)⁻¹ • a 0) θ := by
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  have hs : σ θ ≠ 0 := by
    intro h
    have h0 : θ = 0 := by
      have := hσ θ
      rw [h, map_zero] at this
      exact this.symm
    exact hθ (by simp [h, h0])
  have hk : (σ θ)⁻¹ * σ θ = 1 := inv_mul_cancel₀ hs
  have hvB1 : herm σ (v3 a b θ) (b 1) = 1 := by
    unfold v3
    simp [hf.aa, hf.bb, hf.ab, frameBA hσ hf]
  have hvA0 : herm σ (v3 a b θ) (a 0) = σ θ := by
    unfold v3
    simp [hf.aa, hf.bb, hf.ab, frameBA hσ hf]
  have hvA1 : herm σ (v3 a b θ) (a 1) = σ θ := by
    unfold v3
    simp [hf.aa, hf.bb, hf.ab, frameBA hσ hf]
  have hvpp : herm σ (v3 a b θ) (v3 a b θ) = 0 := by
    unfold v3
    simp [hf.aa, hf.bb, hf.ab, frameBA hσ hf]
    linear_combination (θ + σ θ) * two
  have hvu1 : herm σ (v3 a b θ) (a 2) = 0 := by
    unfold v3
    simp [hf.aa, hf.bb, hf.ab, frameBA hσ hf]
  have hvw1 : herm σ (v3 a b θ) (b 2) = 0 := by
    unfold v3
    simp [hf.aa, hf.bb, hf.ab, frameBA hσ hf]
  have hvu2 : herm σ (v3 a b θ) (a 0 + a 1) = 0 := by
    rw [herm_add_right, hvA0, hvA1]
    linear_combination (σ θ) * two
  have hvw2 : herm σ (v3 a b θ) (b 1 + (σ θ)⁻¹ • a 0) = 0 := by
    rw [herm_add_right, herm_smul_right, hvB1, hvA0, hk]
    linear_combination two
  have hp0 : v3 a b θ ≠ 0 := by
    intro h0
    rw [h0, herm_zero_left] at hvB1
    exact zero_ne_one hvB1
  exact
    { p0 := hp0
      pp := hvpp
      pu₁ := hvu1
      pw₁ := hvw1
      pu₂ := hvu2
      pw₂ := hvw2
      u₁u₁ := hf.aa 2 2
      w₁w₁ := hf.bb 2 2
      u₂u₂ := by simp [hf.aa]
      w₂w₂ := by simp [hf.aa, hf.bb, hf.ab, frameBA hσ hf]
      u₁u₂ := by simp [hf.aa]
      u₁w₂ := by simp [hf.aa, hf.ab]
      w₁u₂ := by simp [frameBA hσ hf]
      w₁w₂ := by simp [hf.bb, frameBA hσ hf]
      u₁w₁ := by simp [hf.ab]
      u₂w₂ := by simp [hf.aa, hf.ab]
      θ0 := hθ }

theorem genSet_finite_ncard_le : (genSet σ a b θ).Finite ∧ (genSet σ a b θ).ncard ≤ 20 := by
  unfold genSet
  obtain ⟨h1, h2⟩ := union_finite_ncard (union_finite_ncard (union_finite_ncard
    (recipeSet_finite_ncard σ (a 0) (a 1) (b 1) (a 2) (b 2) θ)
    (recipeSet_finite_ncard σ (b 0) (a 1) (b 1) (a 2) (b 2) θ))
    (recipeSet_finite_ncard σ (v3 a b θ) (a 2) (b 2) (a 0 + a 1) (b 1 + (σ θ)⁻¹ • a 0) θ))
    (X3_finite_ncard σ a b θ)
  exact ⟨h1, by omega⟩

end CFSG.RankThree.GF2n.Smith81.S81V
