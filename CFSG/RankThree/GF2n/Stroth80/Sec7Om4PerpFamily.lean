module

public import CFSG.RankThree.GF2n.Stroth80.Sec7OmegaMinusFourTrans

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap CFSG.Open
open scoped Matrix

theorem sec7_om4_perp_family {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {Γ : Type*} [Group Γ]
    (φ : Γ →* GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)
    (hφ : φ.range = StatedOmega (StatedQuadMinus 2 K b c))
    {𝒢 : Type*} (x : 𝒢 → (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K))
    (H : 𝒢 → AddSubgroup (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K))
    (g₀ : 𝒢) (hx₀ : x g₀ ≠ 0) (hQ₀ : quadMinus 2 K b c (x g₀) = 0)
    (hH₀ : ∀ y, y ∈ H g₀ ↔ polar (quadMinus 2 K b c) (x g₀) y = 0)
    (hscal : ∀ (g : 𝒢) (s : K), s • x g ∈ H g)
    (hcard : ∀ g : 𝒢, Nat.card (H g) = Nat.card K ^ 3)
    (hsame : ∀ (g g' : 𝒢) (s : K), s ≠ 0 → x g' = s • x g → H g' = H g)
    (hact : ∀ (g : 𝒢) (r : Γ), ∃ g' : 𝒢,
      x g' = ((φ r : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ x g ∧
      ∀ y, y ∈ H g' ↔ ((((φ r)⁻¹ : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)) :
        Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ y ∈
          H g) :
    ∀ g : 𝒢, x g ≠ 0 → ∀ y, y ∈ H g ↔ polar (quadMinus 2 K b c) (x g) y = 0 := by
  intro g hg
  by_cases hQg : quadMinus 2 K b c (x g) = 0
  · have hcancel : ∀ (M : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)
        (w : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K),
        (M : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ
          (((M⁻¹ : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) :
            Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ
              w) = w := by
      intro M w
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
    obtain ⟨A, hA, hAx⟩ :=
      omegaMinusFourSingularTrans_holds K b c hirr (x g₀) (x g) hx₀ hg hQ₀ hQg
    have hAφ : A ∈ φ.range := by
      rw [hφ]
      exact hA
    obtain ⟨r, rfl⟩ := hAφ
    obtain ⟨g', hg'x, hg'H⟩ := hact g₀ r
    have hHg : H g' = H g := hsame g g' 1 one_ne_zero (by rw [one_smul, hg'x, hAx])
    have E := ElemMatrixIso.minus (K := K) (m := 2) (b := b) (c := c) le_rfl hirr
    intro y
    have hpres := E.polar_mulVec hA (x g₀)
      ((((φ r)⁻¹ : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ y)
    rw [hcancel] at hpres
    rw [← hHg, hg'H, hH₀, ← hAx, ← hpres]
  · have hcancel' : ∀ (M : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)
        (w : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K),
        ((M⁻¹ : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ
          ((M : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)
            *ᵥ w) = w := by
      intro M w
      rw [Matrix.mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mulVec]
    have hinv : ∀ r : Γ,
        (∃ s : K, ((φ r : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ
            x g = s • x g) →
        ∀ y ∈ H g, ((φ r : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ
            y ∈ H g := by
      rintro r ⟨s, hs⟩ y hy
      have hs0 : s ≠ 0 := by
        rintro rfl
        apply hg
        rw [← hcancel' (φ r) (x g), hs, zero_smul, Matrix.mulVec_zero]
      obtain ⟨g', hg'x, hg'H⟩ := hact g r
      have hHg : H g' = H g := hsame g g' s hs0 (hg'x.trans hs)
      have hmem := hg'H (((φ r : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) :
        Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ y)
      rw [hcancel'] at hmem
      have hmem2 := hmem.mpr hy
      rw [hHg] at hmem2
      exact hmem2
    exact sec7_om4_nonsingular_stab_of_hom hirr hQg φ hφ (H g) (hscal g) (hcard g) hinv

end CFSG.RankThree.GF2n.Stroth80
