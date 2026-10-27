module

public import CFSG.RankThree.GF2n.Stroth80.Hom24Minus
public import CFSG.RankThree.GF2n.Stroth80.Sec5OmegaFacts

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin QuadraticMap
open scoped Matrix

theorem sec7_invariant_form_scalar {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (β : LinearMap.BilinForm K (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K))
    (hinv : ∀ A : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K,
      A ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 2 K b c) →
      ∀ x y, β ((A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
        (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ x)
        ((A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
        (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ y) = β x y) :
    ∃ κ : K, ∀ x y, β x y = κ * QuadraticMap.polar (quadMinus 2 K b c) x y := by
  have hB : (polarBilin (quadMinus 2 K b c)).Nondegenerate :=
    nondegenerate_polarBilin_quadMinus_of_finite 2 K hirr
  obtain ⟨T, hT⟩ : ∃ T : (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K) →ₗ[K]
      (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K),
      ∀ x y, polarBilin (quadMinus 2 K b c) (T x) y = β x y :=
    ⟨(LinearMap.BilinForm.toDual (polarBilin (quadMinus 2 K b c)) hB).symm.toLinearMap.comp β,
      fun x y =>
      LinearMap.BilinForm.apply_toDual_symm_apply (hB := hB) (β x) y⟩
  have E := ElemMatrixIso.minus (K := K) (m := 2) (b := b) (c := c) le_rfl hirr
  have hpres : ∀ A : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K,
      A ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 2 K b c) →
      ∀ x y, polar (quadMinus 2 K b c)
        ((A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
          (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ x)
        ((A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
          (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ y) =
        polar (quadMinus 2 K b c) x y :=
    fun A hA x y => E.polar_mulVec hA x y
  have hsurj : ∀ (A : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K)
      (w : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K),
      ∃ y : Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2 → K,
        (A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
          (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ y = w := by
    intro A w
    refine ⟨((A⁻¹ : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) :
      Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
        (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ w, ?_⟩
    rw [Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mulVec]
  have hcomm : ∀ A : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K,
      A ∈ CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 2 K b c) →
      ∀ x, T ((A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
          (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ x) =
        (A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
          (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ T x := by
    intro A hA x
    have hz : ∀ w, polarBilin (quadMinus 2 K b c)
        (T ((A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
          (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ x) -
          (A : Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2)
          (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ T x) w = 0 := by
      intro w
      obtain ⟨y, rfl⟩ := hsurj A w
      rw [map_sub, LinearMap.sub_apply, hT, hinv A hA x y, polarBilin_apply_apply,
        hpres A hA, ← polarBilin_apply_apply, hT, sub_self]
    exact sub_eq_zero.mp (hB.1 _ hz)
  obtain ⟨κ, hκ⟩ := stroth_2_4_omegaMinus K (m := 2) le_rfl hirr T hcomm
  refine ⟨κ, fun x y => ?_⟩
  rw [← hT x y, hκ x, map_smul, LinearMap.smul_apply, smul_eq_mul, polarBilin_apply_apply]

end CFSG.RankThree.GF2n.Stroth80
