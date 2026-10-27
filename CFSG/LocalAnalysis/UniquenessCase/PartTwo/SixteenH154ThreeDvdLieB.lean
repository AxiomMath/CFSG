module

public import CFSG.LocalAnalysis.AGLEmbedding.LeviBlockOrthMinusPlane
public import CFSG.ClassicalGroups.Orthogonal.Matrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.ClassicalGroups.Orthogonal
open CFSG.LieType.Universal.Spin CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail

private theorem s16h_quadTail_zero_apply {K : Type} [Field K] {b c : K}
    (v : (Fin 0 ⊕ Fin 0 → K) × (Fin 2 → K)) :
    quadTail 0 (minusTailForm K b c) v = minusTailForm K b c v.2 := by
  rw [quadTail_apply, quadPlus_apply]
  simp

private noncomputable def s16h_quadTailZeroIsometry {K : Type} [Field K] {b c : K} :
    (quadTail 0 (minusTailForm K b c)).IsometryEquiv (minusTailForm K b c) :=
  { (LinearEquiv.uniqueProd : ((Fin 0 ⊕ Fin 0 → K) × (Fin 2 → K)) ≃ₗ[K] (Fin 2 → K)) with
    map_app' := fun v => (s16h_quadTail_zero_apply v).symm }

private noncomputable def s16h_quadMinusLeOneIsometry {K : Type} [Field K] {b c : K} {k : ℕ}
    (hk : k ≤ 1) :
    (quadMinus k K b c).IsometryEquiv (minusTailForm K b c) := by
  have hk0 : k - 1 = 0 := Nat.sub_eq_zero_of_le hk
  exact (minusTailIsometry k K b c).symm.trans (hk0.symm ▸ s16h_quadTailZeroIsometry)

private theorem s16h_map_autCongr_orthogonalGroup {K : Type*} [Field K] {V₁ V₂ : Type*}
    [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
    {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} (e : Q₁.IsometryEquiv Q₂) :
    (TauCeti.QuadraticMap.orthogonalGroup Q₁).map
        (LinearEquiv.autCongr e.toLinearEquiv).toMonoidHom =
      TauCeti.QuadraticMap.orthogonalGroup Q₂ := by
  ext g
  constructor
  · rintro ⟨f, hf, rfl⟩
    refine TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun m => ?_
    rw [MulEquiv.coe_toMonoidHom, LinearEquiv.autCongr_apply_apply]
    erw [e.map_app, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hf, ← e.map_app,
      e.apply_symm_apply]
  · intro hg
    refine ⟨(LinearEquiv.autCongr e.toLinearEquiv).symm g,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff.2 fun m => ?_, MulEquiv.apply_symm_apply _ _⟩
    rw [LinearEquiv.autCongr_symm_apply_apply]
    erw [← e.map_app, e.apply_symm_apply, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg,
      e.map_app]

private theorem s16h_commutator_comm_of_isometry {K : Type*} [Field K] {V₁ V₂ : Type*}
    [AddCommGroup V₁] [Module K V₁] [AddCommGroup V₂] [Module K V₂]
    {Q₁ : QuadraticForm K V₁} {Q₂ : QuadraticForm K V₂} (e : Q₁.IsometryEquiv Q₂)
    (h : ∀ a ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q₂,
        TauCeti.QuadraticMap.orthogonalGroup Q₂⁆,
      ∀ b ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q₂,
        TauCeti.QuadraticMap.orthogonalGroup Q₂⁆, a * b = b * a) :
    ∀ a ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q₁,
        TauCeti.QuadraticMap.orthogonalGroup Q₁⁆,
      ∀ b ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q₁,
        TauCeti.QuadraticMap.orthogonalGroup Q₁⁆, a * b = b * a := by
  intro a ha b hb
  have hmap : ∀ x ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup Q₁,
      TauCeti.QuadraticMap.orthogonalGroup Q₁⁆,
      (LinearEquiv.autCongr e.toLinearEquiv) x ∈
        ⁅TauCeti.QuadraticMap.orthogonalGroup Q₂,
          TauCeti.QuadraticMap.orthogonalGroup Q₂⁆ := by
    intro x hx
    have hx' : (LinearEquiv.autCongr e.toLinearEquiv) x ∈
        (⁅TauCeti.QuadraticMap.orthogonalGroup Q₁,
          TauCeti.QuadraticMap.orthogonalGroup Q₁⁆).map
          (LinearEquiv.autCongr e.toLinearEquiv).toMonoidHom :=
      Subgroup.mem_map_of_mem (LinearEquiv.autCongr e.toLinearEquiv).toMonoidHom hx
    rwa [Subgroup.map_commutator, s16h_map_autCongr_orthogonalGroup e] at hx'
  exact (LinearEquiv.autCongr e.toLinearEquiv).injective (by
    rw [map_mul, map_mul]
    exact h _ (hmap a ha) _ (hmap b hb))

private theorem s16h_commutator_quadMinus_comm_of_le_one {K : Type} [Field K] [Finite K]
    [CharP K 2] {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : ℕ} (hk : k ≤ 1) :
    ∀ x ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus k K b c),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus k K b c)⁆,
      ∀ y ∈ ⁅TauCeti.QuadraticMap.orthogonalGroup (quadMinus k K b c),
        TauCeti.QuadraticMap.orthogonalGroup (quadMinus k K b c)⁆, x * y = y * x :=
  s16h_commutator_comm_of_isometry (s16h_quadMinusLeOneIsometry hk)
    (fun a ha b hb =>
      CFSG.AGLEmbedding.LeviBlock.commute_of_mem_commutator_minusTailForm (g := a) (h := b) hirr
        ha hb)

theorem s16h_comm_statedOmega_quadMinus_of_le_one {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {k : ℕ} (hk : k ≤ 1) :
    ∀ x ∈ StatedOmega (StatedQuadMinus k K b c),
      ∀ y ∈ StatedOmega (StatedQuadMinus k K b c), x * y = y * x := by
  intro x hx y hy
  rw [statedOmega_eq_comap (coe_quadMinus k K b c), Subgroup.mem_comap] at hx hy
  have h := s16h_commutator_quadMinus_comm_of_le_one hirr hk _ hx _ hy
  exact (toLinEquiv _ K).injective (by
    rw [map_mul, map_mul]
    exact h)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
