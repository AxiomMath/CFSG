module

public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSubspaceIndex

public noncomputable section

namespace CFSG.Monster.B.TwoA.Sp8

open Module Submodule CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag
  CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open LinearMap (BilinForm)

section Transport

variable {K V V' : Type*} [Field K] [AddCommGroup V] [Module K V] [AddCommGroup V']
  [Module K V']

theorem isTotallyIsotropic_map_isometryEquiv {B : BilinForm K V} {B' : BilinForm K V'}
    (φ : B.IsometryEquiv B') {W : Submodule K V} (hW : IsTotallyIsotropic B W) :
    IsTotallyIsotropic B' (W.map (φ.toLinearEquiv : V →ₗ[K] V')) := by
  rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
  exact (φ.map_app y x).trans (hW x hx y hy)

@[expose] def isoSubEquivOf {B : BilinForm K V} {B' : BilinForm K V'} (φ : B.IsometryEquiv B')
    (P : ℕ → Prop) : {W : Submodule K V // IsTotallyIsotropic B W ∧ P (finrank K W)} ≃
      {W : Submodule K V' // IsTotallyIsotropic B' W ∧ P (finrank K W)} where
  toFun W := ⟨W.1.map (φ.toLinearEquiv : V →ₗ[K] V'),
    isTotallyIsotropic_map_isometryEquiv φ W.2.1,
    (LinearEquiv.finrank_map_eq φ.toLinearEquiv W.1).symm ▸ W.2.2⟩
  invFun W := ⟨W.1.map (φ.symm.toLinearEquiv : V' →ₗ[K] V),
    isTotallyIsotropic_map_isometryEquiv φ.symm W.2.1,
    (LinearEquiv.finrank_map_eq φ.symm.toLinearEquiv W.1).symm ▸ W.2.2⟩
  left_inv W := Subtype.ext (by
    show (W.1.map (φ.toLinearEquiv : V →ₗ[K] V')).map (φ.toLinearEquiv.symm : V' →ₗ[K] V) = W.1
    rw [← Submodule.map_comp, LinearEquiv.symm_comp, Submodule.map_id])
  right_inv W := Subtype.ext (by
    show (W.1.map (φ.toLinearEquiv.symm : V' →ₗ[K] V)).map (φ.toLinearEquiv : V →ₗ[K] V') = W.1
    rw [← Submodule.map_comp, LinearEquiv.comp_symm, Submodule.map_id])

theorem coe_isoSubEquivOf {B : BilinForm K V} {B' : BilinForm K V'} (φ : B.IsometryEquiv B')
    (P : ℕ → Prop) (W : {W : Submodule K V // IsTotallyIsotropic B W ∧ P (finrank K W)}) :
    (isoSubEquivOf φ P W : Submodule K V') = W.1.map (φ.toLinearEquiv : V →ₗ[K] V') := rfl

end Transport

theorem natCard_isoSub {K V : Type} [Field K] [AddCommGroup V] [Module K V] [Finite K]
    [FiniteDimensional K V] {r : ℕ} {B : BilinForm K V} (hB : B.IsAlt) (hnd : B.Nondegenerate)
    (hV : finrank K V = 2 * r) {k : ℕ} (hk : k ≤ r) :
    (Nat.card {W : Submodule K V // IsTotallyIsotropic B W ∧ finrank K W = k} : ℚ) =
      isoGaussian r k (Nat.card K) := by
  obtain ⟨φ⟩ := CFSG.ComponentClassification.CatalogueBAlternatingIsometry.exists_form_isometry
    B (pairedSympForm K r) hB hnd pairedSympForm_isAlt
    SymplecticFlag.pairedSympForm_nondegenerate (hV.trans finrank_standard.symm)
  rw [Nat.card_congr (isoSubEquivOf φ (· = k))]
  exact card_isoSubspaces rfl hk

theorem isoGaussian_four_two :
    isoGaussian 4 1 2 = 255 ∧ isoGaussian 4 2 2 = 5355 ∧ isoGaussian 4 3 2 = 11475 ∧
      isoGaussian 4 4 2 = 2295 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
  · simp [isoGaussian, Finset.prod_range_succ]
    norm_num

end CFSG.Monster.B.TwoA.Sp8
