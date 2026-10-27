module

public import CFSG.ClassicalGroups.Symplectic.StandardForm
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogQuadraticNormalForms
public import CFSG.Open.StatedDefs
public import CFSG.RankThree.GF2n.Stroth80.Sec310ClDefs
public import TauCeti.LinearAlgebra.BilinearForm.SymplecticBasis
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Basis
public import CFSG.ClassicalGroups.Orthogonal.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

open CFSG.Open CFSG.ClassicalGroups.Symplectic
open Matrix

variable {K : Type} [Field K] [Finite K] [CharP K 2] {W : Type} [AddCommGroup W] [Module K W]
  [FiniteDimensional K W] {R : Type} [Group R]

theorem basis_J_eq_spJ {m : ℕ} : Matrix.J (Fin m) K = spJ m K := by
  ext i j
  rcases i with i | i <;> rcases j with j | j <;>
    simp [Matrix.J, spJ, Matrix.one_apply, CharTwo.neg_eq]

theorem basis_toGL_mulVec_equivFun {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (f : W ≃ₗ[K] W) (w : W) :
    Matrix.mulVec (b.toGL f : Matrix ι ι K) (b.equivFun w) = b.equivFun (f w) := by
  have h1 : (Matrix.GeneralLinearGroup.toLin' b (b.toGL f)).toLinearEquiv w = f w := by
    rw [Module.Basis.toLin'_toGL]
    rfl
  rw [Matrix.GeneralLinearGroup.toLin'_apply] at h1
  apply b.equivFun.symm.injective
  rw [LinearEquiv.symm_apply_apply, Module.Basis.equivFun_symm_apply, ← h1,
    Fintype.linearCombination_apply]
  rfl

theorem basis_equivFun_symm_plus {n : ℕ} (b : Module.Basis (Fin n ⊕ Fin n) K W)
    (v : Fin n ⊕ Fin n → K) :
    b.equivFun.symm v = ∑ i, v (Sum.inl i) • b (Sum.inl i) +
      ∑ i, v (Sum.inr i) • b (Sum.inr i) := by
  rw [Module.Basis.equivFun_symm_apply, Fintype.sum_sum_type]

theorem basis_equivFun_symm_minus {n : ℕ}
    (b : Module.Basis (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K W)
    (v : Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) :
    b.equivFun.symm v = ∑ i, v (Sum.inl i) • b (Sum.inl i) +
      ∑ i, v (Sum.inr (Sum.inl i)) • b (Sum.inr (Sum.inl i)) +
      v (Sum.inr (Sum.inr 0)) • b (Sum.inr (Sum.inr 0)) +
      v (Sum.inr (Sum.inr 1)) • b (Sum.inr (Sum.inr 1)) := by
  rw [Module.Basis.equivFun_symm_apply, Fintype.sum_sum_type, Fintype.sum_sum_type,
    Fin.sum_univ_two]
  abel

theorem exists_basis_range_symp (F : LinearMap.BilinForm K W) (hnd : F.Nondegenerate)
    (halt : F.IsAlt) (ρ : R →* (W ≃ₗ[K] W)) (hr : ρ.range = sympSubgroup F) :
    ∃ (m : ℕ) (b : Module.Basis (Fin m ⊕ Fin m) K W), Module.finrank K W = 2 * m ∧
      (b.toGL.toMonoidHom.comp ρ).range = StatedSp m K := by
  obtain ⟨m, b, hb⟩ := halt.exists_basis_toMatrix_eq_J hnd
  have hG : ∀ u w, F u w = spForm m K (b.equivFun u) (b.equivFun w) := by
    intro u w
    rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec b F u w, hb,
      basis_J_eq_spJ, spForm_apply]
    rfl
  refine ⟨m, b, ?_, ?_⟩
  · rw [Module.finrank_eq_card_basis b, Fintype.card_sum, Fintype.card_fin, two_mul]
  · rw [MonoidHom.range_comp, hr]
    ext A
    obtain ⟨g, rfl⟩ := b.toGL.surjective A
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply, mem_statedSp_iff_forall]
    constructor
    · intro hg x y
      have hg' : ∀ u w, F (g u) (g w) = F u w := hg
      obtain ⟨u, rfl⟩ := b.equivFun.surjective x
      obtain ⟨w, rfl⟩ := b.equivFun.surjective y
      rw [basis_toGL_mulVec_equivFun, basis_toGL_mulVec_equivFun, ← hG, ← hG]
      exact hg' u w
    · intro h
      change ∀ u w, F (g u) (g w) = F u w
      intro u w
      have h' := h (b.equivFun u) (b.equivFun w)
      rw [basis_toGL_mulVec_equivFun, basis_toGL_mulVec_equivFun, ← hG, ← hG] at h'
      exact h'

theorem range_comp_eq_statedOmega {ι : Type} [Fintype ι] [DecidableEq ι]
    (b : Module.Basis ι K W) (Qf : QuadraticForm K W) (ρ : R →* (W ≃ₗ[K] W))
    (hr : ρ.range = ⁅orthSubgroup Qf, orthSubgroup Qf⁆) (Q' : (ι → K) → K)
    (hQ' : ∀ v, Qf (b.equivFun.symm v) = Q' v) :
    (b.toGL.toMonoidHom.comp ρ).range = StatedOmega Q' := by
  have hset : ∀ g : W ≃ₗ[K] W,
      b.toGL g ∈ (orthSubgroup Qf).map b.toGL.toMonoidHom ↔
        ∀ v : ι → K, Q' (Matrix.mulVec (b.toGL g : Matrix ι ι K) v) = Q' v := by
    intro g
    rw [Subgroup.mem_map_equiv, MulEquiv.symm_apply_apply]
    constructor
    · intro hg v
      have hg' : ∀ x, Qf (g x) = Qf x := hg
      obtain ⟨w, rfl⟩ := b.equivFun.surjective v
      rw [← hQ', ← hQ']
      simp only [basis_toGL_mulVec_equivFun, LinearEquiv.symm_apply_apply]
      exact hg' w
    · intro h
      change ∀ x, Qf (g x) = Qf x
      intro x
      have h' := h (b.equivFun x)
      rw [← hQ', ← hQ'] at h'
      simp only [basis_toGL_mulVec_equivFun, LinearEquiv.symm_apply_apply] at h'
      exact h'
  have hset_eq : {A : GL ι K | ∀ v : ι → K, Q' (Matrix.mulVec (A : Matrix ι ι K) v) = Q' v} =
      ((orthSubgroup Qf).map b.toGL.toMonoidHom : Set (GL ι K)) := by
    ext A
    obtain ⟨g, rfl⟩ := b.toGL.surjective A
    exact (hset g).symm
  have hmap : (orthSubgroup Qf).map b.toGL.toMonoidHom =
      CFSG.MatrixModel.isometryCore Q' := by
    unfold CFSG.MatrixModel.isometryCore
    rw [hset_eq, Subgroup.closure_eq]
  rw [MonoidHom.range_comp, hr, Subgroup.map_commutator, hmap]
  rfl

theorem exists_basis_range_omega (Qf : QuadraticForm K W) (hnd : Qf.polarBilin.Nondegenerate)
    {n : ℕ} (hn : 1 ≤ n) (hdim : Module.finrank K W = 2 * n) (ρ : R →* (W ≃ₗ[K] W))
    (hr : ρ.range = ⁅orthSubgroup Qf, orthSubgroup Qf⁆) :
    (∃ b : Module.Basis (Fin n ⊕ Fin n) K W,
        (b.toGL.toMonoidHom.comp ρ).range = StatedOmega (StatedQuadPlus n K)) ∨
      (∃ (β γ : K) (b : Module.Basis (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) K W), β ≠ 0 ∧
        (∀ s : K, s ^ 2 + β * s + γ ≠ 0) ∧
        (b.toGL.toMonoidHom.comp ρ).range = StatedOmega (StatedQuadMinus n K β γ)) := by
  rcases (CFSG.ComponentClassification.UnbalancedCatalog.finite_even_regular_quadratic_normal_forms
    Qf hnd).2.2.1 n hn hdim with ⟨b, hb⟩ | ⟨β, γ, hβ, hs, b, hb⟩
  · refine Or.inl ⟨b, range_comp_eq_statedOmega b Qf ρ hr (StatedQuadPlus n K) ?_⟩
    intro v
    rw [basis_equivFun_symm_plus b v]
    exact hb (fun i => v (Sum.inl i)) (fun i => v (Sum.inr i))
  · refine Or.inr ⟨β, γ, b, hβ, hs,
      range_comp_eq_statedOmega b Qf ρ hr (StatedQuadMinus n K β γ) ?_⟩
    intro v
    rw [basis_equivFun_symm_minus b v]
    exact hb (fun i => v (Sum.inl i)) (fun i => v (Sum.inr (Sum.inl i)))
      (v (Sum.inr (Sum.inr 0))) (v (Sum.inr (Sum.inr 1)))

end CFSG.RankThree.GF2n.Stroth80.Classify
