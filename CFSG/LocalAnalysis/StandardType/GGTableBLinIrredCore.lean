module

public import CFSG.LocalAnalysis.StandardType.GGTableBLinUnitLModProof
public import CFSG.LocalAnalysis.StandardType.GGFieldCaseTableBTypeAIrred

public section

namespace CFSG.StandardType.LinIrred

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ComponentClassification CFSG.Assembly TypeA TypeANbrDvd CFSG.StandardType.LinUnitL

variable {d p : ℕ} {K : Type} [Field K]

section Perm

variable [CharP K 2]

theorem permSL_mul (σ τ : Equiv.Perm (Fin d)) :
    (permSL (σ * τ) : SpecialLinearGroup (Fin d) K) = permSL τ * permSL σ := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, coe_permSL, coe_permSL, coe_permSL, permMatrix_mul]

theorem permSL_one : (permSL (1 : Equiv.Perm (Fin d)) : SpecialLinearGroup (Fin d) K) = 1 := by
  apply Subtype.ext
  rw [coe_permSL, permMatrix_one, Matrix.SpecialLinearGroup.coe_one]

theorem perm_image_mem_closure {L' : Type} [Group L'] (φ' : SpecialLinearGroup (Fin d) K →* L')
    (σ : Equiv.Perm (Fin d)) :
    φ' (permSL σ) ∈ Subgroup.closure
      {m | m ∈ Set.range (fun τ : Equiv.Perm (Fin d) => φ' (permSL τ)) ∧ m * m = 1} := by
  refine Equiv.Perm.swap_induction_on σ ?_ ?_
  · rw [permSL_one, map_one]
    exact Subgroup.one_mem _
  · intro f x y _ ih
    rw [permSL_mul, map_mul]
    refine Subgroup.mul_mem _ ih (Subgroup.subset_closure ⟨⟨_, rfl⟩, ?_⟩)
    rw [← map_mul, ← permSL_mul, Equiv.swap_mul_self, permSL_one, map_one]

variable {L' : Type} [Group L'] {φ' : SpecialLinearGroup (Fin d) K →* L'}

theorem eq_one_of_perm_fixed (hd : 3 ≤ d) (hφ's : Function.Surjective φ')
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t) :
    ∀ a ∈ A, (∀ n ∈ Set.range (fun σ : Equiv.Perm (Fin d) => φ' (permSL σ)),
      MulAut.conj n * a * (MulAut.conj n)⁻¹ = a) → a = 1 := by
  intro a ha hfix
  obtain ⟨t, hat⟩ := hdiag a ha
  exact ActsDiag.eq_one_of_conj_perm hd hφ's hφker hat fun σ => hfix _ ⟨σ, rfl⟩

theorem conj_mul_inv_mem_heart
    (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K) {A : Subgroup (MulAut L')}
    (hφ's : Function.Surjective φ') (hAp : ∀ a ∈ A, a ^ p = 1)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t) (σ : Equiv.Perm (Fin d)) {a : MulAut L'}
    (ha : a ∈ A) :
    MulAut.conj (φ' (permSL σ)) * a * (MulAut.conj (φ' (permSL σ)))⁻¹ * a⁻¹ ∈
      Subgroup.closure (heartSet φ' p) := by
  obtain ⟨t, hat⟩ := hdiag a ha
  have het := (hat.conj_perm σ).mul hat.inv
  have hprod : ∏ k, t (σ k) * (t k)⁻¹ = 1 := by
    rw [Finset.prod_mul_distrib, Finset.prod_inv_distrib, Equiv.prod_comp σ t]
    exact mul_inv_cancel₀ (Finset.prod_ne_zero_iff.mpr fun k _ => hat.ne_zero k)
  have heq : MulAut.conj (φ' (permSL σ)) * a * (MulAut.conj (φ' (permSL σ)))⁻¹ * a⁻¹ =
      MulAut.conj (φ' (diagSLOf (fun k => t (σ k) * (t k)⁻¹) hprod)) :=
    het.unique hφ's (actsDiag_conj (coe_diagSLOf _ hprod))
  rw [heq]
  exact Subgroup.subset_closure ⟨diagSLOf (fun k => t (σ k) * (t k)⁻¹) hprod, _,
    coe_diagSLOf _ hprod, fun k => hat.ratio_pow hφker (hAp a ha) (σ k) k, rfl⟩

end Perm

section Weyl

variable [CharP K 2] [Finite K] {L' : Type} [Group L'] {φ' : SpecialLinearGroup (Fin d) K →* L'}

theorem exists_weyl_fix (hp : p.Prime) (hp2 : p ≠ 2) (hpK : p ∣ Nat.card K - 1) (hd : 5 ≤ d)
    (hφ's : Function.Surjective φ') (hφker : ∀ g, φ' g = 1 → g ∈ scalars d K)
    {A : Subgroup (MulAut L')} (hA : IsElemAbelian p A) (hsc : GGTorusSelfCent p A)
    (hdiag : ∀ a ∈ A, ∃ t : Fin d → K, ActsDiag φ' a t) {n : L'}
    (hn : MulAut.conj n ∈ Subgroup.normalizer (A : Set (MulAut L'))) :
    ∃ w ∈ Set.range (fun σ : Equiv.Perm (Fin d) => φ' (permSL σ)),
      ∀ a ∈ A, a (n * w⁻¹) = n * w⁻¹ := by
  classical
  obtain ⟨g, rfl⟩ := hφ's n
  obtain ⟨ζ, hζ⟩ := TypeA.exists_isPrimitiveRoot hp hpK
  have hζinv : ζ ≠ ζ⁻¹ := ne_inv_of_isPrimitiveRoot hζ hp hp2
  have hζ0 : ζ ≠ 0 := hζ.ne_zero hp.ne_zero
  have hpv : ∀ k l : Fin d, ∀ m, ggPairVec k l ζ m ^ p = 1 := by
    intro k l m
    rw [ggPairVec_apply]
    split_ifs <;> simp [mul_pow, inv_pow, hζ.pow_eq_one]
  have hconj : ∀ s : SpecialLinearGroup (Fin d) K,
      MulAut.conj (φ' (g * s * g⁻¹)) =
        MulAut.conj (φ' g) * MulAut.conj (φ' s) * (MulAut.conj (φ' g))⁻¹ := by
    intro s
    rw [map_mul, map_mul, map_inv, map_mul, map_mul, map_inv]
  have hmono : ∀ i j : Fin d, i ≠ j → ∃ D' : Fin d → K,
      ((SpecialLinearGroup.toGL g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) *
        diagonal (rootT ζ i j) =
      diagonal D' * ((SpecialLinearGroup.toGL g : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) := by
    intro i j hij
    set Dij := diagSLOf (rootT ζ i j) (prod_rootT hζ0 hij) with hDij
    set X := g * Dij * g⁻¹ with hX
    have hXA : MulAut.conj (φ' X) ∈ A := by
      have h1 : MulAut.conj (φ' Dij) ∈ A :=
        conj_mem_of_selfCent hsc hdiag (coe_diagSLOf _ _) (rootT_pow hζ.pow_eq_one i j)
      rw [hX, hconj]
      exact (Subgroup.mem_normalizer_iff.mp hn _).mp h1
    have hXd : (X : Matrix (Fin d) (Fin d) K).IsDiag :=
      isDiag_of_conj_comm hφker hd hζinv fun k l _ D hD =>
        TableB.IsElemAbelian.comm hA hXA (conj_mem_of_selfCent hsc hdiag hD (hpv k l))
    refine ⟨fun k => (X : Matrix (Fin d) (Fin d) K) k k, ?_⟩
    have e1 : X * g = g * Dij := by rw [hX]; group
    have e2 := congrArg (fun y : SpecialLinearGroup (Fin d) K => (y : Matrix (Fin d) (Fin d) K)) e1
    simp only [Matrix.SpecialLinearGroup.coe_mul] at e2
    have hXm : (X : Matrix (Fin d) (Fin d) K) =
        diagonal fun k => (X : Matrix (Fin d) (Fin d) K) k k :=
      ((isDiag_iff_diagonal_diag _).mp hXd).symm
    rw [SpecialLinearGroup.coe_GL_coe_matrix, ← coe_diagSLOf (rootT ζ i j) (prod_rootT hζ0 hij),
      ← hDij, ← e2]
    exact congrArg (· * (g : Matrix (Fin d) (Fin d) K)) hXm
  obtain ⟨π, hπ⟩ := exists_perm_mul_diagonal hζinv (SpecialLinearGroup.toGL g) hmono
  refine ⟨φ' (permSL π), ⟨π, rfl⟩, fun a ha => ?_⟩
  obtain ⟨t, hat⟩ := hdiag a ha
  have hsd : ((g * (permSL π)⁻¹ : SpecialLinearGroup (Fin d) K) :
      Matrix (Fin d) (Fin d) K).IsDiag := by
    refine isDiag_of_conj_comm hφker hd hζinv fun k l _ D hD => ?_
    set E : SpecialLinearGroup (Fin d) K := (permSL π)⁻¹ * D * permSL π with hEdef
    have hE : (E : Matrix (Fin d) (Fin d) K) = diagonal (ggPairVec k l ζ ∘ ⇑π⁻¹) := by
      have := coe_permSL_conj hD π⁻¹
      rwa [← permSL_inv, inv_inv] at this
    have hgE : g * E = D * g := by
      apply Subtype.ext
      rw [Matrix.SpecialLinearGroup.coe_mul g E, Matrix.SpecialLinearGroup.coe_mul D g, hE, hD]
      have h1 := hπ (ggPairVec k l ζ ∘ ⇑π⁻¹)
      rw [SpecialLinearGroup.coe_GL_coe_matrix] at h1
      rw [h1]
      congr 2
      funext m
      simp
    have hsD : g * (permSL π)⁻¹ * D = D * (g * (permSL π)⁻¹) :=
      calc g * (permSL π)⁻¹ * D = g * E * (permSL π)⁻¹ := by rw [hEdef]; group
        _ = D * g * (permSL π)⁻¹ := by rw [hgE]
        _ = D * (g * (permSL π)⁻¹) := by group
    have := congrArg (fun y => MulAut.conj (φ' y)) hsD
    simpa [map_mul] using this
  have e : φ' g * (φ' (permSL π))⁻¹ = φ' (g * (permSL π)⁻¹) := by rw [map_mul, map_inv]
  rw [e]
  exact hat.apply_of_isDiag hsd

end Weyl

end CFSG.StandardType.LinIrred

end
