module

public import TauCeti.LinearAlgebra.BilinearForm.Diagonalization
public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

section Orth

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem w85g_map_eq_natCast_finrank_commSpace {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgg : g * g = 1) {u : V}
    (hu : ∀ x : V, (polar Q x u) ^ 2 = Q (g x - x)) :
    Q u = (finrank K (commSpace g) : K) := by
  classical
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  obtain ⟨X, hX⟩ := (fixSpace g).exists_isCompl
  have hX' : IsCompl X (fixSpace g) := hX.symm
  have hdim : finrank K X = finrank K (commSpace g) := finrank_compl_eq hX'
  set β' : LinearMap.BilinForm K X := (wallForm Q g).restrict X with hβ'def
  have hβ'symm : β'.IsSymm := (wallForm_isSymm hg hgg).restrict X
  have hβ'nd : β'.Nondegenerate := by
    rw [hβ'def]
    exact wallForm_restrict_nondegenerate hQ hg hgg hX'
  by_cases halt : β'.IsAlt
  ·
    have halt' : ((wallForm Q g).restrict X).IsAlt := by rwa [hβ'def] at halt
    have hzero : ∀ x ∈ commSpace g, Q x = 0 := (wallForm_restrict_isAlt_iff hg hX').mp halt'
    have hu0 : u = 0 := by
      refine hQ.1 u fun x => ?_
      rw [polarBilin_apply_apply, polar_comm Q u x]
      have hsq : (polar Q x u) ^ 2 = (0 : K) ^ 2 := by
        rw [hu x, hzero (g x - x) (sub_mem_commSpace g x)]
        simp
      exact CharTwo.sq_inj.mp hsq
    have heven : Even (finrank K (commSpace g)) :=
      even_finrank_commSpace_of_forall_eq_zero hQ hg hgg hzero
    rw [hu0, map_zero, ← hdim]
    exact ((CharP.cast_eq_zero_iff K 2 (finrank K X)).mpr (by
      rw [hdim]
      exact even_iff_two_dvd.mp heven)).symm
  ·
    obtain ⟨e, hmat⟩ :=
      LinearMap.BilinForm.IsSymm.exists_basis_toMatrix_eq_one
        (fun a => isSquare_of_charTwo' a) hβ'symm hβ'nd (fun h => absurd h halt)
    set x₀ : X := ∑ i, e i with hx₀def
    have hcoord : e.repr x₀ = (fun _ : Fin (finrank K X) => (1 : K)) := by
      rw [hx₀def]
      simpa using e.repr_sum_self (fun _ : Fin (finrank K X) => (1 : K))
    have hdot_self : ∀ y : X, β' y y = ∑ i, e.repr y i * e.repr y i := by
      intro y
      rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec e β' y y, hmat,
        Matrix.one_mulVec]
      simp [dotProduct]
    have hdot_x0 : ∀ y : X, β' y x₀ = ∑ i, e.repr y i := by
      intro y
      rw [LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec e β' y x₀, hmat,
        Matrix.one_mulVec, hcoord]
      simp [dotProduct]
    have keycoord : ∀ y : X, β' y y = (β' y x₀) ^ 2 := by
      intro y
      rw [hdot_self y, hdot_x0 y, sum_pow_char 2 Finset.univ (fun i => e.repr y i)]
      simp [pow_two]
    have h1 : ∀ y : X, wallForm Q g (y : V) (y : V) = β' y y := by
      intro y
      rw [hβ'def, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
    have h2 : ∀ y : X, wallForm Q g (y : V) (x₀ : V) = β' y x₀ := by
      intro y
      rw [hβ'def, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
    have keyX : ∀ y : X, polar Q (y : V) u = wallForm Q g (y : V) (x₀ : V) := by
      intro y
      apply CharTwo.sq_inj.mp
      rw [hu (y : V), ← wallForm_self hg (y : V), h1 y, h2 y, keycoord y]
    have keyFix : ∀ c ∈ fixSpace g, polar Q c u = wallForm Q g c (x₀ : V) := by
      intro c hc
      have hc0 : polar Q c u = 0 := by
        apply CharTwo.sq_inj.mp
        rw [hu c, mem_fixSpace.mp hc, sub_self, map_zero]
        simp
      have hcf : wallForm Q g c (x₀ : V) = 0 := by
        rw [wallForm_symm hg hgg]
        exact wallForm_apply_fixSpace Q (x₀ : V) hc
      rw [hc0, hcf]
    have keyAll : ∀ v : V, polar Q v u = wallForm Q g v (x₀ : V) := by
      intro v
      have hv : v ∈ X ⊔ fixSpace g := by rw [hX'.sup_eq_top]; exact Submodule.mem_top
      obtain ⟨y, hy, c, hc, rfl⟩ := Submodule.mem_sup.mp hv
      rw [polar_add_left, map_add, LinearMap.add_apply, keyX ⟨y, hy⟩, keyFix c hc]
    have hu_eq : u = g (x₀ : V) - (x₀ : V) := by
      have hdiff : u - (g (x₀ : V) - (x₀ : V)) = 0 := by
        refine hQ.1 _ fun v => ?_
        rw [polarBilin_apply_apply, QuadraticMap.polar_sub_left, polar_comm Q u v,
          polar_comm Q (g (x₀ : V) - (x₀ : V)) v, keyAll v, wallForm_apply, sub_self]
      exact sub_eq_zero.mp hdiff
    have hdiag : wallForm Q g (x₀ : V) (x₀ : V) = (finrank K X : K) := by
      have hxx : wallForm Q g (x₀ : V) (x₀ : V) = β' x₀ x₀ := by
        rw [hβ'def, LinearMap.BilinForm.restrict_apply, LinearMap.domRestrict_apply]
      rw [hxx, LinearMap.BilinForm.apply_eq_dotProduct_toMatrix_mulVec e β' x₀ x₀, hmat,
        Matrix.one_mulVec, hcoord]
      simp [dotProduct, Finset.sum_const, nsmul_eq_mul]
    rw [hu_eq, ← wallForm_self hg (x₀ : V), hdiag, hdim]

end Orth

end CFSG.LocalAnalysis.WeakClosure81

end
