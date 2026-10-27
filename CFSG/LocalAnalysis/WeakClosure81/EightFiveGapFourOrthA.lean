module

public import CFSG.RankThree.OrthogonalInvolutions.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Module QuadraticMap CFSG.RankThree.OrthogonalInvolutions

section Orth

variable {K V : Type} [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V]

theorem w85g_exists_polar_sq_eq {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgg : g * g = 1) :
    ∃ u : V, ∀ x : V, (polar Q x u) ^ 2 = Q (g x - x) := by
  classical
  haveI : ExpChar K 2 := ExpChar.prime Nat.prime_two
  haveI : PerfectRing K 2 := inferInstance
  let ρ : K ≃+* K := (frobeniusEquiv K 2).symm
  have hρ : ∀ x : K, ρ x ^ 2 = x := fun x => frobeniusEquiv_symm_pow_p K 2 x
  have hρ2 : ∀ x : K, ρ (x ^ 2) = x := fun x => frobeniusEquiv_symm_pow K 2 x
  let φ : V →ₗ[K] K :=
    { toFun := fun x => ρ (Q (g x - x))
      map_add' := by
        intro x y
        have hsub : g (x + y) - (x + y) = (g x - x) + (g y - y) := by
          rw [map_add]; abel
        have hzero : polar Q (g x - x) (g y - y) = 0 :=
          polar_commSpace_eq_zero hg hgg (sub_mem_commSpace g x) (sub_mem_commSpace g y)
        rw [hsub, map_add_eq, hzero, add_zero]
        exact map_add ρ _ _
      map_smul' := by
        intro c x
        have hsub : g (c • x) - c • x = c • (g x - x) := by
          rw [map_smul, smul_sub]
        rw [hsub, QuadraticMap.map_smul, smul_eq_mul, smul_eq_mul, ← pow_two, map_mul, hρ2]
        rfl }
  refine ⟨(LinearMap.BilinForm.toDual Q.polarBilin hQ).symm φ, fun x => ?_⟩
  have h1 : Q.polarBilin ((LinearMap.BilinForm.toDual Q.polarBilin hQ).symm φ) x = φ x :=
    LinearMap.BilinForm.apply_toDual_symm_apply φ x
  rw [polar_comm Q x, ← polarBilin_apply_apply, h1]
  exact hρ _

theorem w85g_apply_eq_of_polar_sq_eq {Q : QuadraticForm K V}
    (hQ : Q.polarBilin.Nondegenerate) {g : V ≃ₗ[K] V} {u : V}
    (hu : ∀ x : V, (polar Q x u) ^ 2 = Q (g x - x)) {h : V ≃ₗ[K] V}
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hhg : h * g = g * h) : h u = u := by
  have key : ∀ y : V, polar Q (h y) u = polar Q y u := by
    intro y
    apply CharTwo.sq_inj.mp
    rw [hu (h y), hu y]
    have hcomm : g (h y) = h (g y) := by
      have h1 := congrArg (fun e : V ≃ₗ[K] V => e y) hhg
      simpa [LinearEquiv.mul_apply] using h1.symm
    have h2 : h (g y) - h y = h (g y - y) := by rw [map_sub]
    rw [hcomm, h2, TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hh]
  have key2 : ∀ x : V, polar Q x (h u) = polar Q x u := by
    intro x
    calc polar Q x (h u)
        = polar Q (h (h.symm x)) (h u) := by rw [LinearEquiv.apply_symm_apply h x]
      _ = polar Q (h.symm x) u :=
          TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hh _ _
      _ = polar Q (h (h.symm x)) u := (key (h.symm x)).symm
      _ = polar Q x u := by rw [LinearEquiv.apply_symm_apply h x]
  have hzero : h u - u = 0 := by
    refine hQ.1 _ fun x => ?_
    rw [polarBilin_apply_apply, QuadraticMap.polar_sub_left, polar_comm Q (h u) x,
      polar_comm Q u x, key2, sub_self]
  exact sub_eq_zero.mp hzero

end Orth

end CFSG.LocalAnalysis.WeakClosure81

end
