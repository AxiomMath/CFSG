module

public import CFSG.RankThree.PartOne.KC.OrthogonalPrimaryPairing
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityDescent

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section Dual

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem polar_eq_polar_primaryProjection_reciprocal (hx : OddOrderIsometry Q p x) {r : K[X]}
    (hr : r ∈ primaryFactors x.toLinearMap) {u : V} (hu : u ∈ primaryComponent x.toLinearMap r)
    (y : V) : QuadraticMap.polar Q u y =
      QuadraticMap.polar Q u (primaryProjection x.toLinearMap (reciprocalPolynomial r) y) := by
  classical
  have hsum : y = ∑ a ∈ primaryFactors x.toLinearMap, primaryProjection x.toLinearMap a y := by
    have := LinearMap.congr_fun (sum_primaryProjection hx.squarefree_minpoly) y
    rw [LinearMap.sum_apply] at this
    simpa using this.symm
  have h := map_sum (QuadraticMap.polarBilin Q u) (fun a => primaryProjection x.toLinearMap a y)
    (primaryFactors x.toLinearMap)
  simp only [QuadraticMap.polarBilin_apply_apply] at h
  conv_lhs => rw [hsum]
  rw [h, Finset.sum_eq_single (reciprocalPolynomial r)]
  · intro a ha har
    exact hx.polar_primaryComponent_eq_zero hr ha har hu
      (primaryProjection_mem hx.squarefree_minpoly ha y)
  · intro hr'
    exact absurd (hx.reciprocalPolynomial_mem hr) hr'

theorem inf_primaryComponent_reciprocal_ne_bot (hx : OddOrderIsometry Q p x) {r : K[X]}
    (hr : r ∈ primaryFactors x.toLinearMap) {S : Submodule K V} (hS : ∀ v ∈ S, x v ∈ S)
    (hnd : (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) S).Nondegenerate)
    (hne : S ⊓ primaryComponent x.toLinearMap r ≠ ⊥) :
    S ⊓ primaryComponent x.toLinearMap (reciprocalPolynomial r) ≠ ⊥ := by
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨y, hyS, hy⟩ : ∃ y ∈ S, QuadraticMap.polar Q u y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hu0
    have := hnd.1 ⟨u, hu.1⟩ (fun y => by simpa using hcon y y.2)
    exact congrArg Subtype.val this
  intro hbot
  have hmem : primaryProjection x.toLinearMap (reciprocalPolynomial r) y ∈
      S ⊓ primaryComponent x.toLinearMap (reciprocalPolynomial r) :=
    ⟨aeval_apply_mem_of_forall_mem (f := x.toLinearMap) hS _ hyS,
      primaryProjection_mem hx.squarefree_minpoly (hx.reciprocalPolynomial_mem hr) y⟩
  rw [hbot, Submodule.mem_bot] at hmem
  apply hy
  rw [polar_eq_polar_primaryProjection_reciprocal hx hr hu.2 y, hmem,
    QuadraticMap.polar_zero_right]

end Dual

end CFSG.RankThree.PartOne.KCOrthogonal
