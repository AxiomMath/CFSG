module

public import CFSG.RankThree.PartOne.KC.OrthogonalPrimaryPairing
public import CFSG.RankThree.PartOne.KC.OrthogonalKernelSectorRigidityDescent

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Polynomial Module CFSG.RankThree.PartOne.KCPrimary

section Regular

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {Q : QuadraticForm K V} {p : ℕ} {x : V ≃ₗ[K] V}

theorem polar_eq_polar_primaryProjection (hx : OddOrderIsometry Q p x) {r : K[X]}
    (hr : r ∈ primaryFactors x.toLinearMap) (hself : r = reciprocalPolynomial r) {u : V}
    (hu : u ∈ primaryComponent x.toLinearMap r) (y : V) :
    QuadraticMap.polar Q u y = QuadraticMap.polar Q u (primaryProjection x.toLinearMap r y) := by
  classical
  have hsum : y = ∑ a ∈ primaryFactors x.toLinearMap, primaryProjection x.toLinearMap a y := by
    have := LinearMap.congr_fun (sum_primaryProjection hx.squarefree_minpoly) y
    rw [LinearMap.sum_apply] at this
    simpa using this.symm
  have h := map_sum (QuadraticMap.polarBilin Q u) (fun a => primaryProjection x.toLinearMap a y)
    (primaryFactors x.toLinearMap)
  simp only [QuadraticMap.polarBilin_apply_apply] at h
  conv_lhs => rw [hsum]
  rw [h, Finset.sum_eq_single r]
  · intro a ha har
    exact hx.polar_primaryComponent_eq_zero hr ha (by rw [← hself]; exact har)
      hu (primaryProjection_mem hx.squarefree_minpoly ha y)
  · intro hr'
    exact absurd hr hr'

theorem exists_polar_ne_zero_of_selfdual (hx : OddOrderIsometry Q p x) {r : K[X]}
    (hr : r ∈ primaryFactors x.toLinearMap) (hself : r = reciprocalPolynomial r)
    {S : Submodule K V} (hS : ∀ v ∈ S, x v ∈ S)
    (hnd : (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) S).Nondegenerate) {u : V}
    (hu : u ∈ S ⊓ primaryComponent x.toLinearMap r) (hu0 : u ≠ 0) :
    ∃ u' ∈ S ⊓ primaryComponent x.toLinearMap r, QuadraticMap.polar Q u u' ≠ 0 := by
  obtain ⟨y, hyS, hy⟩ : ∃ y ∈ S, QuadraticMap.polar Q u y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    apply hu0
    have := hnd.1 ⟨u, hu.1⟩ (fun y => by simpa using hcon y y.2)
    exact congrArg Subtype.val this
  refine ⟨primaryProjection x.toLinearMap r y, ⟨?_, ?_⟩, ?_⟩
  · exact aeval_apply_mem_of_forall_mem (f := x.toLinearMap) hS _ hyS
  · exact primaryProjection_mem hx.squarefree_minpoly hr y
  · rw [← polar_eq_polar_primaryProjection hx hr hself hu.2 y]
    exact hy

omit [FiniteDimensional K V] in
theorem exists_map_ne_zero_of_polar_ne_zero {a b : V} (h : QuadraticMap.polar Q a b ≠ 0) :
    Q a ≠ 0 ∨ Q b ≠ 0 ∨ Q (a + b) ≠ 0 := by
  by_contra hcon
  push Not at hcon
  obtain ⟨h1, h2, h3⟩ := hcon
  apply h
  have := QuadraticMap.map_add Q a b
  rw [h1, h2, h3, zero_add, zero_add] at this
  exact this.symm

omit [FiniteDimensional K V] in
theorem exists_map_ne_zero_of_nondegenerate {S : Submodule K V}
    (hnd : (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) S).Nondegenerate)
    (hS : S ≠ ⊥) : ∃ v ∈ S, Q v ≠ 0 := by
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS
  obtain ⟨y, hy⟩ : ∃ y : S, QuadraticMap.polar Q u y ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hu0 (congrArg Subtype.val (hnd.1 ⟨u, hu⟩ (fun y => by simpa using hcon y)))
  rcases exists_map_ne_zero_of_polar_ne_zero hy with h | h | h
  · exact ⟨u, hu, h⟩
  · exact ⟨y, y.2, h⟩
  · exact ⟨u + y, S.add_mem hu y.2, h⟩

theorem exists_map_ne_zero_of_selfdual (hx : OddOrderIsometry Q p x) {r : K[X]}
    (hr : r ∈ primaryFactors x.toLinearMap) (hself : r = reciprocalPolynomial r)
    {S : Submodule K V} (hS : ∀ v ∈ S, x v ∈ S)
    (hnd : (LinearMap.BilinForm.restrict (QuadraticMap.polarBilin Q) S).Nondegenerate)
    (hne : S ⊓ primaryComponent x.toLinearMap r ≠ ⊥) :
    ∃ v ∈ S ⊓ primaryComponent x.toLinearMap r, Q v ≠ 0 := by
  obtain ⟨u, hu, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨u', hu', hpol⟩ := exists_polar_ne_zero_of_selfdual hx hr hself hS hnd hu hu0
  rcases exists_map_ne_zero_of_polar_ne_zero hpol with h | h | h
  · exact ⟨u, hu, h⟩
  · exact ⟨u', hu', h⟩
  · exact ⟨u + u', Submodule.add_mem _ hu hu', h⟩

end Regular

end CFSG.RankThree.PartOne.KCOrthogonal
