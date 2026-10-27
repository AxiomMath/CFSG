module

public import CFSG.RankThree.GF2n.Stroth80.Sec56SingularSpan

public section

namespace CFSG.RankThree.GF2n.Stroth80

open QuadraticMap

variable {K : Type} [Field K] [CharP K 2]

theorem vanishLA_polar_range {V : Type} [AddCommGroup V] [Module K V] {Q' : QuadraticForm K V}
    {T : V →ₗ[K] V} (hT2 : ∀ w, T (T w) = 0) (hiso : ∀ w, Q' (w + T w) = Q' w) (v w : V) :
    polar Q' (T v) (T w) = 0 := by
  have h1 : ∀ a b : V, polar Q' (a + T a) (b + T b) = polar Q' a b := by
    intro a b
    have e : (a + T a) + (b + T b) = (a + b) + T (a + b) := by rw [map_add]; abel
    unfold QuadraticMap.polar
    rw [e, hiso, hiso, hiso]
  have h2 : ∀ a b : V, polar Q' a (T b) + polar Q' (T a) b + polar Q' (T a) (T b) = 0 := by
    intro a b
    have := h1 a b
    simp only [polar_add_left, polar_add_right] at this
    linear_combination this
  have h3 := h2 v (T w)
  simp only [hT2, polar_zero_right, add_zero, zero_add] at h3
  exact h3

theorem vanishLA_Q_range_add {V : Type} [AddCommGroup V] [Module K V] {Q' : QuadraticForm K V}
    {T : V →ₗ[K] V} (hT2 : ∀ w, T (T w) = 0) (hiso : ∀ w, Q' (w + T w) = Q' w) (v w : V) :
    Q' (T (v + w)) = Q' (T v) + Q' (T w) := by
  rw [map_add, QuadraticMap.map_add Q' (T v) (T w), vanishLA_polar_range hT2 hiso, add_zero]

theorem vanishLA_polar_eq_Q_of_singular {V : Type} [AddCommGroup V] [Module K V]
    {Q' : QuadraticForm K V} {T : V →ₗ[K] V} (hiso : ∀ w, Q' (w + T w) = Q' w) {w : V}
    (hw : Q' w = 0) : polar Q' w (T w) = Q' (T w) := by
  have h := hiso w
  rw [QuadraticMap.map_add Q' w (T w), hw, zero_add] at h
  have h2 : polar Q' w (T w) + Q' (T w) = 0 := by linear_combination h
  have h3 : polar Q' w (T w) = -Q' (T w) := eq_neg_of_add_eq_zero_left h2
  rw [h3, CharTwo.neg_eq]

theorem vanishLA_exists_nonsing_perp {ι : Type} [Fintype ι] [DecidableEq ι] [Finite K]
    {Q' : QuadraticForm K (ι → K)} (hQ : (polarBilin Q').Nondegenerate)
    (h4 : 4 ≤ Module.finrank K (ι → K)) {x : ι → K} (hx : x ≠ 0) :
    ∃ d : ι → K, polar Q' x d = 0 ∧ Q' d ≠ 0 := by
  by_contra hcon
  push Not at hcon
  let N : Submodule K (ι → K) := Submodule.span K {x}
  let H := LinearMap.BilinForm.orthogonal (polarBilin Q') N
  have hdimN : Module.finrank K N = 1 := finrank_span_singleton hx
  have hH : Module.finrank K H = Module.finrank K (ι → K) - 1 := by
    rw [LinearMap.BilinForm.finrank_orthogonal hQ N, hdimN]
  have hHmem : ∀ y ∈ H, polar Q' x y = 0 := by
    intro y hy
    have := (LinearMap.BilinForm.mem_orthogonal_iff).mp hy x (Submodule.mem_span_singleton_self x)
    simpa [polarBilin_apply_apply] using this
  have hHiso : H ≤ LinearMap.BilinForm.orthogonal (polarBilin Q') H := by
    intro y hy
    rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro z hz
    have hyz : polar Q' y z = 0 := by
      have h1 := hcon (y + z) (by
        rw [polar_add_right, hHmem y hy, hHmem z hz, add_zero])
      have h2 := hcon y (hHmem y hy)
      have h3 := hcon z (hHmem z hz)
      have h4' := QuadraticMap.map_add Q' y z
      rw [h1] at h4'
      rw [h2, h3] at h4'
      linear_combination -h4'
    simpa [polarBilin_apply_apply] using (polar_comm Q' y z ▸ hyz)
  have hle := Submodule.finrank_mono hHiso
  rw [LinearMap.BilinForm.finrank_orthogonal hQ H, hH] at hle
  have hpos : 1 ≤ Module.finrank K (ι → K) := by omega
  omega

theorem vanishLA_exists_singular_polar {ι : Type} [Fintype ι] [DecidableEq ι] [Finite K]
    {Q' : QuadraticForm K (ι → K)} (hQ : (polarBilin Q').Nondegenerate)
    (h4 : 4 ≤ Module.finrank K (ι → K)) {T : (ι → K) →ₗ[K] (ι → K)}
    (hT2 : ∀ w, T (T w) = 0) (hiso : ∀ w, Q' (w + T w) = Q' w) (hT : ∃ v, Q' (T v) ≠ 0) :
    ∃ w, Q' w = 0 ∧ polar Q' w (T w) ≠ 0 := by
  classical
  by_contra hcon
  push Not at hcon
  have hsing : ∀ w, Q' w = 0 → Q' (T w) = 0 := fun w hw => by
    rw [← vanishLA_polar_eq_Q_of_singular hiso hw]
    exact hcon w hw
  let f : (ι → K) →+ K := AddMonoidHom.mk' (fun w => Q' (T w))
    (fun v w => vanishLA_Q_range_add hT2 hiso v w)
  have hall : ∀ x, Q' (T x) = 0 := by
    intro x
    by_cases hx : x = 0
    · subst hx
      simp
    · obtain ⟨d, hd, hdQ⟩ := vanishLA_exists_nonsing_perp hQ h4 hx
      have hS : ∀ s : ι → K, polar Q' d s = 0 → Q' s = 0 → s ∈ f.ker := by
        intro s _ hs
        exact AddMonoidHom.mem_ker.mpr (hsing s hs)
      have hxS := CFSG.ClassicalGroups.Orthogonal.mem_of_forall_singular_perp hQ (by omega) hdQ hS
        (x := x) (by rw [polar_comm]; exact hd)
      exact AddMonoidHom.mem_ker.mp hxS
  obtain ⟨v, hv⟩ := hT
  exact hv (hall v)

end CFSG.RankThree.GF2n.Stroth80
