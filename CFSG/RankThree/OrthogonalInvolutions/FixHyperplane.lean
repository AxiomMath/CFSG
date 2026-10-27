module

public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.Basic

public section

namespace CFSG.RankThree.OrthogonalInvolutions

open QuadraticMap

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

private lemma sub_smul_v₁_mem_inf_ker {W : Submodule K V} (μ : Module.Dual K V) {v₁ : V}
    (hv₁ : v₁ ∈ W) (hμ : μ v₁ = 1) {w : V} (hw : w ∈ W) :
    w - μ w • v₁ ∈ W ⊓ LinearMap.ker μ := by
  refine Submodule.mem_inf.mpr ⟨Submodule.sub_mem W hw (W.smul_mem (μ w) hv₁), ?_⟩
  rw [LinearMap.mem_ker, map_sub, map_smul, hμ, smul_eq_mul, mul_one, sub_self]

private lemma polar_sub_v₁_eq_zero_of_fixes {Q : QuadraticForm K V} {W : Submodule K V}
    (μ : Module.Dual K V) {v₁ : V} {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (hgH : ∀ x ∈ W, μ x = 0 → g x = x)
    {y : V} (hyW : y ∈ W) (hyμ : μ y = 0) : polar Q (g v₁ - v₁) y = 0 := by
  have hgy : g y = y := hgH y hyW hyμ
  have hpres : polar Q (g v₁) y = polar Q v₁ y := by
    simpa [hgy] using TauCeti.QuadraticMap.polar_apply_of_mem_orthogonalGroup hg v₁ y
  rw [QuadraticMap.polar_sub_left, hpres, sub_self]

private lemma Q_sub_add_polar_eq_zero {Q : QuadraticForm K V} {g : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q) (v₁ : V) :
    Q (g v₁ - v₁) + polar Q v₁ (g v₁ - v₁) = 0 := by
  have hgv : Q (g v₁) = Q v₁ := TauCeti.QuadraticMap.map_app_of_mem_orthogonalGroup hg v₁
  have hx : v₁ + (g v₁ - v₁) = g v₁ := by abel
  rw [QuadraticMap.polar, hx, hgv]
  abel

private lemma eq_zero_of_polar_eq_zero {Q : QuadraticForm K V} {W : Submodule K V}
    (hW : ∀ x ∈ W, (∀ y ∈ W, polar Q x y = 0) → x = 0) (μ : Module.Dual K V) {v₁ : V}
    (hv₁ : v₁ ∈ W) (hμ : μ v₁ = 1) {z : V} (hzW : z ∈ W)
    (hzH : ∀ y ∈ W, μ y = 0 → polar Q z y = 0) (hzv : polar Q z v₁ = 0) :
    z = 0 := by
  apply hW z hzW
  intro y hy
  have hy' := sub_smul_v₁_mem_inf_ker μ hv₁ hμ hy
  have h1 : polar Q z (y - μ y • v₁) = 0 := hzH _ hy'.1 hy'.2
  have h2 : polar Q z (μ y • v₁) = 0 := by
    rw [QuadraticMap.polar_smul_right, hzv, smul_zero]
  calc polar Q z y = polar Q z ((y - μ y • v₁) + μ y • v₁) := by rw [sub_add_cancel]
    _ = 0 := by rw [QuadraticMap.polar_add_right, h1, h2, add_zero]

private lemma eq_smul_div_of_polar {Q : QuadraticForm K V} {W : Submodule K V}
    (hW : ∀ x ∈ W, (∀ y ∈ W, polar Q x y = 0) → x = 0) (μ : Module.Dual K V) {v₁ : V}
    (hv₁ : v₁ ∈ W) (hμ : μ v₁ = 1) {x x' : V} (hxW : x ∈ W) (hx'W : x' ∈ W)
    (hxH : ∀ y ∈ W, μ y = 0 → polar Q x y = 0)
    (hx'H : ∀ y ∈ W, μ y = 0 → polar Q x' y = 0)
    (hxv : polar Q v₁ x ≠ 0) :
    x' = (polar Q v₁ x' / polar Q v₁ x) • x := by
  set z : V := polar Q v₁ x' • x - polar Q v₁ x • x' with hz
  have hzW : z ∈ W := by
    rw [hz]
    exact Submodule.sub_mem W (W.smul_mem _ hxW) (W.smul_mem _ hx'W)
  have hzH : ∀ y ∈ W, μ y = 0 → polar Q z y = 0 := by
    intro y hy hyμ
    rw [hz]
    simp only [QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left, smul_eq_mul,
      hxH y hy hyμ, hx'H y hy hyμ, mul_zero, sub_zero]
  have hzv : polar Q z v₁ = 0 := by
    rw [hz]
    simp only [QuadraticMap.polar_sub_left, QuadraticMap.polar_smul_left, smul_eq_mul,
      QuadraticMap.polar_comm Q x v₁, QuadraticMap.polar_comm Q x' v₁]
    ring
  have hz0 : z = 0 := eq_zero_of_polar_eq_zero hW μ hv₁ hμ hzW hzH hzv
  have hz' : polar Q v₁ x • x' = polar Q v₁ x' • x := by
    have hsub : polar Q v₁ x' • x - polar Q v₁ x • x' = 0 := by
      rw [← hz]
      exact hz0
    exact (sub_eq_zero.mp hsub).symm
  rw [div_eq_inv_mul, mul_smul, ← hz', inv_smul_smul₀ hxv]

private lemma smul_eq_one_of_polar {Q : QuadraticForm K V} {x x' : V} (v₁ : V) {c : K}
    (hx : Q x + polar Q v₁ x = 0) (hx' : Q x' + polar Q v₁ x' = 0)
    (hxx' : x' = c • x) (hQx : Q x ≠ 0) (hx'0 : x' ≠ 0) : c = 1 := by
  have hQx' : Q x' = c ^ 2 * Q x := by
    rw [hxx', QuadraticMap.map_smul, smul_eq_mul]
    ring
  have hpx' : polar Q v₁ x' = c * polar Q v₁ x := by
    rw [hxx', QuadraticMap.polar_smul_right, smul_eq_mul]
  have hpx : polar Q v₁ x = -Q x := by
    rw [eq_neg_iff_add_eq_zero, add_comm]
    exact hx
  have hzero : (c ^ 2 - c) * Q x = 0 := by
    have h := hx'
    rw [hQx', hpx', hpx] at h
    rw [show (c ^ 2 - c) * Q x = c ^ 2 * Q x + c * (-Q x) by ring]
    exact h
  have hc : c ^ 2 - c = 0 := by
    rcases mul_eq_zero.mp hzero with h | h
    · exact h
    · exact absurd h hQx
  have hfac : c * (c - 1) = 0 := by
    rw [← hc]
    ring
  rcases mul_eq_zero.mp hfac with hc0 | hc1
  · exfalso
    apply hx'0
    rw [hxx', hc0, zero_smul]
  · exact sub_eq_zero.mp hc1

private lemma eq_on_of_eq_apply {W : Submodule K V} (μ : Module.Dual K V) {v₁ : V}
    (hv₁ : v₁ ∈ W) (hμ : μ v₁ = 1) {g h : V ≃ₗ[K] V}
    (hgH : ∀ x ∈ W, μ x = 0 → g x = x)
    (hhH : ∀ x ∈ W, μ x = 0 → h x = x) (hv : g v₁ = h v₁) :
    ∀ w ∈ W, g w = h w := by
  intro w hw
  have h₁ := sub_smul_v₁_mem_inf_ker μ hv₁ hμ hw
  have hg₁ : g (w - μ w • v₁) = w - μ w • v₁ := hgH _ h₁.1 h₁.2
  have hh₁ : h (w - μ w • v₁) = w - μ w • v₁ := hhH _ h₁.1 h₁.2
  calc g w = g ((w - μ w • v₁) + μ w • v₁) := by rw [sub_add_cancel]
    _ = g (w - μ w • v₁) + g (μ w • v₁) := g.map_add _ _
    _ = (w - μ w • v₁) + μ w • g v₁ := by rw [hg₁, g.map_smul]
    _ = (w - μ w • v₁) + μ w • h v₁ := by rw [hv]
    _ = h (w - μ w • v₁) + h (μ w • v₁) := by rw [hh₁, h.map_smul]
    _ = h ((w - μ w • v₁) + μ w • v₁) := (h.map_add _ _).symm
    _ = h w := by rw [sub_add_cancel]

theorem eqOn_of_fix_ker {Q : QuadraticForm K V} {W : Submodule K V}
    (hW : ∀ x ∈ W, (∀ y ∈ W, polar Q x y = 0) → x = 0) (μ : Module.Dual K V) {v₁ : V}
    (hv₁ : v₁ ∈ W) (hμ : μ v₁ = 1) {g h : V ≃ₗ[K] V}
    (hg : g ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hh : h ∈ TauCeti.QuadraticMap.orthogonalGroup Q)
    (hgW : ∀ w ∈ W, g w ∈ W) (hhW : ∀ w ∈ W, h w ∈ W)
    (hgH : ∀ x ∈ W, μ x = 0 → g x = x) (hhH : ∀ x ∈ W, μ x = 0 → h x = x)
    (hg1 : g v₁ ≠ v₁) (hh1 : h v₁ ≠ v₁) : ∀ w ∈ W, g w = h w := by
  have hxgW : g v₁ - v₁ ∈ W := Submodule.sub_mem W (hgW v₁ hv₁) hv₁
  have hxgH : ∀ y ∈ W, μ y = 0 → polar Q (g v₁ - v₁) y = 0 :=
    fun y hy hyμ => polar_sub_v₁_eq_zero_of_fixes μ hg hgH hy hyμ
  have hxgrel := Q_sub_add_polar_eq_zero hg v₁
  have hxgQ : Q (g v₁ - v₁) ≠ 0 := by
    intro h0
    apply hg1
    have hp : polar Q v₁ (g v₁ - v₁) = 0 := by
      have h := hxgrel
      rw [h0, zero_add] at h
      exact h
    have hz : g v₁ - v₁ = 0 :=
      eq_zero_of_polar_eq_zero hW μ hv₁ hμ hxgW hxgH (by rwa [QuadraticMap.polar_comm])
    exact sub_eq_zero.mp hz
  have hxgv : polar Q v₁ (g v₁ - v₁) ≠ 0 := by
    intro h0
    apply hxgQ
    have h := hxgrel
    rw [h0, add_zero] at h
    exact h
  have hxhW : h v₁ - v₁ ∈ W := Submodule.sub_mem W (hhW v₁ hv₁) hv₁
  have hxhH : ∀ y ∈ W, μ y = 0 → polar Q (h v₁ - v₁) y = 0 :=
    fun y hy hyμ => polar_sub_v₁_eq_zero_of_fixes μ hh hhH hy hyμ
  have hxhrel := Q_sub_add_polar_eq_zero hh v₁
  have hxheq : h v₁ - v₁ =
      (polar Q v₁ (h v₁ - v₁) / polar Q v₁ (g v₁ - v₁)) • (g v₁ - v₁) :=
    eq_smul_div_of_polar hW μ hv₁ hμ hxgW hxhW hxgH hxhH hxgv
  have hxh0 : h v₁ - v₁ ≠ 0 := sub_ne_zero.mpr hh1
  have hc : polar Q v₁ (h v₁ - v₁) / polar Q v₁ (g v₁ - v₁) = 1 :=
    smul_eq_one_of_polar v₁ hxgrel hxhrel hxheq hxgQ hxh0
  have hv : g v₁ = h v₁ := by
    have h1 : h v₁ - v₁ = g v₁ - v₁ := by rw [hxheq, hc, one_smul]
    have h2 : h v₁ = g v₁ := by
      simpa using congrArg (· + v₁) h1
    exact h2.symm
  exact eq_on_of_eq_apply μ hv₁ hμ hgH hhH hv

end CFSG.RankThree.OrthogonalInvolutions
