module

public import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelAut

public section

namespace CFSG.StandardType

private theorem ggReflCross_of_commute {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V]
    [Module (ZMod p) V] {x y : V} {f g : Module.Dual (ZMod p) V}
    (hfx : f x = 2) (hgy : g y = 2)
    (hcomm : Commute (Module.reflection hfx) (Module.reflection hgy)) (w : V) :
    (f y * g w) • x = (g x * f w) • y := by
  have hw := congrArg (fun T : V ≃ₗ[ZMod p] V => T w)
    ((commute_iff_eq (Module.reflection hfx) (Module.reflection hgy)).mp hcomm)
  simp only [LinearEquiv.mul_apply] at hw
  have hdiff : Module.reflection hfx (Module.reflection hgy w) -
        Module.reflection hgy (Module.reflection hfx w)
      = (f y * g w) • x - (g x * f w) • y := by
    simp only [Module.reflection_apply, map_sub, map_smul]
    module
  have hzero : Module.reflection hfx (Module.reflection hgy w) -
      Module.reflection hgy (Module.reflection hfx w) = 0 := sub_eq_zero.mpr hw
  rw [hdiff] at hzero
  exact sub_eq_zero.mp hzero

theorem ggReflEq_of_commute_of_adjacent {p : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) {V : Type} [AddCommGroup V] [Module (ZMod p) V]
    {x y : V} {f g : Module.Dual (ZMod p) V} (hfx : f x = 2) (hgy : g y = 2)
    (hcomm : Commute (Module.reflection hfx) (Module.reflection hgy))
    (hadj : f y ≠ 0 ∨ g x ≠ 0) :
    Module.reflection hfx = Module.reflection hgy := by
  obtain ⟨hx0, _⟩ := ne_zero_of_apply_eq_two hp2 hfx
  obtain ⟨hy0, _⟩ := ne_zero_of_apply_eq_two hp2 hgy
  have h2 : (2 : ZMod p) ≠ 0 := zmod_two_ne_zero (p := p) hp2
  have hcross := ggReflCross_of_commute hfx hgy hcomm
  have hI : (2 * f y) • x = (f y * g x) • y := by
    have h := hcross y
    rw [hgy, mul_comm (f y) 2, mul_comm (g x) (f y)] at h
    exact h
  have hII : (f y * g x) • x = (2 * g x) • y := by
    have h := hcross x
    rw [hfx, mul_comm (g x) 2] at h
    exact h
  have ha : f y ≠ 0 := by
    rcases hadj with ha | hb
    · exact ha
    · by_contra ha0
      have h0 : (2 * g x) • y = 0 := by
        rw [ha0, zero_mul, zero_smul] at hII
        exact hII.symm
      exact hb ((mul_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hy0)).resolve_left h2)
  have hb : g x ≠ 0 := by
    rcases hadj with ha | hb
    · by_contra hb0
      have h0 : (2 * f y) • x = 0 := by
        rw [hb0, mul_zero, zero_smul] at hI
        exact hI
      exact ha ((mul_eq_zero.mp ((smul_eq_zero.mp h0).resolve_right hx0)).resolve_left h2)
    · exact hb
  let c : ZMod p := (2 * f y)⁻¹ * (f y * g x)
  have hc : c = (2 * f y)⁻¹ * (f y * g x) := rfl
  have hx : x = c • y := by
    have h := congrArg (fun z : V => ((2 * f y)⁻¹) • z) hI
    simp only [smul_smul] at h
    rw [inv_mul_cancel₀ (mul_ne_zero h2 ha), one_smul] at h
    rw [hc]
    exact h
  have hca : c * f y = 2 := by
    have h := congrArg f hx
    rw [hfx, map_smul, smul_eq_mul] at h
    exact h.symm
  have hgx : g x = 2 * c := by
    rw [hc]
    field_simp
  have hg : g = c • f := by
    ext w
    have h := hcross w
    rw [hgx, hx] at h
    simp only [smul_smul] at h
    have hs : f y * g w * c = 2 * c * f w := by
      have hsub : ((f y * g w * c) - (2 * c * f w)) • y = 0 := by
        rw [sub_smul, h, sub_self]
      exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right hy0)
    have h2eq : (2 : ZMod p) * g w = 2 * (c * f w) := by
      calc (2 : ZMod p) * g w = g w * 2 := by ring
        _ = g w * (f y * c) := by rw [mul_comm (f y) c, hca]
        _ = f y * g w * c := by ring
        _ = 2 * c * f w := hs
        _ = 2 * (c * f w) := by ring
    simpa only [LinearMap.smul_apply, smul_eq_mul] using mul_left_cancel₀ h2 h2eq
  refine LinearEquiv.ext fun w => ?_
  rw [Module.reflection_apply, Module.reflection_apply, hg, hx]
  simp only [LinearMap.smul_apply, smul_eq_mul, smul_smul]
  rw [mul_comm (f w) c]

private theorem ggReflKerEq_of_reflectionEq {p : ℕ} [Fact p.Prime] {V : Type}
    [AddCommGroup V] [Module (ZMod p) V] {x y : V} {f g : Module.Dual (ZMod p) V}
    (hfx : f x = 2) (hgy : g y = 2) (hx : x ≠ 0) (hy : y ≠ 0)
    (h : Module.reflection hfx = Module.reflection hgy) :
    LinearMap.ker f = LinearMap.ker g := by
  ext w
  rw [LinearMap.mem_ker, LinearMap.mem_ker]
  have h1 : f w = 0 ↔ Module.reflection hfx w = w := by
    rw [Module.reflection_apply, sub_eq_self, smul_eq_zero, or_iff_left hx]
  have h2 : g w = 0 ↔ Module.reflection hgy w = w := by
    rw [Module.reflection_apply, sub_eq_self, smul_eq_zero, or_iff_left hy]
  have hw : Module.reflection hfx w = Module.reflection hgy w := congrArg (fun T => T w) h
  rw [h1, h2, ← hw]

theorem exists_not_commute_reflection_of_connected {p : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {V : Type} [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    {ι : Type} [Nonempty ι] (f : ι → Module.Dual (ZMod p) V) (v : ι → V)
    (hfv : ∀ i, f i (v i) = 2)
    (hconn : ∀ S : Set ι, S.Nonempty →
      (∀ i j, (f i (v j) ≠ 0 ∨ f j (v i) ≠ 0) → (i ∈ S ↔ j ∈ S)) → S = Set.univ)
    (hcodim : Module.finrank (ZMod p) ↥(⨅ i, LinearMap.ker (f i) : Submodule (ZMod p) V) + 2 ≤
      Module.finrank (ZMod p) V) :
    ∃ i j, ¬ Commute (Module.reflection (hfv i)) (Module.reflection (hfv j)) := by
  by_contra hcon
  push Not at hcon
  let i0 : ι := Classical.choice (inferInstance : Nonempty ι)
  let S : Set ι := {j | Module.reflection (hfv j) = Module.reflection (hfv i0)}
  have hSne : S.Nonempty := ⟨i0, rfl⟩
  have hSclosed : ∀ i j, (f i (v j) ≠ 0 ∨ f j (v i) ≠ 0) → (i ∈ S ↔ j ∈ S) := by
    intro i j hadj
    have heq : Module.reflection (hfv i) = Module.reflection (hfv j) :=
      ggReflEq_of_commute_of_adjacent hp2 (hfv i) (hfv j) (hcon i j) hadj
    constructor
    · intro hi; exact heq.symm.trans hi
    · intro hj; exact heq.trans hj
  have hSuniv : S = Set.univ := hconn S hSne hSclosed
  have hjS : ∀ j, Module.reflection (hfv j) = Module.reflection (hfv i0) := by
    intro j
    have h : j ∈ S := by rw [hSuniv]; exact Set.mem_univ j
    simpa only [S, Set.mem_setOf_eq] using h
  have hker : ∀ j, LinearMap.ker (f j) = LinearMap.ker (f i0) := by
    intro j
    exact ggReflKerEq_of_reflectionEq (hfv j) (hfv i0)
      (ne_zero_of_apply_eq_two hp2 (hfv j)).1 (ne_zero_of_apply_eq_two hp2 (hfv i0)).1 (hjS j)
  have hinf : (⨅ j, LinearMap.ker (f j)) = LinearMap.ker (f i0) := by
    refine le_antisymm (iInf_le _ i0) (le_iInf fun j => ?_)
    rw [hker j]
  have hcodim' : Module.finrank (ZMod p) ↥(LinearMap.ker (f i0)) + 2 ≤
      Module.finrank (ZMod p) V := by
    rw [hinf] at hcodim
    exact hcodim
  have hfin := Module.Dual.finrank_ker_add_one_of_ne_zero (K := ZMod p) (f := f i0)
    (ne_zero_of_apply_eq_two hp2 (hfv i0)).2
  omega

end CFSG.StandardType

end
