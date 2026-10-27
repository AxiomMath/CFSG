module

public import CFSG.LocalAnalysis.WeakClosure81.W172Arith
public import CFSG.LocalAnalysis.WeakClosure81.W172Count
public import CFSG.LocalAnalysis.WeakClosure81.W172ModMain

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.SignalizerFunctorTheorem.Quadratic Subgroup
open scoped commutatorElement

variable {W : Type} [AddCommGroup W] [Module (ZMod 2) W] [Finite W]

theorem w172_false_of_orbit_bound {p : ℕ} {X : Subgroup (LGL 2 W)} {d : LGL 2 W}
    {S : Subgroup (LGL 2 W)} (hset : W172InvSetup p X d S) (hnt : ∃ x ∈ X, d * x * d⁻¹ ≠ x)
    (hS : IsPGroup 2 S) {k c : ℕ} (hk : 1 ≤ k) (hc : 2 * k ≤ c)
    (hD1 : ∀ x ∈ X, Module.finrank (ZMod 2) ↥(commSub (zpowers (x⁻¹ * d * x))) ≤ k)
    (horb : ∀ y ∈ X, d * y * d⁻¹ = y⁻¹ → y ≠ 1 →
      2 ^ c ≤ (Subgroup.normalizer (Subgroup.zpowers y : Set (LGL 2 W))).relIndex S) :
    False := by
  classical
  obtain ⟨Y, hY⟩ := w172_exists_minInv hset hnt
  obtain ⟨a, ha1, hcard⟩ := w172_minInv_card hY
  have hp := hset.prime
  have hp2 := hset.odd
  have hexp := w172_minInv_exp hY
  have hcl := w172_minInv_class_two hY
  have hZ : (⁅Y, Y⁆ : Subgroup (LGL 2 W)) ≠ ⊥ → ∀ z ∈ Y, (∀ y ∈ Y, y * z = z * y) →
      z ∈ (⁅Y, Y⁆ : Subgroup (LGL 2 W)) := fun hne => w172_minInv_center hY hne
  have horb' : ∀ y ∈ W172Inv d Y, y ≠ 1 →
      2 ^ c ≤ (Subgroup.normalizer (Subgroup.zpowers y : Set (LGL 2 W))).relIndex S :=
    fun y hy hy1 => horb y (hY.le hy.1) hy.2 hy1
  have hdvd := w172_two_pow_dvd_geom_sum hY hS hcard horb'
  have hdim : ∀ z ∈ W172Inv d Y,
      Module.finrank (ZMod 2) ↥(commSub (zpowers z)) ≤ 2 * k := by
    intro z hz
    have h1 := w172_finrank_commSub_le_add (d := d) (y := z) (n := p) hset.sq
      (hp.odd_of_ne_two hp2) (hexp z hz.1) hz.2
    have h2 : Module.finrank (ZMod 2) ↥(commSub (zpowers d)) ≤ k := by
      have := hD1 1 (one_mem X)
      rwa [inv_one, one_mul, mul_one] at this
    have h3 := hD1 z (hY.le hz.1)
    omega
  have hmov : 2 ≤ a → ∃ z ∈ W172Inv d Y,
      (a = 2 → 2 * orderOf (2 : ZMod p) ≤ 2 * k) ∧
      (3 ≤ a → 16 * a * orderOf (2 : ZMod p) ≤ 27 * (2 * k)) := by
    intro ha2
    obtain ⟨y, hyY, -, hbd⟩ := w172_mod_exists_moving hp hp2 hexp hcl hZ hcard ha2
    obtain ⟨z, ⟨hzI, hzc⟩, -⟩ := w172_minInv_transversal hY y hyY
    have hz : y⁻¹ * z ∈ (⁅Y, Y⁆ : Subgroup (LGL 2 W)) := by
      have := (⁅Y, Y⁆ : Subgroup (LGL 2 W)).inv_mem hzc
      simpa [mul_inv_rev] using this
    obtain ⟨hb2, hb3⟩ := hbd z hzI.1 hz
    exact ⟨z, hzI, fun h => (hb2 h).trans (hdim z hzI),
      fun h => (hb3 h).trans (Nat.mul_le_mul_left 27 (hdim z hzI))⟩
  refine w172_arith_false hp hp2 ha1 hk hc hdvd ?_ ?_
  · intro h2
    obtain ⟨z, -, hb, -⟩ := hmov (by omega)
    exact hb h2
  · intro h3
    obtain ⟨z, -, -, hb⟩ := hmov (by omega)
    exact hb h3

end CFSG.LocalAnalysis.WeakClosure81

end
