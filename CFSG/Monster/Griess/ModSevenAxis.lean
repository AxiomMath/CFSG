module

public import CFSG.Monster.Griess.ModP.Lattice
public import CFSG.Monster.Griess.AutFinite
import CFSG.Monster.Visible.Action
import Mathlib.Tactic.NormNum.Prime

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.Griess.ModP

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin

variable {p : ℕ} [hp : Fact p.Prime]

theorem hensel_identity {u v : SpaceB} (hu : gmul u u = (16 : ℚ) • u)
    (hv : gmul v v = (16 : ℚ) • v)
    (hm : ∀ x, gmul u (cubicQ (gmul u) x) - (16 : ℚ) • cubicQ (gmul u) x = 0) :
    (1920 : ℚ) • (v - u) = -(2 : ℚ)⁻¹ • (gmul u (gmul u (gmul u (gmul (v - u) (v - u)))) -
      (25 / 2 : ℚ) • gmul u (gmul u (gmul (v - u) (v - u))) -
      (26 : ℚ) • gmul u (gmul (v - u) (v - u)) - (240 : ℚ) • gmul (v - u) (v - u)) := by
  obtain ⟨d, rfl⟩ : ∃ d, v = u + d := ⟨v - u, by abel⟩
  rw [add_sub_cancel_left]
  have e : gmul (u + d) (u + d) = gmul u u + (2 : ℚ) • gmul u d + gmul d d := by
    simp only [map_add, LinearMap.add_apply]
    rw [gmul_comm d u, two_smul]
    abel
  rw [hv, hu] at e
  have hdd : gmul d d = (16 : ℚ) • d - (2 : ℚ) • gmul u d := by
    linear_combination (norm := module) (-1 : ℚ) • e
  have hq := hm d
  rw [cubicQ_apply] at hq
  simp only [map_sub, map_add, map_smul] at hq
  rw [hdd]
  simp only [map_sub, map_smul]
  linear_combination (norm := module) (-1 : ℚ) • hq

theorem ne_two_of_not_dvd (hp1920 : ¬ p ∣ 1920) : p ≠ 2 := by
  rintro rfl
  exact hp1920 (by norm_num)

theorem eq_of_sub_mem_LatP (hp1920 : ¬ p ∣ 1920) {u v : SpaceB} (hu0 : u ∈ LatP p 0)
    (hu : gmul u u = (16 : ℚ) • u) (hv : gmul v v = (16 : ℚ) • v)
    (hm : ∀ x, gmul u (cubicQ (gmul u) x) - (16 : ℚ) • cubicQ (gmul u) x = 0)
    (hd : v - u ∈ LatP p 1) : u = v := by
  have hp2 := ne_two_of_not_dvd hp1920
  have hn2 : ¬ p ∣ 2 := fun h => hp1920 (h.trans (by norm_num))
  have hL : ∀ {j : ℕ} {x : SpaceB}, x ∈ LatP p j → gmul u x ∈ LatP p j := fun hx =>
    gmul_mem_LatP_of_mem_zero hp2 hu0 hx
  have h25 : (25 / 2 : ℚ) ∈ ratLocal p := by
    have h := intCast_div_mem_ratLocal p 25 (b := 2) (by exact_mod_cast hn2)
    push_cast at h
    exact h
  have h26 : (26 : ℚ) ∈ ratLocal p := by exact_mod_cast natCast_mem_ratLocal p 26
  have h240 : (240 : ℚ) ∈ ratLocal p := by exact_mod_cast natCast_mem_ratLocal p 240
  have hhalf : -(2 : ℚ)⁻¹ ∈ ratLocal p := by
    have h := inv_natCast_mem_ratLocal p hn2
    exact neg_mem (by exact_mod_cast h)
  have h1920 : (1920 : ℚ)⁻¹ ∈ ratLocal p := by
    have h := inv_natCast_mem_ratLocal p hp1920
    exact_mod_cast h
  have key := hensel_identity hu hv hm
  have hstep : ∀ k, v - u ∈ LatP p (k + 1) → v - u ∈ LatP p (k + 2) := by
    intro k hk
    have hw : gmul (v - u) (v - u) ∈ LatP p (k + 2) :=
      LatP_anti (by omega) (gmul_mem_LatP hp2 hk hk)
    have hR := sub_mem (sub_mem (sub_mem (hL (hL (hL hw))) (smul_mem_LatP h25 (hL (hL hw))))
      (smul_mem_LatP h26 (hL hw))) (smul_mem_LatP h240 hw)
    have h1 : (1920 : ℚ) • (v - u) ∈ LatP p (k + 2) := by
      rw [key]
      exact smul_mem_LatP hhalf hR
    have h2 := smul_mem_LatP h1920 h1
    rwa [smul_smul, inv_mul_cancel₀ (by norm_num : (1920 : ℚ) ≠ 0), one_smul] at h2
  have hall' : ∀ k, v - u ∈ LatP p (k + 1) := by
    intro k
    induction k with
    | zero => exact hd
    | succ k ih => exact hstep k ih
  have hall : ∀ k, v - u ∈ LatP p k := fun k => LatP_anti (Nat.le_succ k) (hall' k)
  exact (sub_eq_zero.1 (eq_zero_of_forall_mem_LatP hall)).symm

theorem axis_mem_BR {r : Q} (hr : IsShortCoord (coordOf r)) : axis r ∈ BR := by
  have h32 : (32 : ℚ)⁻¹ ∈ dyadic := by
    have e : (32 : ℚ)⁻¹ = (2 : ℚ)⁻¹ ^ 5 := by norm_num
    rw [e]
    exact pow_mem inv_two_mem_dyadic' 5
  refine mem_BR_iff.2 ⟨fun i j => ?_, fun c => ?_, fun j i => ?_⟩
  · have e : ((axis r).1 : Matrix (Fin 24) (Fin 24) ℚ) i j = Am (axis r) i j := rfl
    rw [e, Am_axis, axisE_coe hr]
    simp only [Matrix.smul_apply, Matrix.vecMulVec_apply, smul_eq_mul]
    exact mul_mem two_mem_dyadic' (mul_mem h32 (mul_mem (uQ_mem_dyadic _ i) (uQ_mem_dyadic _ j)))
  · have e : (axis r).2.1 c = xs (axis r) c := rfl
    rw [e, xs_axis, Pi.neg_apply, Pi.smul_apply, smul_eq_mul]
    exact neg_mem (mul_mem two_mem_dyadic' (Visible.Xlift_apply_mem_dyadic r c))
  · have e : (axis r).2.2 j i = Nm (axis r) j i := rfl
    rw [e, Nm_axis]
    exact zero_mem _

theorem quartic_map_axis {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : IsAlgAut g) {r : Q}
    (hr : IsShortCoord (coordOf r)) (x : SpaceB) :
    gmul (g (axis r)) (cubicQ (gmul (g (axis r))) x) -
      (16 : ℚ) • cubicQ (gmul (g (axis r))) x = 0 := by
  have hL : ∀ y, gmul (g (axis r)) y = g (gmul (axis r) (g.symm y)) := fun y => by
    rw [hg, g.apply_symm_apply]
  have hC : ∀ y, cubicQ (gmul (g (axis r))) y = g (cubicQ (gmul (axis r)) (g.symm y)) := by
    intro y
    simp only [cubicQ_apply, hL, LinearEquiv.symm_apply_apply, map_sub, map_add, map_smul]
  rw [hC, hL, LinearEquiv.symm_apply_apply, ← map_smul, ← map_sub, quartic_axis hr, map_zero]

theorem gmul_map_axis_self {g : SpaceB ≃ₗ[ℚ] SpaceB} (hg : IsAlgAut g) {r : Q}
    (hr : IsShortCoord (coordOf r)) : gmul (g (axis r)) (g (axis r)) = (16 : ℚ) • g (axis r) := by
  rw [← hg, axis_mul_self hr, map_smul]

theorem eq_axis_of_sub_mem_LatP (hp1920 : ¬ p ∣ 1920) {g h : SpaceB ≃ₗ[ℚ] SpaceB}
    (hg : g ∈ AutO) (hh : h ∈ AutO) (hgB : ∀ x ∈ BR, g x ∈ BR) {r₁ r₂ : Q}
    (hr₁ : IsShortCoord (coordOf r₁)) (hr₂ : IsShortCoord (coordOf r₂))
    (hd : g (axis r₁) - h (axis r₂) ∈ LatP p 1) : g (axis r₁) = h (axis r₂) := by
  have hp2 := ne_two_of_not_dvd hp1920
  have hu0 : g (axis r₁) ∈ LatP p 0 :=
    mem_LatP_zero_of_mem_BR hp2 (hgB _ (axis_mem_BR hr₁))
  have hd' : h (axis r₂) - g (axis r₁) ∈ LatP p 1 := by
    rw [← neg_sub]
    exact neg_mem hd
  exact eq_of_sub_mem_LatP hp1920 hu0 (gmul_map_axis_self hg.1 hr₁)
    (gmul_map_axis_self hh.1 hr₂) (quartic_map_axis hg.1 hr₁) hd'

end CFSG.Monster.Griess.ModP

namespace CFSG.Monster.Griess.ModSeven

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.Griess.ModP

instance fact_prime_seven : Fact (Nat.Prime 7) := ⟨by norm_num⟩

theorem eq_axis_of_cong7 {g h : SpaceB ≃ₗ[ℚ] SpaceB} (hg : g ∈ AutO) (hh : h ∈ AutO)
    (hgB : ∀ x ∈ BR, g x ∈ BR) {r₁ r₂ : Q} (hr₁ : IsShortCoord (coordOf r₁))
    (hr₂ : IsShortCoord (coordOf r₂))
    (hd : ∀ i, basisB.repr (g (axis r₁) - h (axis r₂)) i / 7 ∈ ratLocal 7) :
    g (axis r₁) = h (axis r₂) :=
  eq_axis_of_sub_mem_LatP (p := 7) (by norm_num) hg hh hgB hr₁ hr₂ fun i => by
    rw [pow_one]
    exact_mod_cast hd i

end CFSG.Monster.Griess.ModSeven
