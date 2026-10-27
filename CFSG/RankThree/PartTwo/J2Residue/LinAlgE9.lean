module

public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.RankThree.PartTwo.J2Residue

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem finrank_ne_finrank_ker_add_one (h3 : (3 : K) ≠ 0) [FiniteDimensional K V]
    {g h : V →ₗ[K] V} (hg : g * g * g = 1) (hh : h * g = g * g * h) (hhu : IsUnit h) :
    Module.finrank K V ≠ Module.finrank K (LinearMap.ker (g - 1)) + 1 := by
  classical
  intro hdim
  let N : Module.End K V := g - 1
  have hNker : N.ker = LinearMap.ker (g - 1) := rfl
  have hW1 : Module.finrank K N.range = 1 := by
    have hrn := LinearMap.finrank_range_add_finrank_ker N
    rw [hNker, hdim, add_comm (Module.finrank K (LinearMap.ker (g - 1)))] at hrn
    exact Nat.add_right_cancel hrn
  have hWne : N.range ≠ ⊥ := by
    intro hbot
    have h0 : Module.finrank K N.range = 0 := by rw [hbot]; simp
    rw [h0] at hW1
    exact Nat.zero_ne_one hW1
  obtain ⟨w, hwW, hw0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hWne
  have hgW : ∀ x ∈ N.range, g x ∈ N.range := by
    rintro x ⟨y, rfl⟩
    exact ⟨g y, by
      simp only [N, LinearMap.sub_apply, Module.End.one_apply, LinearMap.map_sub]⟩
  have hh_apply : ∀ y : V, h (g y) = g (g (h y)) := by
    intro y
    have happ := congrArg (fun f : Module.End K V => f y) hh
    simpa [Module.End.mul_apply] using happ
  have hhW : ∀ x ∈ N.range, h x ∈ N.range := by
    rintro x ⟨y, rfl⟩
    refine ⟨(g + 1) (h y), ?_⟩
    have hfac : (g - 1) * (g + 1) = g * g - 1 := by noncomm_ring
    calc
      N ((g + 1) (h y)) = ((g - 1) * (g + 1)) (h y) := rfl
      _ = (g * g - 1) (h y) := by rw [hfac]
      _ = g (g (h y)) - h y := by
        rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.one_apply]
      _ = h (g y) - h y := by rw [← hh_apply y]
      _ = h (g y - y) := (LinearMap.map_sub h (g y) y).symm
      _ = h (N y) := rfl
  have hinj : Function.Injective h := ((Module.End.isUnit_iff h).mp hhu).1
  let w' : N.range := ⟨w, hwW⟩
  have hw'0 : w' ≠ 0 := by
    intro hzero
    have hcoe : (w' : V) = 0 := by
      rw [hzero]
      rfl
    exact hw0 hcoe
  obtain ⟨a, ha⟩ := exists_smul_eq_of_finrank_eq_one hW1 hw'0 (⟨g w, hgW w hwW⟩ : N.range)
  obtain ⟨b, hb⟩ := exists_smul_eq_of_finrank_eq_one hW1 hw'0 (⟨h w, hhW w hwW⟩ : N.range)
  have haV : a • w = g w := by
    have := congrArg Subtype.val ha
    simpa using this
  have hbV : b • w = h w := by
    have := congrArg Subtype.val hb
    simpa using this
  have hgw : g w = a • w := haV.symm
  have hg2w : g (g w) = a ^ 2 • w := by
    rw [hgw, LinearMap.map_smul, hgw]
    module
  have hg3w' : g (g (g w)) = a ^ 3 • w := by
    rw [hg2w, LinearMap.map_smul, hgw]
    module
  have hg3w : g (g (g w)) = w := by
    have happ := congrArg (fun f : Module.End K V => f w) hg
    simpa [Module.End.mul_apply] using happ
  have ha3 : a ^ 3 = 1 := by
    refine smul_left_injective K hw0 ?_
    change a ^ 3 • w = 1 • w
    rw [← hg3w', hg3w, one_smul]
  have hrel : a * b = a ^ 2 * b := by
    have h1 : h (g w) = (a * b) • w := by
      rw [hgw, LinearMap.map_smul, ← hbV]
      module
    have h2 : g (g (h w)) = (a ^ 2 * b) • w := by
      rw [← hbV, LinearMap.map_smul, LinearMap.map_smul, hg2w]
      module
    have h3eq : h (g w) = g (g (h w)) := hh_apply w
    rw [h1, h2] at h3eq
    exact smul_left_injective K hw0 h3eq
  have hb0 : b ≠ 0 := by
    intro hbzero
    have hwzero : b • w = 0 := by rw [hbzero, zero_smul]
    rw [hbV] at hwzero
    exact hw0 (hinj (by simpa using hwzero))
  have ha2 : a ^ 2 = a := (mul_right_cancel₀ hb0 hrel).symm
  have ha1 : a = 1 := by
    have h3a : a ^ 3 = a := by
      calc
        a ^ 3 = a ^ 2 * a := by rw [pow_succ]
        _ = a * a := by rw [ha2]
        _ = a ^ 2 := (sq a).symm
        _ = a := ha2
    exact h3a.symm.trans ha3
  have hgw_eq : g w = w := by
    rw [hgw, ha1, one_smul]
  have hNw : N w = 0 := by
    simp [N, hgw_eq]
  have hN2 : N * N = 0 := by
    ext y
    have hy : N y ∈ N.range := ⟨y, rfl⟩
    obtain ⟨c, hc⟩ := exists_smul_eq_of_finrank_eq_one hW1 hw'0 (⟨N y, hy⟩ : N.range)
    have hcV : c • w = N y := by
      have := congrArg Subtype.val hc
      simpa using this
    calc
      (N * N) y = N (N y) := by rw [Module.End.mul_apply]
      _ = N (c • w) := by rw [hcV]
      _ = c • N w := by rw [LinearMap.map_smul]
      _ = 0 := by rw [hNw, smul_zero]
  have hg_eq : g = 1 + N := by
    change g = 1 + (g - 1)
    rw [add_comm, sub_add_cancel]
  have hgN_apply : ∀ y : V, g y = y + N y := by
    intro y
    have happ := congrArg (fun f : Module.End K V => f y) hg_eq
    simpa [LinearMap.add_apply, Module.End.one_apply] using happ
  have hgNy : ∀ y : V, g (N y) = N y := by
    intro y
    have hNN : N (N y) = 0 := by
      have happ := congrArg (fun f : Module.End K V => f y) hN2
      simpa [Module.End.mul_apply] using happ
    rw [hgN_apply (N y), hNN, add_zero]
  have hg2_apply : ∀ y : V, g (g y) = y + (2 : K) • N y := by
    intro y
    rw [hgN_apply y, LinearMap.map_add, hgNy y, hgN_apply y]
    module
  have hg3_apply : ∀ y : V, g (g (g y)) = y + (3 : K) • N y := by
    intro y
    rw [hg2_apply y, LinearMap.map_add, LinearMap.map_smul, hgNy y, hgN_apply y]
    module
  have hg3y : ∀ y : V, g (g (g y)) = y := by
    intro y
    have happ := congrArg (fun f : Module.End K V => f y) hg
    simpa [Module.End.mul_apply] using happ
  have hNzero_apply : ∀ y : V, N y = 0 := by
    intro y
    have h := hg3_apply y
    rw [hg3y y] at h
    have hzero : (3 : K) • N y = 0 := add_eq_left.mp h.symm
    exact (smul_eq_zero.mp hzero).resolve_left h3
  have hNzero : N = 0 := LinearMap.ext hNzero_apply
  obtain ⟨y, hy⟩ := hwW
  rw [hNzero] at hy
  exact hw0 (by simpa using hy.symm)

end CFSG.RankThree.PartTwo.J2Residue
