module

public import Mathlib.LinearAlgebra.Matrix.CharP
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Coeff
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas

public section

namespace CFSG.RankThree.PartTwo.Sec8.Hering88N

open Polynomial

theorem pow_four_eq_one_of_two_power_le_four {F : Type*} [Field F] [CharP F 2] {n : ℕ}
    (hn : n ≤ 4) {u : Matrix (Fin n) (Fin n) F} (h2 : ∃ k : ℕ, u ^ 2 ^ k = 1) : u ^ 4 = 1 := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases Nat.eq_zero_or_pos n with rfl | hpos
  · exact Subsingleton.elim _ _
  haveI : NeZero n := ⟨hpos.ne'⟩
  obtain ⟨k, hk⟩ := h2
  have hN : IsNilpotent (u - 1) := ⟨2 ^ k, by
    rw [sub_pow_char_pow_of_commute (p := 2) (h := Commute.one_right u), one_pow, hk, sub_self]⟩
  have hcp : (u - 1).charpoly = X ^ n := by
    have h := (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN).eq_zero
    simpa [sub_eq_zero] using h
  have hn0 : (u - 1) ^ n = 0 := by
    have h := Matrix.aeval_self_charpoly (u - 1)
    rw [hcp] at h
    simpa using h
  have h4 : (u - 1) ^ 2 ^ 2 = 0 := by
    rw [show 2 ^ 2 = n + (4 - n) by omega, pow_add, hn0, zero_mul]
  have e : (u - 1) ^ 2 ^ 2 = u ^ 2 ^ 2 - 1 := by
    rw [sub_pow_char_pow_of_commute (p := 2) (h := Commute.one_right u), one_pow]
  rw [e, sub_eq_zero] at h4
  simpa using h4

theorem isCompl_ker_sub_one_ker_sq_add_add_one {K V : Type*} [Field K] [AddCommGroup V]
    [Module K V] (h3 : (3 : K) ≠ 0) (g : Module.End K V) (hg : g ^ 3 = 1) :
    IsCompl (LinearMap.ker (g - 1)) (LinearMap.ker (g ^ 2 + g + 1)) := by
  have hg3v : ∀ v, g (g (g v)) = v := fun v => by
    have := congrArg (fun f : Module.End K V => f v) hg
    simpa [pow_succ, Module.End.mul_apply] using this
  have hsq : ∀ v, (g ^ 2) v = g (g v) := fun v => by simp [pow_two, Module.End.mul_apply]
  constructor
  · rw [disjoint_iff_inf_le]
    rintro v ⟨h1, h2⟩
    have h1' : g v = v := by
      have := LinearMap.mem_ker.mp h1
      rwa [LinearMap.sub_apply, Module.End.one_apply, sub_eq_zero] at this
    have h2' := LinearMap.mem_ker.mp h2
    rw [LinearMap.add_apply, LinearMap.add_apply, Module.End.one_apply, hsq, h1', h1'] at h2'
    have h3v : (3 : K) • v = 0 := by rw [← h2']; module
    exact (smul_eq_zero.mp h3v).resolve_left h3
  · rw [codisjoint_iff_le_sup]
    intro v _
    set w : V := (3 : K)⁻¹ • (g (g v) + g v + v) with hw
    have hgw : g w = w := by
      rw [hw, map_smul, map_add, map_add, hg3v]; congr 1; abel
    refine Submodule.mem_sup.mpr ⟨w, ?_, v - w, ?_, by abel⟩
    · simp [LinearMap.mem_ker, hgw]
    · simp only [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply, hsq, map_sub, hgw]
      rw [hw, smul_add, smul_add]
      have e : (3 : K)⁻¹ • g (g v) + (3 : K)⁻¹ • g v + (3 : K)⁻¹ • v = w := by
        rw [hw, smul_add, smul_add]
      rw [e]
      have : (3 : K) • w = g (g v) + g v + v := by rw [hw, smul_smul, mul_inv_cancel₀ h3, one_smul]
      rw [← this]; module

theorem pow_four_eq_zero_of_isNilpotent {K V : Type*} [Field K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (hdim : Module.finrank K V ≤ 4) (N : Module.End K V)
    (hN : IsNilpotent N) : N ^ 4 = 0 := by
  obtain ⟨n, hn⟩ := hN
  have h : N ^ Module.finrank K V = 0 := by
    have := Module.End.ker_pow_le_ker_pow_finrank N n
    rw [hn, LinearMap.ker_zero] at this
    exact LinearMap.ker_eq_top.mp (top_unique this)
  rw [show 4 = (4 - Module.finrank K V) + Module.finrank K V by omega, pow_add, h, mul_zero]

end CFSG.RankThree.PartTwo.Sec8.Hering88N
