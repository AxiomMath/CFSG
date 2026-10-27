module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Defs
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.AutAlternatingFour
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section

namespace CFSG.GorensteinWalter

universe u

open Equiv Equiv.Perm

private def s4_r0 : Equiv.Perm (Fin 4) :=
  Equiv.swap 0 1 * Equiv.swap 0 2

private def s4_s0 : Equiv.Perm (Fin 4) := Equiv.swap 1 2

private theorem s4_r0_three : s4_r0.IsThreeCycle := by
  exact isThreeCycle_swap_mul_swap_same (by decide) (by decide) (by decide)

private theorem s4_s0_inv_r0 : s4_s0 * s4_r0 * s4_s0⁻¹ = s4_r0⁻¹ := by
  decide

/-- Every order-three subgroup of `S₄` has an odd involution in its
normalizer. -/
public theorem firstCase_s4_normalizer_odd_involution
    (T : Subgroup (Equiv.Perm (Fin 4))) (hTcard : Nat.card T = 3) :
    ∃ s : Equiv.Perm (Fin 4), IsInvolution s ∧
      s ∈ Subgroup.normalizer (T : Set (Equiv.Perm (Fin 4))) ∧
      Equiv.Perm.sign s ≠ 1 ∧
      ∃ x : Equiv.Perm (Fin 4), x ∈ T ∧ orderOf x = 3 ∧
        s * x * s⁻¹ = x⁻¹ := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨xX, hxord⟩ := exists_prime_orderOf_dvd_card' (G := T) 3 (by rw [hTcard])
  let x : Equiv.Perm (Fin 4) := xX
  have hxorder : orderOf x = 3 := by
    simpa [x] using (Subgroup.orderOf_coe xX).trans hxord
  have hxne : x ≠ 1 := by
    intro hx1
    rw [hx1, orderOf_one] at hxorder
    omega
  have hxcycle : x.cycleType = {3} := by
    obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (by
      rw [hxorder]
      exact Nat.prime_three)
    have hsum : x.cycleType.sum ≤ 4 := by
      calc
        x.cycleType.sum = x.support.card := Equiv.Perm.sum_cycleType x
        _ ≤ Fintype.card (Fin 4) := x.support.card_le_univ
        _ = 4 := by simp
    have hn0 : n = 0 := by
      simp [hn, hxorder, Multiset.sum_replicate] at hsum
      omega
    simpa [hn0, hxorder] using hn
  have hconj : ∃ p : Equiv.Perm (Fin 4), p * x * p⁻¹ = s4_r0 := by
    have hrtype : s4_r0.cycleType = {3} := s4_r0_three.cycleType
    obtain ⟨p, hp⟩ := (isConj_iff).mp
      ((Equiv.Perm.isConj_iff_cycleType_eq).mpr (hxcycle.trans hrtype.symm))
    exact ⟨p, hp⟩
  rcases hconj with ⟨p, hp⟩
  let s := p⁻¹ * s4_s0 * p
  have hs0ne : s4_s0 ≠ 1 := by decide
  have hsI : IsInvolution s := by
    refine ⟨?_, ?_⟩
    · intro hs1
      apply hs0ne
      have h' : p⁻¹ * s4_s0 * p = 1 := by simpa [s] using hs1
      calc
        s4_s0 = p * (p⁻¹ * s4_s0 * p) * p⁻¹ := by group
        _ = p * 1 * p⁻¹ := by rw [h']
        _ = 1 := by simp
    · dsimp [s]
      have hs0sq : s4_s0 ^ 2 = 1 := by decide
      rw [pow_two]
      calc
        (p⁻¹ * s4_s0 * p) * (p⁻¹ * s4_s0 * p) =
            p⁻¹ * (s4_s0 * s4_s0) * p := by group
        _ = 1 := by rw [← pow_two, hs0sq]; simp
  have hT_eq : T = Subgroup.zpowers x := by
    have heq := Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr xX.2) (by
      rw [Nat.card_zpowers, hxorder, hTcard])
    exact heq.symm
  have hsx : s * x * s⁻¹ = x⁻¹ := by
    calc
      s * x * s⁻¹ = p⁻¹ * (s4_s0 * (p * x * p⁻¹) * s4_s0⁻¹) * p := by
        dsimp [s]
        group
      _ = p⁻¹ * (s4_s0 * s4_r0 * s4_s0⁻¹) * p := by rw [hp]
      _ = p⁻¹ * s4_r0⁻¹ * p := by rw [s4_s0_inv_r0]
      _ = x⁻¹ := by rw [← hp]; group
  have hsNorm : s ∈ Subgroup.normalizer (T : Set (Equiv.Perm (Fin 4))) := by
    rw [hT_eq, Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, hn⟩
      rw [← hn, ← conj_zpow, hsx]
      exact Subgroup.mem_zpowers_iff.mpr ⟨-n, by simp⟩
    · intro hz
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, hn⟩
      have hback : s * (s * z * s⁻¹) * s⁻¹ ∈ Subgroup.zpowers x := by
        rw [← hn, ← conj_zpow, hsx]
        exact Subgroup.mem_zpowers_iff.mpr ⟨-n, by simp⟩
      have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hsI.2
      have hEq : s * (s * z * s⁻¹) * s⁻¹ = z := by
        rw [hsinv]
        calc
          s * (s * z * s) * s = (s * s) * z * (s * s) := by group
          _ = z := by have hss : s * s = 1 := hsI.2; rw [hss]; simp
      rw [hEq] at hback
      exact hback
  refine ⟨s, hsI, hsNorm, ?_, x, xX.2, hxorder, hsx⟩
  dsimp [s]
  have hs0sign : Equiv.Perm.sign s4_s0 = -1 := by
    rw [show s4_s0 = Equiv.swap 1 2 by rfl]
    exact Equiv.Perm.sign_swap (by decide)
  rw [map_mul, map_mul, map_inv, hs0sign]
  intro h
  have := congrArg (fun z : ℤˣ => (z : ℤ)) h
  norm_num at this

/- The generator-explicit form is the convenient interface for quotient
arguments: the selected involution is known to invert the chosen generator,
not merely some generator of the order-three subgroup. -/
public theorem firstCase_s4_generator_normalizer_odd_involution
    (x : Equiv.Perm (Fin 4)) (hxorder : orderOf x = 3) :
    ∃ s : Equiv.Perm (Fin 4), IsInvolution s ∧
      s ∈ Subgroup.normalizer (Subgroup.zpowers x : Set (Equiv.Perm (Fin 4))) ∧
      Equiv.Perm.sign s ≠ 1 ∧ s * x * s⁻¹ = x⁻¹ := by
  classical
  have hxcycle : x.cycleType = {3} := by
    obtain ⟨n, hn⟩ := Equiv.Perm.cycleType_prime_order (by
      rw [hxorder]
      exact Nat.prime_three)
    have hsum : x.cycleType.sum ≤ 4 := by
      calc
        x.cycleType.sum = x.support.card := Equiv.Perm.sum_cycleType x
        _ ≤ Fintype.card (Fin 4) := x.support.card_le_univ
        _ = 4 := by simp
    have hn0 : n = 0 := by
      simp [hn, hxorder, Multiset.sum_replicate] at hsum
      omega
    simpa [hn0, hxorder] using hn
  have hconj : ∃ p : Equiv.Perm (Fin 4), p * x * p⁻¹ = s4_r0 := by
    have hrtype : s4_r0.cycleType = {3} := s4_r0_three.cycleType
    obtain ⟨p, hp⟩ := (isConj_iff).mp
      ((Equiv.Perm.isConj_iff_cycleType_eq).mpr (hxcycle.trans hrtype.symm))
    exact ⟨p, hp⟩
  rcases hconj with ⟨p, hp⟩
  let s := p⁻¹ * s4_s0 * p
  have hsI : IsInvolution s := by
    refine ⟨?_, ?_⟩
    · intro hs1
      have hs0ne : s4_s0 ≠ 1 := by decide
      apply hs0ne
      have h' : p⁻¹ * s4_s0 * p = 1 := by simpa [s] using hs1
      calc
        s4_s0 = p * (p⁻¹ * s4_s0 * p) * p⁻¹ := by group
        _ = p * 1 * p⁻¹ := by rw [h']
        _ = 1 := by simp
    · dsimp [s]
      have hs0sq : s4_s0 ^ 2 = 1 := by decide
      rw [pow_two]
      calc
        (p⁻¹ * s4_s0 * p) * (p⁻¹ * s4_s0 * p) =
            p⁻¹ * (s4_s0 * s4_s0) * p := by group
        _ = 1 := by rw [← pow_two, hs0sq]; simp
  have hsx : s * x * s⁻¹ = x⁻¹ := by
    calc
      s * x * s⁻¹ = p⁻¹ * (s4_s0 * (p * x * p⁻¹) * s4_s0⁻¹) * p := by
        dsimp [s]
        group
      _ = p⁻¹ * (s4_s0 * s4_r0 * s4_s0⁻¹) * p := by rw [hp]
      _ = p⁻¹ * s4_r0⁻¹ * p := by rw [s4_s0_inv_r0]
      _ = x⁻¹ := by rw [← hp]; group
  have hsNorm : s ∈ Subgroup.normalizer
      (Subgroup.zpowers x : Set (Equiv.Perm (Fin 4))) := by
    rw [Subgroup.mem_normalizer_iff]
    intro z
    constructor
    · intro hz
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, hn⟩
      rw [← hn, ← conj_zpow, hsx]
      exact Subgroup.mem_zpowers_iff.mpr ⟨-n, by simp⟩
    · intro hz
      rcases Subgroup.mem_zpowers_iff.mp hz with ⟨n, hn⟩
      have hback : s * (s * z * s⁻¹) * s⁻¹ ∈ Subgroup.zpowers x := by
        rw [← hn, ← conj_zpow, hsx]
        exact Subgroup.mem_zpowers_iff.mpr ⟨-n, by simp⟩
      have hsinv : s⁻¹ = s := inv_eq_of_mul_eq_one_right hsI.2
      have hEq : s * (s * z * s⁻¹) * s⁻¹ = z := by
        rw [hsinv]
        calc
          s * (s * z * s) * s = (s * s) * z * (s * s) := by group
          _ = z := by have hss : s * s = 1 := hsI.2; rw [hss]; simp
      rw [hEq] at hback
      exact hback
  refine ⟨s, hsI, hsNorm, ?_, hsx⟩
  dsimp [s]
  have hs0sign : Equiv.Perm.sign s4_s0 = -1 := by
    rw [show s4_s0 = Equiv.swap 1 2 by rfl]
    exact Equiv.Perm.sign_swap (by decide)
  rw [map_mul, map_mul, map_inv, hs0sign]
  intro h
  have := congrArg (fun z : ℤˣ => (z : ℤ)) h
  norm_num at this

end CFSG.GorensteinWalter
