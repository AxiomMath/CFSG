module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.L3YC.CommLift
public import CFSG.Quasithin.EmptyFaithful.SBd5Dec
public import CFSG.Quasithin.Background.C4Defs

public section

namespace CFSG.Quasithin

open CFSG.Open hiding StatedSL StatedSp
open CFSG.LieType.BorelTits
open CFSG.Assembly.LowTwoRank (StatedSL)
open scoped commutatorElement

namespace Stellmacher.L3YC

section Lift

variable {G : Type} [Group G] [Finite G]

theorem card_eq_of_isLnTwoQuot {L : Subgroup G} (hq : IsLnTwoQuot L 3) :
    ∃ j : ℕ, Nat.card ↥L = 168 * 2 ^ j := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨j, hj⟩ := IsPGroup.iff_card.mp (CFSG.pCore_isPGroup (p := 2) (G := ↥L))
  refine ⟨j, ?_⟩
  rw [(CFSG.pCore 2 ↥L).card_eq_card_quotient_mul_card_subgroup, SBd5.card_quot_of_isLnTwoQuot hq, hj]

omit [Finite G] in
theorem exists_mem_ker_of_mem_pCoreOf {L : Subgroup G} {F : Type} [Field F]
    {α : ↥L →* ↥(StatedSL 3 F)} (hα : IsModO2Surj L α) {p : G} (hp : p ∈ pCoreOf 2 L) :
    ∃ p' : ↥L, (p' : G) = p ∧ α p' = 1 := by
  obtain ⟨o, ho, hoe⟩ := Subgroup.mem_map.mp hp
  refine ⟨o, hoe, ?_⟩
  have : o ∈ α.ker := by rw [hα.2]; exact ho
  exact this

theorem exists_order_three_lift {L : Subgroup G} (hq : IsLnTwoQuot L 3) {F : Type} [Field F]
    (α : ↥L →* ↥(StatedSL 3 F)) (hα : IsModO2Surj L α) {y : G} (hy : y ∈ N0 L)
    (hy3 : y ^ 3 = 1) {xb : ↥(StatedSL 3 F)} (hxb : orderOf xb = 3) :
    ∃ x : ↥L, orderOf (x : G) = 3 ∧ y * (x : G) = (x : G) * y ∧ α x = xb := by
  obtain ⟨l, hl⟩ := hα.1 xb
  obtain ⟨p, hp, hpc⟩ := exists_mem_centralizer_coset hy hy3 l.2
  obtain ⟨p', hp'e, hp'1⟩ := exists_mem_ker_of_mem_pCoreOf hα hp
  set l' : ↥L := l * p' with hl'
  have hαl' : α l' = xb := by rw [hl', map_mul, hl, hp'1, mul_one]
  have hcomm : y * (l' : G) = (l' : G) * y := by
    rw [hl']
    simpa [hp'e] using hpc
  obtain ⟨j, hj⟩ := card_eq_of_isLnTwoQuot hq
  have h3n : 3 ∣ orderOf l' := by
    have := orderOf_map_dvd α l'
    rwa [hαl', hxb] at this
  obtain ⟨m, hm⟩ := h3n
  have hnc : orderOf l' ∣ 168 * 2 ^ j := hj ▸ orderOf_dvd_natCard l'
  have hm3 : ¬ 3 ∣ m := by
    intro h3m
    obtain ⟨m', rfl⟩ := h3m
    have h9 : 9 ∣ 168 * 2 ^ j := by
      refine dvd_trans ⟨m', ?_⟩ hnc
      rw [hm]; ring
    have hcop : Nat.Coprime 9 (2 ^ j) := Nat.Coprime.pow_right j (by norm_num)
    have := hcop.dvd_of_dvd_mul_right h9
    omega
  have hmm : (m * m) % 3 = 1 := by
    have : m % 3 = 1 ∨ m % 3 = 2 := by omega
    rcases this with h | h <;> simp [Nat.mul_mod, h]
  set x : ↥L := l' ^ (m * m) with hx
  have hαx : α x = xb := by
    rw [hx, map_pow, hαl', ← pow_mod_orderOf, hxb, hmm, pow_one]
  have hx3 : x ^ 3 = 1 := by
    rw [hx, ← pow_mul]
    have : m * m * 3 = orderOf l' * m := by rw [hm]; ring
    rw [this, pow_mul, pow_orderOf_eq_one, one_pow]
  have hx1 : x ≠ 1 := by
    intro h
    rw [h, map_one] at hαx
    have : orderOf xb = 1 := by rw [← hαx]; exact orderOf_one
    omega
  refine ⟨x, ?_, ?_, hαx⟩
  · rw [Subgroup.orderOf_coe]
    exact orderOf_eq_prime hx3 hx1
  · have : Commute y (l' : G) := hcomm
    have h2 := this.pow_right (m * m)
    simpa [hx] using h2.eq

end Lift

end Stellmacher.L3YC

end CFSG.Quasithin
