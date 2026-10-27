module

public import CFSG.Quasithin.EmptyFaithful.R3cBlocks

public section

namespace CFSG.Quasithin.A38c7

open CFSG.Assembly.LowTwoRank

theorem card_statedSL_three {F : Type} [Field F] [Finite F] :
    Nat.card ↥(StatedSL 3 F) = Nat.card F ^ 3 * ((Nat.card F ^ 2 - 1) * (Nat.card F ^ 3 - 1)) :=
  CFSG.Open.StatedAPI.card_statedSL_three F

theorem card_statedSL_five : Nat.card ↥(StatedSL 5 (ZMod 2)) = 9999360 :=
  CFSG.Open.StatedAPI.card_statedSL_five_zmod_two

theorem dvd_27_card_statedSL_three {F : Type} [Field F] [Finite F] {n : ℕ} (hn : Even n)
    (hcard : Nat.card F = 2 ^ n) : 27 ∣ Nat.card ↥(StatedSL 3 F) := by
  rw [card_statedSL_three, hcard]
  obtain ⟨m, hm⟩ := hn
  have h1 : 2 ^ n % 3 = 1 := by
    rw [hm, ← two_mul, pow_mul]
    norm_num [Nat.pow_mod]
  obtain ⟨r, hr⟩ : ∃ r, 2 ^ n = 3 * r + 1 := ⟨2 ^ n / 3, by omega⟩
  rw [hr]
  have e2 : (3 * r + 1) ^ 2 - 1 = 3 * (r * (3 * r + 2)) := Nat.sub_eq_of_eq_add (by ring)
  have e3 : (3 * r + 1) ^ 3 - 1 = 9 * (r * (3 * r ^ 2 + 3 * r + 1)) :=
    Nat.sub_eq_of_eq_add (by ring)
  rw [e2, e3]
  exact ⟨(3 * r + 1) ^ 3 * (r * (3 * r + 2)) * (r * (3 * r ^ 2 + 3 * r + 1)), by ring⟩

section Quot5

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem card_eq_of_quot5 (hq : IsLnTwoQuot L 5) : ∃ k : ℕ, Nat.card ↥L = 2 ^ k * 9999360 := by
  obtain ⟨e⟩ := hq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := by
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hN
  refine ⟨k, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L),
    Nat.card_congr e.toEquiv, card_statedSL_five, hk]
  ring

theorem not_dvd_27_card_of_quot5 (hq : IsLnTwoQuot L 5) : ¬ 27 ∣ Nat.card ↥L := by
  obtain ⟨k, hk⟩ := card_eq_of_quot5 hq
  rw [hk]
  intro h
  have hcop : Nat.Coprime 27 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have := hcop.dvd_of_dvd_mul_left h
  omega

theorem two_le_pRank_of_quot5 (hq : IsLnTwoQuot L 5) : 2 ≤ CFSG.Open.pRank 3 L := by
  obtain ⟨e⟩ := hq
  have h1 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSL 5 (ZMod 2))) :=
    R3c.two_le_pRank_three_statedSL_five_two
  have e' : (↥L ⧸ CFSG.Open.pCore 2 ↥L) ≃* ↥(StatedSL 5 (ZMod 2)) :=
    (QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥L 2).symm).trans e
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e'] at h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.pRank_quotient_two_group (CFSG.Open.pCore 2 ↥L)
    (CFSG.LieType.BorelTits.pCore_isPGroup 2) Nat.prime_three (by norm_num)] at h1
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  exact h1

end Quot5

end CFSG.Quasithin.A38c7
