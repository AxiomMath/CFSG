module

public import CFSG.Quasithin.EmptyFaithful.A38c7Main
public import CFSG.Quasithin.EmptyFaithful.T1515dB

public section

namespace CFSG.Quasithin.A38c10

open CFSG.Assembly.LowTwoRank CFSG.Quasithin.A38c7

section Quot4

variable {G : Type} [Group G] [Finite G] {L : Subgroup G}

theorem card_eq_of_quot4 (hq : IsLnTwoQuot L 4) : ∃ k : ℕ, Nat.card ↥L = 2 ^ k * 20160 := by
  obtain ⟨e⟩ := hq
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hN : IsPGroup 2 ↥(CFSG.pCore 2 ↥L) := by
    exact CFSG.LieType.BorelTits.pCore_isPGroup 2
  obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2)).1 hN
  refine ⟨k, ?_⟩
  rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥L),
    Nat.card_congr e.toEquiv, card_statedSL_four_zmod1527d, hk]
  ring

theorem not_dvd_27_card_of_quot4 (hq : IsLnTwoQuot L 4) : ¬ 27 ∣ Nat.card ↥L := by
  obtain ⟨k, hk⟩ := card_eq_of_quot4 hq
  rw [hk]
  intro h
  have hcop : Nat.Coprime 27 (2 ^ k) := Nat.Coprime.pow_right k (by norm_num)
  have := hcop.dvd_of_dvd_mul_left h
  omega

theorem two_le_pRank_of_quot4 (hq : IsLnTwoQuot L 4) : 2 ≤ CFSG.Open.pRank 3 L := by
  obtain ⟨e⟩ := hq
  have h1 : 2 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup ↥(StatedSL 4 (ZMod 2))) :=
    R3c.two_le_pRank_three_statedSL_four_two
  have e' : (↥L ⧸ CFSG.Open.pCore 2 ↥L) ≃* ↥(StatedSL 4 (ZMod 2)) :=
    (QuotientGroup.quotientMulEquivOfEq (CFSG.pCore_eq_open ↥L 2).symm).trans e
  rw [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num : 1 < 3) e'] at h1
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [CFSG.SectionRank.pRank_quotient_two_group (CFSG.Open.pCore 2 ↥L)
    (CFSG.LieType.BorelTits.pCore_isPGroup 2) Nat.prime_three (by norm_num)] at h1
  rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
  exact h1

end Quot4

theorem concl15317_two4 {G : Type} [Group G] [Finite G] {T V₁ Yp I L : Subgroup G}
    (c17 : Concl15317 T V₁ Yp I L) (hq : IsLnTwoQuot L 4) : Yp ≤ thetaOf I ∧ thetaOf I = L := by
  rcases c17 with ⟨h1, -⟩ | ⟨-, hY, hθ⟩ | ⟨-, n, F, hF, hFin, hn, hcard, ⟨e⟩⟩
  · have := two_le_pRank_of_quot4 hq
    omega
  · exact ⟨hY, hθ⟩
  · exfalso
    apply not_dvd_27_card_of_quot4 hq
    have h27 : 27 ∣ Nat.card ↥(CFSG.Assembly.LowTwoRank.StatedSL 3 F) :=
      dvd_27_card_statedSL_three hn (by rw [Nat.card_eq_fintype_card]; exact hcard)
    rw [← Nat.card_congr e.toEquiv] at h27
    exact h27.trans (card_autOn_dvd L _)

end CFSG.Quasithin.A38c10
