module

public import CFSG.RankThree.PartTwo.Sec19.Census194.Defs
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194

open CFSG CFSG.RankThree.PartTwo.Sec19

theorem odd_card_center_of_pCore_eq_bot {Y : Type} [Group Y] [Finite Y]
    (h : CFSG.pCore 2 Y = ⊥) : Odd (Nat.card (Subgroup.center Y)) := by
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center Y) := by
    rcases Nat.even_or_odd (Nat.card (Subgroup.center Y)) with he | ho
    · exact even_iff_two_dvd.mp he
    · exact absurd ho hodd
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨x, hx⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center Y) 2 h2
  have hzo : orderOf (x : Y) = 2 := by rw [Subgroup.orderOf_coe]; exact hx
  have hnorm : (Subgroup.zpowers (x : Y)).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr x.2)
  have hpg : IsPGroup 2 (Subgroup.zpowers (x : Y)) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hzo]
    norm_num
  have hle : Subgroup.zpowers (x : Y) ≤ CFSG.pCore 2 Y := le_sSup ⟨hnorm, hpg⟩
  rw [h] at hle
  have hmem : (x : Y) ∈ (⊥ : Subgroup Y) := hle (Subgroup.mem_zpowers _)
  rw [Subgroup.mem_bot] at hmem
  rw [hmem, orderOf_one] at hzo
  omega

@[expose] def TooBig (G : Type) [Group G] [Finite G] : Prop :=
  ∃ r : ℕ, r.Prime ∧ ((r = 3 ∧ 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G)) ∨
    (3 < r ∧ 3 ≤ CFSG.Open.pRank r (⊤ : Subgroup G)))

theorem tooBig_of_three {G : Type} [Group G] [Finite G]
    (h : 4 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup G)) : TooBig G :=
  ⟨3, Nat.prime_three, Or.inl ⟨rfl, h⟩⟩

theorem tooBig_of_prime {G : Type} [Group G] [Finite G] {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (h : 3 ≤ CFSG.Open.pRank r (⊤ : Subgroup G)) : TooBig G :=
  ⟨r, hr, Or.inr ⟨hr3, h⟩⟩

theorem Census194RankHyp.false_of_tooBig {Y : Type} [Group Y] [Finite Y]
    (h : Census194RankHyp Y) (ht : TooBig Y) : False := by
  obtain ⟨r, hr, ⟨rfl, h4⟩ | ⟨hr3, h3⟩⟩ := ht
  · have := h.pRank_three
    omega
  · have := h.pRank_prime r hr hr3
    omega

theorem _root_.CFSG.RankThree.PartTwo.Sec19.Census194RankHyp.false_of_tooBig {Y : Type}
    [Group Y] [Finite Y] (h : Census194RankHyp Y) (ht : TooBig Y) : False :=
  CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194.Census194RankHyp.false_of_tooBig h ht

theorem TooBig.of_mulEquiv {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    (e : G ≃* G') (h : TooBig G) : TooBig G' := by
  obtain ⟨r, hr, ⟨rfl, h4⟩ | ⟨hr3, h3⟩⟩ := h
  · exact tooBig_of_three (by rwa [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv (by norm_num) e])
  · exact tooBig_of_prime hr hr3 (by
      rwa [← CFSG.SectionRank.pRank_top_eq_of_mulEquiv hr.one_lt e])

theorem TooBig.of_injective {G G' : Type} [Group G] [Finite G] [Group G'] [Finite G']
    (f : G →* G') (hf : Function.Injective f) (h : TooBig G) : TooBig G' := by
  obtain ⟨r, hr, ⟨rfl, h4⟩ | ⟨hr3, h3⟩⟩ := h
  · exact tooBig_of_three
      (h4.trans (CFSG.SectionRank.pRank_top_le_of_injective (by norm_num) f hf))
  · exact tooBig_of_prime hr hr3
      (h3.trans (CFSG.SectionRank.pRank_top_le_of_injective hr.one_lt f hf))

noncomputable def mulEquivQuotientCenterOfEqBot {Y : Type} [Group Y]
    (h : Subgroup.center Y = ⊥) : Y ≃* Y ⧸ Subgroup.center Y :=
  (QuotientGroup.quotientBot.symm).trans (QuotientGroup.quotientMulEquivOfEq h.symm)

end CFSG.RankThree.PartTwo.Sec19.Census194.RonanC194
