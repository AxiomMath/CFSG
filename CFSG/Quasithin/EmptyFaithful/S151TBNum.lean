module

public import CFSG.Quasithin.EmptyFaithful.S151U5

public section

namespace CFSG.Quasithin.S151TB

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Quasithin.FLc
  CFSG.Timmesfeld.Orders CFSG.Quasithin.H13.VolI CFSG.Quasithin.Vol2.Ch10.SecA

variable {G : Type} [Group G] [Finite G]

theorem card_eq_three_mul {L B : Subgroup G} (hB : IsSylowTwoOf B L) {e q o m : ℕ}
    (ho : o % 2 = 1) (hLcard : Nat.card ↥L = 2 ^ q * (2 ^ e * o)) (hN3 : o = 3 * (m - 1)) :
    Nat.card ↥L = 3 * Nat.card B * (m - 1) := by
  have hBL : B ≤ L := hB.1
  have h1 : Nat.card (B.subgroupOf L) * (B.subgroupOf L).index = Nat.card ↥L :=
    Subgroup.card_mul_index _
  have h2 : Nat.card (B.subgroupOf L) = Nat.card B :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBL).toEquiv
  obtain ⟨b, hb⟩ := IsPGroup.iff_card.mp hB.2.1
  have hmodd : (B.subgroupOf L).index % 2 = 1 := Nat.two_dvd_ne_zero.mp hB.2.2
  have hm : (B.subgroupOf L).index = o := by
    apply s151u_odd_part (b := b) (c := q + e) hmodd ho
    rw [← hb, ← h2, h1, hLcard]
    ring
  rw [← h1, h2, hm, hN3]
  ring

theorem numerics_of_type {L B : Subgroup G}
    (htype : IsLnBlock L 3 ∨ IsAltBlockType L 6 ∨ IsG2Block L) (hB : IsSylowTwoOf B L) :
    IsShort2 L ∧ Nat.card ↥L = 3 * Nat.card B * (Nat.card (BlockN L) - 1) ∧
      4 ≤ Nat.card (BlockN L) := by
  rcases htype with h3 | h6 | hg
  · obtain ⟨e, β, hs⟩ := exists_lnStr h3
    have hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 168 := by
      rw [card_quot_pCore_of_surjective e hs.surj hs.ker, card_SLt_three]
    obtain ⟨q, hq⟩ := s151u_card_L hc
    have hn := s151u_card_BlockN_L3 hs
    refine ⟨h3.1, card_eq_three_mul (e := 3) (q := q) (o := 21) hB (by norm_num)
      (by rw [hq]; norm_num) (by rw [hn]), by rw [hn]; norm_num⟩
  · obtain ⟨hsh, α, hα, hker, β, hβs, hβk, -⟩ := h6
    have hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 360 := by
      rw [card_quot_pCore_of_surjective α hα hker, card_alt 6 (by norm_num)]
      decide
    obtain ⟨q, hq⟩ := s151u_card_L hc
    have hn : Nat.card (BlockN L) = 16 := by
      have h := Subgroup.index_ker β
      rw [hβk] at h
      have h2 : Nat.card β.range = Nat.card (Multiplicative (AltHeart 6)) := by
        rw [MonoidHom.range_eq_top.mpr hβs]
        exact Subgroup.card_top
      show ((blockZ L).subgroupOf (blockU L)).index = 16
      rw [h, h2, Nat.card_congr (Multiplicative.toAdd : Multiplicative (AltHeart 6) ≃ AltHeart 6)]
      exact CFSG.Quasithin.H13.A6Coc.card_altHeart
    refine ⟨hsh, card_eq_three_mul (e := 3) (q := q) (o := 45) hB (by norm_num)
      (by rw [hq]; norm_num) (by rw [hn]), by rw [hn]; norm_num⟩
  · obtain ⟨hsh, hpsu, hidx, hnatural⟩ := hg
    have hc : Nat.card (↥L ⧸ CFSG.pCore 2 ↥L) = 6048 :=
      CFSG.Quasithin.H13.card_of_statedClassicalModel_psu_three_three hpsu
    obtain ⟨q, hq⟩ := s151u_card_L hc
    have hn : Nat.card (BlockN L) = 64 := hidx
    refine ⟨hsh, card_eq_three_mul (e := 5) (q := q) (o := 189) hB (by norm_num)
      (by rw [hq]; norm_num) (by rw [hn]), by rw [hn]; norm_num⟩

end CFSG.Quasithin.S151TB
