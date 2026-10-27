module

import CFSG.CharacterTheory.Wreathed.NormalOddIndexFullCenterLayer
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF79

open CFSG CFSG.RankThree.PartTwo.Sec21
open CFSG.Assembly (KProper InCatalog)
open CFSG.Assembly.RankThreeEven (localRank)

variable {G : Type} [Group G]

theorem generalizedFitting_eq_top_of_simple' [Finite G] (hs : IsSimpleGroup G)
    (hna : ∃ x y : G, x * y ≠ y * x) : generalizedFitting G = ⊤ := by
  haveI : (⊤ : Subgroup G).Normal := inferInstance
  haveI : IsSimpleGroup (⊤ : Subgroup G) := Subgroup.topEquiv.isSimpleGroup
  have hna' : ∃ a b : (⊤ : Subgroup G), a * b ≠ b * a := by
    obtain ⟨x, y, hxy⟩ := hna
    exact ⟨⟨x, trivial⟩, ⟨y, trivial⟩, fun h => hxy (congrArg Subtype.val h)⟩
  refine CFSG.Wreathed.NormalOddIndexFullCenterLayer.generalizedFitting_eq_simple
    (⊤ : Subgroup G) hna' ?_
  rw [eq_bot_iff]
  intro z hz
  have hzc : z ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_iff.mp hz g (Subgroup.mem_top g)
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h | h
  · rw [h] at hzc
    exact hzc
  · exfalso
    obtain ⟨x, y, hxy⟩ := hna
    have : y ∈ Subgroup.center G := by rw [h]; trivial
    exact hxy (Subgroup.mem_center_iff.mp this x)

theorem thmA_exists_sylow [Finite G] (H : Subgroup G) : ∃ B : Subgroup G, IsSylowOf 3 B H := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P⟩ : Nonempty (Sylow 3 H) := inferInstance
  refine ⟨(P : Subgroup H).map H.subtype, ?_, ?_, ?_⟩
  · rintro _ ⟨x, -, rfl⟩
    exact x.2
  · exact P.isPGroup'.map H.subtype
  · rw [Subgroup.relIndex, Subgroup.subgroupOf,
      Subgroup.comap_map_eq_self_of_injective H.subtype_injective]
    exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr (P.not_dvd_index)

theorem pRank_cen_eq_three [Finite G] {b : G} {B : Subgroup G} (hB : IsSylowOf 3 B (Cen b))
    (hB3 : IsElemAb 3 3 B) : CFSG.Open.pRank 3 (Cen b) = 3 := by
  haveI : IsElementaryAbelian 3 B := hB3.1
  have hel : CFSG.Open.IsElemAbelian 3 B :=
    ⟨hB3.1.toIsMulCommutative, fun x hx => elemPow_eq_one_of_isElementaryAbelian x hx⟩
  apply le_antisymm
  · refine csSup_le' ?_
    rintro k ⟨E, hEC, -, hk⟩
    have h1 : 3 ^ k ∣ Nat.card (Cen b) := hk ▸ Subgroup.card_dvd_of_le hEC
    have h2 := Subgroup.relIndex_mul_card (H := B) (K := Cen b)
    rw [inf_of_le_left hB.1, hB3.2] at h2
    have h3 : 3 ^ k ∣ 3 ^ 3 * B.relIndex (Cen b) := by rw [mul_comm, h2]; exact h1
    have h4 : Nat.Coprime (3 ^ k) (B.relIndex (Cen b)) :=
      (Nat.Coprime.pow_left _ hB.2.2)
    have h5 : 3 ^ k ∣ 3 ^ 3 := h4.dvd_of_dvd_mul_right h3
    exact (Nat.pow_dvd_pow_iff_le_right (by norm_num)).mp h5
  · exact le_csSup (CFSG.RankThreeEvenClassification.Helpers.pRank_bddAbove 3 Nat.prime_three _)
      ⟨B, hB.1, hel, hB3.2⟩

end CFSG.RankThree.PartTwo.Sec21.FF79
