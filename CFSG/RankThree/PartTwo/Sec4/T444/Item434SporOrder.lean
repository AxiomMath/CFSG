module

public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SporKit
public import CFSG.Sporadic.Bridge.M22
public import CFSG.Sporadic.Bridge.M23Surj
public import CFSG.Sporadic.Bridge.HSSurj
public import CFSG.Sporadic.Schreier.MathieuOddCoreM22
public import CFSG.RankThree.PartOne.SPOR.Outer
public import CFSG.RankThree.PartTwo.Sec4.Item47Kinds

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.LocalCores CFSG.Blueprint
open Item434Kit Item434Alt
open CFSG.ComponentClassification.OuterAutomorphisms (Outer equivalence)

namespace Item434Spor

variable {G : Type} [Group G] [Finite G] {A M Q : Subgroup G} {X : Type*} [Group X]

theorem false_of_not_dvd_card (h : Ctx434Core G A M Q)
    (e : layer G ⧸ Subgroup.center (layer G) ≃* X) (hout : ¬ 3 ∣ Nat.card (Outer X))
    (hX : ¬ 27 ∣ Nat.card X) (h27 : Nat.card h.layerStar = 27) : False := by
  have hPmap := map_comap_conj_eq h e hout
  have h1 : Nat.card (A.map (quotConj e)) ∣
      Nat.card ((A.map (quotConj e)).comap (MulAut.conj : X →* MulAut X)) := by
    conv_lhs => rw [← hPmap]
    exact Subgroup.card_map_dvd _ _
  rw [card_map_quotConj h e, h27] at h1
  exact hX (h1.trans (Subgroup.card_subgroup_dvd_card _))

theorem not_three_dvd_card_outer_of_le_two [Finite X] (h : Nat.card (Outer X) ≤ 2) :
    ¬ 3 ∣ Nat.card (Outer X) := by
  have : Finite (MulAut X) := MulEquiv.finite_left
  intro h3
  have := Nat.le_of_dvd Nat.card_pos h3
  omega

end Item434Spor

section Families


theorem item434SporAtCard_m22_27 :
    Item434SporAtCard .M22 27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  have b' : NativeSporadic.M22 ≃* Spor .M22 := b
  have hcard : Nat.card (Spor .M22) = 443520 := by
    rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Mathieu.card_M22]
  have : Finite (Spor .M22) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hout : ¬ 3 ∣ Nat.card (Outer (Spor .M22)) := by
    refine Item434Spor.not_three_dvd_card_outer_of_le_two ?_
    rw [← Nat.card_congr (equivalence b').toEquiv]
    exact Sec4.card_outer_le_two_of_card_mulAut_le CFSG.Sporadic.Schreier.m22_center_eq_bot'
      CFSG.Sporadic.Schreier.m22_mulAut_card
  exact (Item434Spor.false_of_not_dvd_card hc e₀ hout (by rw [hcard]; norm_num) h27).elim

theorem item434SporAtCard_m23_27 :
    Item434SporAtCard .M23 27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
  have b' : NativeSporadic.M23 ≃* Spor .M23 := b
  have hcard : Nat.card (Spor .M23) = 10200960 := by
    rw [← Nat.card_congr b'.toEquiv, CFSG.Sporadic.Schreier.m23_card]
  have : Finite (Spor .M23) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hout : ¬ 3 ∣ Nat.card (Outer (Spor .M23)) := by
    refine Item434Spor.not_three_dvd_card_outer_of_le_two ?_
    rw [← Nat.card_congr (equivalence b').toEquiv]
    exact CFSG.Sporadic.Schreier.at_m23_schreier.1
  exact (Item434Spor.false_of_not_dvd_card hc e₀ hout (by rw [hcard]; norm_num) h27).elim

theorem item434SporAtCard_hs_27 :
    Item434SporAtCard .HS 27 := by
  intro G₀ _ _ hG₀ H G _ _ f hf hker A M Q hc hL h27
  obtain ⟨e₀⟩ := hL
  obtain ⟨b⟩ := CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  have b' : NativeSporadic.Carrier .HS ≃* Spor .HS := b
  have hcard : Nat.card (Spor .HS) = 44352000 := by
    rw [← Nat.card_congr b.toEquiv, CFSG.Sporadic.HS.card_HS]
  have : Finite (Spor .HS) := Nat.finite_of_card_ne_zero (by rw [hcard]; norm_num)
  have hout : ¬ 3 ∣ Nat.card (Outer (Spor .HS)) := by
    refine Item434Spor.not_three_dvd_card_outer_of_le_two ?_
    rw [← Nat.card_congr (equivalence b').toEquiv]
    exact CFSG.RankThree.PartOne.SPOR.card_outer_HS_le_two
  exact (Item434Spor.false_of_not_dvd_card hc e₀ hout (by rw [hcard]; norm_num) h27).elim

end Families

end CFSG.RankThree.PartTwo.Sec4
