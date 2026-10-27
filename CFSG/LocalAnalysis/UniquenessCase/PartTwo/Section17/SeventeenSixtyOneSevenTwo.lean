module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem normalizer_ne_top_of_card_prime (D : Data G) {Z : Subgroup G} {r : ℕ}
    (hr : r.Prime) (hZ : Nat.card Z = r) : normalizer (Z : Set G) ≠ ⊤ := by
  intro htop
  have hZn : Z.Normal := Subgroup.normalizer_eq_top_iff.mp htop
  have : IsSimpleGroup G := D.standing.simple
  have : Fact r.Prime := ⟨hr⟩
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal Z with hbot | htopZ
  · have h1 : Nat.card Z = 1 := by rw [hbot, Subgroup.card_bot]
    rw [hZ] at h1
    exact hr.ne_one h1
  · have hcardG : Nat.card G = r := by
      rw [← hZ, htopZ, Subgroup.card_top]
    have : IsCyclic G := isCyclic_of_prime_card hcardG
    have : IsMulCommutative G := IsCyclic.isMulCommutative
    obtain ⟨a, b, hab⟩ := D.standing.nonab
    exact hab (mul_comm a b)

theorem not_isMulCommutative_bar_of_isL2_or_isSz
    {K : Subgroup G}
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3) : ¬ IsMulCommutative (Bar2 K) := by
  intro hcomm
  have : IsMulCommutative (Bar2 K) := hcomm
  have : IsSimpleGroup (Bar2 K) := by
    rcases hshape with h | h
    · exact CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) h
    · have hS : CFSG.Blueprint.SuzukiModel (Bar2 K) 2 3 :=
        (CFSG.Blueprint.LieModel.twistedB2_iff (n := 0) (p := 2) (f := 3)).mp h |>.2
      exact (CFSG.LieType.Simplicity.fam_2b2_simplicity (Bar2 K) 2 3 hS).2
  have hp := CFSG.OrderReductions.Helpers.prime_card_of_simple_commutative (Bar2 K)
  rcases hshape with h | h
  · rw [card_of_isL2 h] at hp
    norm_num at hp
  · rw [show Nat.card (Bar2 K) = CFSG.Open.ordSuzuki 8 from
      CFSG.GH74.card_of_lieModel_twistedB2 h, CFSG.Open.ordSuzuki] at hp
    norm_num at hp

theorem not_card_bar_dvd_alt
    {K : Subgroup G} {p : ℕ}
    (h : (p = 3 ∧ IsL2 (Bar2 K) 3) ∨ (p = 5 ∧ IsSz (Bar2 K) 3)) :
    ¬ Nat.card (Bar2 K) ∣ Nat.card (alternatingGroup (Fin (2 * p))) := by
  rintro hdvd
  have h6 : Nat.card (alternatingGroup (Fin (2 * 3))) = 360 := by
    rw [CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 4]
    norm_num
  have h10 : Nat.card (alternatingGroup (Fin (2 * 5))) = 1814400 := by
    rw [CFSG.Alternating.Multipliers.nat_card_alternatingGroup_fin 8]
    norm_num
  rcases h with ⟨rfl, hL2⟩ | ⟨rfl, hSz⟩
  · rw [card_of_isL2 hL2, h6] at hdvd
    norm_num at hdvd
  · rw [show Nat.card (Bar2 K) = CFSG.Open.ordSuzuki 8 from
      CFSG.GH74.card_of_lieModel_twistedB2 hSz, CFSG.Open.ordSuzuki, h10] at hdvd
    norm_num at hdvd


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
