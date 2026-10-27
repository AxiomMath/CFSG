module

public import CFSG.RankThree.PartTwo.Sec21.Item2113Res2ProofChoice
import CFSG.RankThree.PartTwo.Sec17.Item1730Conj
import CFSG.RankThree.PartTwo.KFacts.KS17J2AutOuter
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.Sec4.LThreePiFieldTwo
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut

public section

namespace CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open Subgroup
open scoped Pointwise

variable {G : Type} [Group G]

theorem le_inf_sup_zpowers {A L : Subgroup G} {c : G} (hcA : c ∈ A)
    (hLc : L ≤ centralizer ({c} : Set G)) (hle : A ≤ zpowers c ⊔ L) :
    A ≤ (A ⊓ L) ⊔ zpowers c := by
  intro a ha
  have hcC : c ∈ centralizer (L : Set G) := mem_centralizer_iff.mpr fun l hl =>
    mem_centralizer_singleton_iff.mp (hLc hl)
  have hnorm : zpowers c ≤ normalizer (L : Set G) :=
    (zpowers_le.mpr hcC).trans (centralizer_le_normalizer _)
  have hmem : a ∈ ((zpowers c : Subgroup G) : Set G) * (L : Set G) := by
    rw [← coe_mul_of_left_le_normalizer_right _ _ hnorm]
    exact hle ha
  obtain ⟨w, hw, l, hl, rfl⟩ := hmem
  have hwA : w ∈ A := (zpowers_le.mpr hcA) hw
  have hlA : l ∈ A := by
    have : l = w⁻¹ * (w * l) := by group
    rw [this]
    exact A.mul_mem (A.inv_mem hwA) ha
  have hcomm : w * l = l * w := by
    obtain ⟨k, rfl⟩ := mem_zpowers_iff.mp hw
    exact ((Commute.zpow_left (mem_centralizer_singleton_iff.mp (hLc hl)).symm k)).eq
  change w * l ∈ _
  rw [hcomm]
  exact mul_mem (mem_sup_left ⟨hlA, hl⟩) (mem_sup_right hw)

section Choice


theorem item2113ChoiceHJ_of (h211 : Item211) (h45 : Sec4.Item4_5) : Item2113ChoiceHJ := by
  intro G _ _ A E U c L hpair hJ _
  have hL : IsList218 L := Or.inr (Or.inr (Or.inl hJ))
  obtain ⟨hcA, hc1, hLc, hAL, hcL⟩ := Item2113Res2Proof.pair_data h45 hpair hL
  have hAe := hpair.mem_S.1.1
  have h27 : Nat.card A = 27 := by
    rw [Item2113Proof.card_eq_of_isList218 h211 hpair hL]; norm_num
  have hEA : E ≤ A := hpair.mem_E.2
  have hE27 : Nat.card E = 27 := hpair.mem_E.1.2.1
  have hEeq : E = A := eq_of_le_of_card_ge hEA (by rw [h27, hE27])
  have hAE : A ∈ partTwoE G := hEeq ▸ hpair.mem_E.1
  have hFE : partTwoF G = partTwoE G := (hpair.side hAE).symm
  have hJout : KFacts.KS17J2AutThree := KFacts.ks17J2AutThree_of_outer
    CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model.2.2.2.2.2
  have hle : A ≤ zpowers c ⊔ L :=
    Sec17.le_zpowers_sup_of_j2 Sec4.Sporadic.rank3II_4_15 hJout hFE hJ hcL hAe h27 hcA hAL
  have hc3 : c ^ 3 = 1 := hAe.2 c hcA
  have hcomm : ∀ a ∈ A ⊓ L, a * c = c * a := fun a ha =>
    mem_centralizer_singleton_iff.mp (hLc ha.2)
  have hcn : c ∉ A ⊓ L := fun h => hcL h.2
  have hcard := Sec4.card_sup_zpowers_of_not_mem hc3 hcomm hcn
  have heq : (A ⊓ L) ⊔ zpowers c = A :=
    le_antisymm (sup_le inf_le_left (zpowers_le.mpr hcA)) (le_inf_sup_zpowers hcA hLc hle)
  rw [heq, h27] at hcard
  omega

end Choice

end CFSG.RankThree.PartTwo.Sec21.Item2113Res3Proof
