module

public import CFSG.RankThree.PartTwo.Sec17.RouteForms
import CFSG.RankThree.PartTwo.Sec14.Item148Solvable

public section

namespace CFSG.RankThree.PartTwo.Sec14

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Late CFSG.RankThree.LocalRank CFSG.GH74.GLS

variable {G : Type} [Group G] [Finite G] {A L : Subgroup G} {c : G}

theorem claim1411LocalW_of_nonsolvable (h : Sec14Std G A c L) (h146 : Item146 A (lB A))
    (hbot : ∃ B, IsHyperplane A B ∧ lB A B = ⊥)
    (hW : ∀ Y : Subgroup G, Y = delta A (lB A) Y → Y ∈ scriptY A → ¬ Group.IsSolvable ↥Y →
      TransOn A (lB A) (Subgroup.normalizer (A : Set G)) Y) :
    ∀ Y ∈ scriptY A, TransOn A (lB A) (Subgroup.normalizer (A : Set G)) Y := by
  have hXW : xA A ≤ Subgroup.normalizer (A : Set G) :=
    (pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le_normalizer _)
  intro Y hY
  have hY' : delta A (lB A) Y ∈ scriptY A := by
    refine ⟨fun htop => hY.1 (top_le_iff.mp ?_), le_normalizer_sSup fun Q hQ => hQ.1.1.2.2⟩
    rw [← htop]
    exact delta_le Y
  have hYΔ : delta A (lB A) Y = delta A (lB A) (delta A (lB A) Y) := (delta_delta Y).symm
  refine transOn_of_delta ?_
  by_cases hs : Group.IsSolvable ↥(delta A (lB A) Y)
  · exact transOn_mono hXW (transOn_of_isSolvable_std h h146 hbot hYΔ hY' hs)
  · exact hW _ hYΔ hY' hs

theorem rank3II_14_11_1_of_W (h : Sec14Std G A c L)
    (hW : ∀ Y ∈ scriptY A, TransOn A (lB A) (Subgroup.normalizer (A : Set G)) Y) :
    Item1411_1 A (lB A) := by
  intro S hS T hT
  rw [inf_top_eq]
  exact rank3II_14_11_1_lB h (fun Y hY => hW Y hY) hS hT

theorem item1411_1R_of_W (h146 : Item146S14) (hbot : Item145BotS14)
    (hW : Claim1411NonsolvWR) : Item1411_1R :=
  fun G _ _ A c L hR => rank3II_14_11_1_of_W hR.toSec14Std
    (claim1411LocalW_of_nonsolvable hR.toSec14Std (h146 G A c L hR.toSec14Std)
      (hbot G A c L hR.toSec14Std) (hW G A c L hR))

end CFSG.RankThree.PartTwo.Sec14
