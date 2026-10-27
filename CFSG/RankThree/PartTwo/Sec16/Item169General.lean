module

public import CFSG.RankThree.PartTwo.Sec16.Item16TailEnd
public import CFSG.RankThree.PartTwo.Sec16.Item16TailMore
import CFSG.RankThree.PartTwo.KFacts.KS14Orders
import CFSG.Models.PGLOrders
public import CFSG.RankThree.PartTwo.Sec16.Item163Proof

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16.Proof169 CFSG.GH74.GLS
open CFSG.Assembly.RankThreeEven (projSL projSU)

variable {G : Type} [Group G] [Finite G]

theorem card_projSL_three_four : Nat.card (projSL 3 (GaloisField 2 2)) = 20160 :=
  CFSG.PGLModel.card_projSL_three_four

theorem card_projSU_three_five [Fact (Nat.Prime 5)] : Nat.card (projSU 3 5 1) = 126000 :=
  CFSG.PGLModel.card_projSU_three_five

theorem l34_not_a7_not_u35 {X : Type} [Group X]
    (hX : Nonempty (X ≃* projSL 3 (GaloisField 2 2))) :
    IsEmpty (X ≃* alternatingGroup (Fin 7)) ∧
      ∀ _ : Fact (Nat.Prime 5), IsEmpty (X ≃* projSU 3 5 1) := by
  obtain ⟨e⟩ := hX
  have hX : Nat.card X = 20160 := by rw [Nat.card_congr e.toEquiv, card_projSL_three_four]
  refine ⟨⟨fun f => ?_⟩, fun _ => ⟨fun f => ?_⟩⟩
  · have h := Nat.card_congr f.toEquiv
    rw [hX, KFacts.KS14.card_alternatingGroup_five_seven_ten.2.1] at h
    norm_num at h
  · have h := Nat.card_congr f.toEquiv
    rw [hX, card_projSU_three_five] at h
    norm_num at h

theorem rank3II_16_9_2_of {A : Subgroup G} {c : G} {L : Subgroup G} (h : Sec15R G A c L)
    (hY0 : (scriptY0 A (lB A)).Nonempty) (h163 : Item163 A (lB A) c L)
    (hMeets : Step163Meets) (h1514 : Item1514 A (lB A) c L) (h1510 : Item1510 A)
    (hBr : Step169TwoBridge) :
    IsEmpty (↥L ⧸ aschbacherSolvableCore 3 ↥L ≃* projSL 3 (GaloisField 2 2)) := by
  refine ⟨fun φ => ?_⟩
  obtain ⟨Y, hY⟩ := hY0
  obtain ⟨Y₀, -, hY₀⟩ := Finite.exists_le_maximal (p := (· ∈ scriptY0 A (lB A))) hY
  have hLY : L ≤ Y₀ := (h163 Y₀ hY₀).2.2.2.1
  have hmeet := hMeets G A c L h Y₀ hY₀ hLY
  obtain ⟨hA7, hU35⟩ := l34_not_a7_not_u35 ⟨φ⟩
  rcases h1514 Y₀ hY₀ hmeet with ⟨-, -, hΩ, hprod, -⟩ | ⟨⟨e⟩, -⟩ | ⟨⟨h5, ⟨e⟩⟩, -⟩
  · exact false_of_l34 h φ hΩ hprod h1510 hBr
  · exact hA7.false e
  · exact (hU35 h5).false e

end CFSG.RankThree.PartTwo.Sec16
