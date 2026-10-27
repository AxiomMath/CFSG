module

public import CFSG.RankThree.PartTwo.Sec4.Census.WiringSporadic
import CFSG.RankThree.PartTwo.Census.CenterThreeTransfer
import CFSG.RankThree.PartTwo.Sec4.Census.CoverSLThree46

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec4

theorem card_center_dvd_three_of_A6 {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X)
    (hZ : IsPGroup 3 (Subgroup.center X))
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 6)) :
    Nat.card (Subgroup.center X) ∣ 3 :=
  CenterThreeTransfer.card_center_dvd_three_of_mulEquiv hX hZ e (m := 40)
    (by rw [nat_card_alternatingGroup, Nat.card_fin]; decide) (by norm_num)

theorem card_center_dvd_three_of_A7 {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X)
    (hZ : IsPGroup 3 (Subgroup.center X))
    (e : X ⧸ Subgroup.center X ≃* alternatingGroup (Fin 7)) :
    Nat.card (Subgroup.center X) ∣ 3 :=
  CenterThreeTransfer.card_center_dvd_three_of_mulEquiv hX hZ e (m := 280)
    (by rw [nat_card_alternatingGroup, Nat.card_fin]; decide) (by norm_num)

theorem card_center_dvd_three_of_M22 {X : Type} [Group X] [Finite X] (hX : IsQuasisimple X)
    (hZ : IsPGroup 3 (Subgroup.center X))
    (e : X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.M22) :
    Nat.card (Subgroup.center X) ∣ 3 :=
  CenterThreeTransfer.card_center_dvd_three_of_mulEquiv hX hZ e (m := 49280)
    (card_m22_eq.trans (by norm_num)) (by norm_num)

@[expose] def CoverCenterThreeRest : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsQuasisimple X → IsPGroup 3 (Subgroup.center X) →
    (Blueprint.ChevalleyExceptionalModel (X ⧸ Subgroup.center X) .G2 3 1 ∨
      Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.J3) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.McL) ∨
      Nonempty (X ⧸ Subgroup.center X ≃* Blueprint.NativeSporadic.ON)) →
    Nat.card (Subgroup.center X) ∣ 3

theorem coverCenterThree_of_rest (h : CoverCenterThreeRest) : CoverCenterThree := by
  intro X _ _ hX hZ hS
  rcases hS with hA6 | hA7 | hG2 | hM22 | hJ3 | hMcL | hON
  · exact card_center_dvd_three_of_A6 hX hZ hA6.some
  · exact card_center_dvd_three_of_A7 hX hZ hA7.some
  · exact h X hX hZ (Or.inl hG2)
  · exact card_center_dvd_three_of_M22 hX hZ hM22.some
  · exact h X hX hZ (Or.inr (Or.inl hJ3))
  · exact h X hX hZ (Or.inr (Or.inr (Or.inl hMcL)))
  · exact h X hX hZ (Or.inr (Or.inr (Or.inr hON)))

section Item46


theorem rank3II_4_6_of_cover_rest (h41 : Item4_1) (hmult : TripleCoverInputs)
    (hsl : CoverSLThree46) (hcen : CoverCenterThreeRest) : Item4_6 :=
  rank3II_4_6_of_cover h41 hmult hsl (coverCenterThree_of_rest hcen)

theorem rank3II_4_6_of_cover_rest' (h41 : Item4_1) (hmult : TripleCoverInputs)
    (hcen : CoverCenterThreeRest) : Item4_6 :=
  rank3II_4_6_of_cover_rest h41 hmult coverSLThree46 hcen

end Item46

end CFSG.RankThree.PartTwo.Sec4.Census
