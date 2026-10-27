module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
public import CFSG.RankThree.PartTwo.KFacts.KS14HJBasic
public import CFSG.Adapters.StatedClassicalSmallOrders
public import CFSG.Adapters.StatedClassicalUnitaryOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F08
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem not_isSpor_J2_of_isL3Odd_three_or_psu33 {X : Type} [Group X]
    (hX : IsL3Odd X 3 ∨ LieModel X .PSU 3 3 1) : ¬ IsSpor X .J2 := by
  intro hJ2
  obtain ⟨e⟩ := hJ2
  have hcard : Nat.card X = 604800 := by
    rw [Nat.card_congr e.toEquiv]
    change Nat.card CFSG.Blueprint.NativeSporadic.J2 = 604800
    exact CFSG.RankThree.PartTwo.KFacts.KS14.card_nativeJ2
  rcases hX with hL3 | hU3
  · have hm : LieModel X .PSL 3 3 1 := hL3
    have hcl : CFSG.Open.StatedClassicalModel X .PSL 3 3 1 :=
      CFSG.Blueprint.LieModel.statedClassicalModel hm (by decide)
    have h5616 : Nat.card X = 5616 :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_three hcl
    omega
  · have hcl : CFSG.Open.StatedClassicalModel X .PSU 3 3 1 :=
      CFSG.Blueprint.LieModel.statedClassicalModel hU3 (by decide)
    have h6048 : Nat.card X = 6048 :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psu_three_three hcl
    omega

theorem list880_of_isL3Odd_three {X : Type} [Group X] (h : IsL3Odd X 3) : List880 X := by
  have h' : LieModel X .PSL 3 3 1 := h
  unfold List880
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h'))))))))))))

theorem list880_of_psu33 {X : Type} [Group X] (h : LieModel X .PSU 3 3 1) : List880 X := by
  unfold List880
  exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl ⟨1, Or.inl ⟨rfl, h⟩⟩))))))))))))))

theorem k_eq_one_of_list880 {D : Data G} (h880 : F08.R880 D) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hlist : List880 (Bar2 L)) (hJ2 : ¬ IsSpor (Bar2 L) .J2) :
    D.k = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
    by_contra hns
    obtain ⟨P, hP⟩ :=
      CFSG.ClassicalInvolution.GlaubermanAut.exists_isSylowOf_ge
        (p := 3) (R := (⊥ : Subgroup G)) (H := D.M) (IsPGroup.of_bot) bot_le
    exact hJ2 (h880 L hL hlist hns P hP.2).1
  exact Data.k_eq_one_of_isStronglyPEmbedded D hstr

theorem k_eq_one_of_isL3Odd_or_psu33 {D : Data G} (h880 : F08.R880 D) {L : Subgroup G}
    (hL : L ∈ calC D.M)
    (htype : IsL3Odd (Bar2 L) 3 ∨ LieModel (Bar2 L) .PSU 3 3 1) : D.k = 1 := by
  rcases htype with hL3 | hU3
  · exact k_eq_one_of_list880 h880 hL (list880_of_isL3Odd_three hL3)
      (not_isSpor_J2_of_isL3Odd_three_or_psu33 (Or.inl hL3))
  · exact k_eq_one_of_list880 h880 hL (list880_of_psu33 hU3)
      (not_isSpor_J2_of_isL3Odd_three_or_psu33 (Or.inr hU3))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
