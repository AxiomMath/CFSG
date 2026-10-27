module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenEightGraphOuter

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

section Certified


theorem gap17_8_graphOuterThree_of_mBarGT (D : Data G) (hx : DataExt D)
    (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D) (h127 : R127 D) (h1114 : R1114 D)
    (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G) (h183 : W3Thm183 G)
    (h111 : W3Thm111 G) (h126 : R126 D) (h869 : F08.R869 D) (h77 : Inputs1719.W4Lem7_7)
    (hKL : Inputs1719.K_L33AutE8) (h411 : W4Lem4_11Prime) {V₀ V : Subgroup G}
    (hm : MBarGT D.M V₀ V 3) : Gap17_8_graphOuterThree D V₀ V := by
  intro hV L hL hL3 hTL hk _ _ _ _ _ _ _ _ _
  have hnt : ¬ F08.Thin8 L := not_thin8_of_isL3Odd hL3
  have h117 : C117 D V₀ V := ElevenNine.c117_of_hyp11 D h869 (Hyp125.hyp11 h127 hV)
  have hL1 : barSub V₀ V hV.isElemAbelian L ≠ ⊥ := barSub_ne_bot_of_not_thin hV h117 hL hnt
  have hU' : UniqueMax D.M (L ⊔ D.T) := Inputs1719.uniqueMax_sup_T_of_not_thin h869 hL hnt
  have hN : calNOf L = {D.M} :=
    h869 L (Or.inl hL) L le_rfl
      (sup_eq_left.mpr (CFSG.LieType.BorelTits.pCoreOf_le 2 L)) hnt
  have hU : UniqueMax D.M L := UC22.uc22p22u_uniqueMax_of_calN D hL.1.le hN
  have hUc : UniqueMax D.M (UC22.conjClosure D.M L) :=
    uc22p22u_uniqueMax_mono D (TwelveTwentyThree.le_conjClosure D.M L)
      (TwelveTwentyThree.conjClosure_le hL.1.le) hU
  have hb : bBar (UC22.conjClosure D.M L) D.M V₀ V hV.isElemAbelian ≤ 2 :=
    b17_8BoundTwo_holds h77 hKL D V₀ V hV L hL hL3
  have hInFSq' : CFSG.LocalAnalysis.WeakClosure81.InFSq 1 (L ⊔ D.T) :=
    gap17_8_inFSq_of h411 D hV L hL hL3 hTL hk
  have hsp3 : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
    by_contra hns
    have h2 : D.k = 2 := (Data.k_eq_two_iff D).2 hns
    omega
  have hbar3 : 3 ∣ Nat.card (Bar2 L) := by
    have hcl : CFSG.Open.StatedClassicalModel (Bar2 L) .PSL 3 3 1 :=
      CFSG.Blueprint.LieModel.statedClassicalModel hL3 (by decide)
    have h5616 : Nat.card (Bar2 L) = 5616 :=
      CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_three hcl
    rw [h5616]
    norm_num
  have h3H : 3 ∣ Nat.card ↥(L ⊔ D.T) := by
    have h3L : 3 ∣ Nat.card ↥L := by
      rw [card_eq_card_pCoreOf_mul_card_bar2 (G := G) L]
      exact dvd_mul_of_dvd_right hbar3 _
    exact h3L.trans (Subgroup.card_dvd_of_le le_sup_left)
  have hO2 : ∀ g : G, g ∉ D.M → ¬ twoResidual (L ⊔ D.T) ≤ conjSubgroup D.M g :=
    CFSG.GroupTheory.twoResidual_not_le_conjSubgroup_of_isStronglyPEmbedded Nat.prime_three
      (by norm_num) (sup_le hL.1.le D.sylowM.le) h3H hsp3
  exact false_of_bBar_le_two D hx h61 h66 h127 h1114 h162 hTor h1482 h183 h111 h126 hk
    hV hL hL1 hU' hUc hInFSq' hb hm hO2

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
