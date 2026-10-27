module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiveA6Transfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiveA6InFSq
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.A6Exp4SThreePairHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFiveA6Orbit
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.A7PermutingHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem gap17_5_A6Module_of {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h17_1 : R17_1At D V₀ V hV) (h17_4 : R17_4AtA D V₀ V hV)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (h66 : UC6.R6_6 D) (h86 : W3Lem86_1 G) (h88 : W3Thm88 G) (h126 : R126 D)
    (h914N : W3Lem914N G) (hG5P : Gap17_5_A6Pair D V₀ V) (h410 : W4Lem4_10)
    (h43c : W3Lem45_2Chief) (h869 : F08.R869 D) (h127 : R127 D) (hC117 : C117 D V₀ V)
    (hKpair : Inputs1719.K_A6Exp4SThreePair) (hKaut : Inputs1719.K_A6AutOrder8)
    (h106 : Inputs1719.W4Lem10_6Q) :
    Gap17_5_A6Module D V₀ V := by
  intro _ L hL hshape hk
  have hnt : ¬ F08.Thin8 L := not_thin8_of_barO2Z_altSix hshape
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
    by_contra hns
    have h2 : D.k = 2 := (Data.k_eq_two_iff D).2 hns
    omega
  have hU : UniqueMax D.M (L ⊔ D.T) := Inputs1719.uniqueMax_sup_T_of_not_thin h869 hL hnt
  by_cases hexp : ExpFourAut17 D L
  · exact (false_of_expFour hV h17_1 h17_4 h869 h127 hC117 h106 hKpair hk hL hshape hexp).elim
  · exact ⟨card_vzero_le_four_of_not_expFour_orbit hTim hcat D h66 h86 h88 h126 h914N hV hG5P
      hL hshape hKaut hexp hsp hU, inFSq_one_of_not_expFour h410 h43c hL hshape hexp⟩

section Certified


theorem seventeen_five_of_A6Inputs {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h17_1 : R17_1At D V₀ V hV) (h82 : F08.R82 D)
    (h880 : F08.R880 D)
    (hx : DataExt D) (h61 : UC6.R6_1 D) (h66 : UC6.R6_6 D) (h127 : R127 D)
    (h1114 : R1114 D) (h162 : W3Thm162Ext G) (hTor : W3Lem148Torus G) (h1482 : W3Lem148_2 G)
    (h183 : W3Thm183 G) (h111 : W3Thm111 G) (h126 : R126 D) (h869 : F08.R869 D)
    (hC117 : C117 D V₀ V) (h1669 : Nat.card V₀ ≤ 4 → MBarGT D.M V₀ V 3)
    (h77 : Inputs1719.W4Lem7_7) (h106 : Inputs1719.W4Lem10_6Q)
    (hTim : CFSG.CGT.Timmesfeld75.NodeStatement) (hcat : ¬ CFSG.Blueprint.Catalog G)
    (h86 : W3Lem86_1 G) (h88 : W3Thm88 G) (h914N : W3Lem914N G) (h410 : W4Lem4_10)
    (h43c : W3Lem45_2Chief) (h618 : W3_6_18 G)
    (h93 : CFSG.LocalAnalysis.WeakClosure81.Thm93 V₀ D.T) (h416 : Inputs1719.W4Lem4_16)
    (hG5P : Gap17_5_A6Pair D V₀ V) :
    R17_5At D V₀ V := by
  have hKA1 : Inputs1719.K_A7Permuting := Inputs1719.k_A7Permuting_holds
  exact seventeen_five_of_A6Module hV h17_1 h82 h880 hKA1 hx h61 h66 h127 h1114 h162 hTor h1482
    h183 h111 h126 h869 hC117 h1669 h77 h106
    (gap17_5_A6Module_of hV h17_1
      (r17_4AtA_holds D h111 h126 h127 h618 hTim hcat h66 h88 h86 hx h61 h1114 h162 hTor h1482
        h183 hV h93 h1669 (Inputs1719.w4Lem4_16b_of_w4Lem4_16 h416) h77)
      hTim hcat h66 h86 h88 h126 h914N hG5P h410 h43c h869 h127 hC117
      Inputs1719.k_A6Exp4SThreePair_holds Inputs1719.k_A6AutOrder8_holds h106)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
