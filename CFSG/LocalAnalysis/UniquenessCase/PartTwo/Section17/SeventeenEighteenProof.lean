module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsB
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicArithHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicCoverHolds
public import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
public import CFSG.LocalAnalysis.UniquenessCase.UC22P20p
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenNineTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataKParam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.SporadicThreePermutingLe
public import CFSG.ClassicalInvolution.SmallCases.UpgradeCoverClassical
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma53
public import CFSG.HardMathSupport.Solomon.LocalBalance.Lemma54
public import CFSG.LieType.SteinbergBRMulEquivCores
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
public import CFSG.Quasithin.Vol2.Ch10SecKGA318
public import CFSG.RankThree.PartTwo.Sec3.TwoThreeStructure

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]



@[expose] def B17_18Bound (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ (hV : Hyp125 D V₀ V) (L : Subgroup G), Ctx17_17 D V₀ V L →
    2 < CFSG.Open.pRank 3 (UC22.conjClosure D.M L) → D.k = 1 → (L.subgroupOf D.M).Normal →
    IsSpor (BarInf L) .ONan →
      bBar (UC22.conjClosure D.M L) D.M V₀ V hV.isElemAbelian + 3 <
        mBar D.M V₀ V hV.isElemAbelian

@[expose] def Gap17_18Reduction (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, Ctx17_17 D V₀ V L → 2 < CFSG.Open.pRank 3 (UC22.conjClosure D.M L) →
    D.k = 1 ∧
      ((∃ X : Subgroup G, F11.InP11 D X) ∨
        ((L.subgroupOf D.M).Normal ∧ IsSpor (BarInf L) .ONan))

@[expose] def Gap17_18ReductionResidual (D : Data G) (V₀ V : Subgroup G) : Prop :=
  ∀ L : Subgroup G, Ctx17_17 D V₀ V L → 2 < CFSG.Open.pRank 3 (UC22.conjClosure D.M L) →
    (CFSG.Open.pRank 3 L ≤ 2 ∨ (IsSpor (BarInf L) .ONan ∧ ¬ (L.subgroupOf D.M).Normal)) →
      D.k = 1 ∧
        ((∃ X : Subgroup G, F11.InP11 D X) ∨
          ((L.subgroupOf D.M).Normal ∧ IsSpor (BarInf L) .ONan))

theorem k_eq_one_of_pRank_gt_two (D : Data G) (V₀ V : Subgroup G) (h82 : F08.R82 D)
    {L : Subgroup G} (c : Ctx17_17 D V₀ V L) (h3L : 2 < CFSG.Open.pRank 3 L) :
    D.k = 1 :=
  Data.k_eq_one_of_isStronglyPEmbedded D
    (h82 L ⟨c.mem_calC.1, c.mem_calC.2.1, h3L, Or.inl (s15_Three_qs_of_open c.mem_calC.2.2)⟩)

theorem exists_inP11_of_three_rank_gt_two (D : Data G) (V₀ V : Subgroup G)
    (hKS1 : Inputs1719.K_SporadicThreePermutingLe (CFSG.Open.pRank 3 D.M))
    (hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    {L : Subgroup G} (c : Ctx17_17 D V₀ V L) (h3L : 2 < CFSG.Open.pRank 3 L)
    (hON : ¬ IsSpor (BarInf L) .ONan) :
    ∃ X : Subgroup G, F11.InP11 D X := by
  obtain ⟨s, hs⟩ := c.sporadic
  obtain ⟨eBI⟩ := UC22.uc22p21k_barInf_equiv_of_calC c.mem_calC
  have hperm := exists_permutes_three_of_calC (D := D) (L := L) c.mem_calC ?_
  · obtain ⟨X, hXM, -, hXp, hXexp, hXnc, hXperm⟩ := hperm
    exact ⟨X, inP11_of_strongly Nat.prime_three (by norm_num) hstr hXM hXp hXexp hXnc hXperm⟩
  intro Y _ _ K hKn hKq hKodd he hcent hidx S hS
  obtain ⟨e⟩ := he
  have hoddZ : Odd (Nat.card (Subgroup.center ↥K)) := hKodd
  have hsporK : IsSpor (↥K ⧸ Subgroup.center ↥K) s := by
    obtain ⟨eS⟩ := hs
    let eZ : (↥K ⧸ Subgroup.center ↥K) ≃*
        (Bar2 L ⧸ Subgroup.center (Bar2 L)) :=
      QuotientGroup.congr _ _ e (Subgroup.map_center_eq e)
    exact ⟨(eZ.trans eBI.symm).trans eS⟩
  have hKON : s ≠ .ONan := by
    rintro rfl
    exact hON hs
  have hKL : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) = CFSG.Open.pRank 3 L := by
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv (p := 3) (by norm_num) e,
      pRank_bar2_eq_of_odd (Y := L) (p := 3) Nat.prime_three (by norm_num)]
  have hm3 : 2 < CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) := hKL ▸ h3L
  have hm3le : CFSG.Open.pRank 3 (⊤ : Subgroup ↥K) ≤ CFSG.Open.pRank 3 D.M :=
    hKL ▸ CFSG.SectionRank.pRank_mono (by norm_num) c.mem_calC.1.le
  exact hKS1 Y K S s hKn hKq hoddZ hsporK hcent hidx hS hm3 hm3le hKON

theorem gap17_18Reduction (D : Data G) (V₀ V : Subgroup G) (h82 : F08.R82 D)
    (hKS1 : Inputs1719.K_SporadicThreePermutingLe (CFSG.Open.pRank 3 D.M))
    (hRes : Gap17_18ReductionResidual D V₀ V) :
    Gap17_18Reduction D V₀ V := by
  intro L c h3
  classical
  by_cases h2 : CFSG.Open.pRank 3 L ≤ 2
  · exact hRes L c h3 (Or.inl h2)
  · push Not at h2
    have hk : D.k = 1 := k_eq_one_of_pRank_gt_two D V₀ V h82 c h2
    refine ⟨hk, ?_⟩
    by_cases hON : IsSpor (BarInf L) .ONan
    · by_cases hN : (L.subgroupOf D.M).Normal
      · exact Or.inr ⟨hN, hON⟩
      · exact (hRes L c h3 (Or.inr ⟨hON, hN⟩)).2
    · refine Or.inl ?_
      have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
        by_contra h
        exact absurd ((Data.k_eq_two_iff D).2 h) (by omega)
      exact exists_inP11_of_three_rank_gt_two D V₀ V hKS1 hstr c h2 hON

section Certificates



theorem two_lt_pRank_three_of_isSpor_ONan (D : Data G)
    {V₀ V : Subgroup G} {L : Subgroup G} (c : Ctx17_17 D V₀ V L)
    (hO : IsSpor (BarInf L) .ONan) :
    2 < CFSG.Open.pRank 3 L := by
  have hq : CFSG.Open.IsQuasisimple (Bar2 L) := c.mem_calC.2.2
  have hodd : Odd (Nat.card (Subgroup.center (Bar2 L))) :=
    UC22.uc22p20p_odd_center_bar2 ↥L
  obtain ⟨eBI⟩ := UC22.uc22p21k_barInf_equiv_of_calC c.mem_calC
  obtain ⟨eO⟩ := hO
  have hspor : IsSpor (Bar2 L ⧸ Subgroup.center (Bar2 L)) .ONan :=
    ⟨eBI.symm.trans eO⟩
  have h4q : 4 ≤ CFSG.Open.pRank 3
      (⊤ : Subgroup (Bar2 L ⧸ Subgroup.center (Bar2 L))) :=
    Inputs1719.k_ONanQuotThreeRank_holds _ hspor
  rw [← pRank_bar2_eq_of_odd (Y := L) (p := 3) Nat.prime_three (by norm_num)]
  by_contra hle
  push Not at hle
  have hcov := Inputs1719.k_SporadicCoverThreeRank_holds (Bar2 L) .ONan hq hodd hspor hle
  omega

end Certificates

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
