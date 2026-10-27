module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.NineTwentyTwoSp5
public import CFSG.CGT.PushingUpLit.CGT6M.FiveHeisStructure
public import CFSG.CGT.PushingUpLit.CGT6M.FiveDataPSL
public import CFSG.Adapters.ClassicalCatalogLinearUnitary
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne

open CFSG.Open
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

section Certified


private theorem not_isSmallStrongP_five {X : Type} [Group X] [Finite X]
    (hcard : Nat.card X = 372000) (hsimple : IsSimpleGroup X)
    (hsmall : CFSG.AGLEmbedding.IsSmallStrongP 5 X) : False := by
  rcases hsmall with hL2 | hU3 | hAlt | ⟨h3, -⟩ | ⟨-, hrest⟩ | ⟨h11, -⟩
  · have h := CFSG.AGLEmbedding.KFactProofs.SmallIdent.card_of_isSmallLinTwo
      (p := 5) Nat.prime_five (by norm_num) hL2
    rw [hcard] at h
    norm_num at h
  · have h := CFSG.AGLEmbedding.KFactProofs.SmallIdent.card_mul_gcd_of_isSmallUnitary
      (p := 5) hU3
    rw [hcard] at h
    norm_num at h
  · have h := CFSG.AGLEmbedding.KFactProofs.SmallIdent.card_of_isAltTwoP
      (p := 5) Nat.prime_five hAlt
    rw [hcard] at h
    norm_num at h
  · norm_num at h3
  · rcases hrest with hT | hMcL | hFi
    · have h := CFSG.AGLEmbedding.KFactProofs.SmallIdent.card_of_isTitsGroup hT
      rw [hcard] at h
      norm_num at h
    · have h := CFSG.AGLEmbedding.KFactProofs.SmallIdent.card_of_isMcL hsimple hMcL
      rw [hcard] at h
      norm_num at h
    · have h := CFSG.AGLEmbedding.KFactProofs.SmallIdent.card_of_isFi22 hsimple hFi
      rw [hcard] at h
      norm_num at h
  · norm_num at h11

theorem k_L35NoStrongFive_of_smallIdent (hSI : CFSG.AGLEmbedding.KFactSmallIdent) :
    K_L35NoStrongFive := by
  intro X _ _ hLie N hNne hN
  have : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  have hQ : CFSG.Open.StatedClassicalModel X .PSL 3 5 1 :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hLie
  have hsimple : IsSimpleGroup X :=
    CFSG.Open.StatedAPI.isSimpleGroup_of_statedClassicalModel hQ
  have hcard : Nat.card X = 372000 :=
    CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_five hQ
  have hd : CFSG.CGT.PushingUpLit.CGT6M.HeisData X :=
    CFSG.CGT.PushingUpLit.CGT6M.heisData_PSL3_5 hQ
  have hnab : ∃ a b : X, a * b ≠ b * a := hd.exists_noncomm
  have hcat : CFSG.Open.IsCatalogGroup X :=
    CFSG.ClassicalModels.statedClassicalModel_PSL_inCatalog X 3 5 1 (by norm_num) hQ
      (by norm_num) (by norm_num)
  have hrk : CFSG.pRank 5 (⊤ : Subgroup X) ≤ 2 := by
    rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
    exact hd.pRank_le_two
  obtain ⟨T⟩ : Nonempty (Sylow 5 X) := inferInstance
  have hTcyc : ¬ IsCyclic (T : Subgroup X) := hd.not_isCyclic_sylow T
  have hTsyl : CFSG.RankThree.PartOne.IsSylowOf 5 (T : Subgroup X) ⊤ :=
    ⟨le_top, T.isPGroup',
      by simpa [Subgroup.relIndex_top_right] using T.not_dvd_index⟩
  obtain ⟨g, hgT⟩ :=
    CFSG.RankThree.PartOne.IsStronglyPEmbedded.exists_conj_ge hN hTsyl
  have hN' : IsStronglyPEmbedded 5
      (CFSG.RankThree.PartOne.StrongP.conjSub g N) := hN.conj g
  have hN'ne : CFSG.RankThree.PartOne.StrongP.conjSub g N ≠ ⊤ := fun h =>
    hNne (CFSG.RankThree.PartOne.StrongP.conjSub_eq_top_iff.mp h)
  have hΓ : CFSG.Open.GLBCore 5 1 (T : Subgroup X) ≠ ⊤ :=
    ne_top_of_le_ne_top hN'ne
      (CFSG.LocalAnalysis.UniquenessCase.UCK.glbCore_le_of_isStronglyPEmbedded hN' T.isPGroup'
        hgT)
  exact not_isSmallStrongP_five hcard hsimple
    (hSI X hsimple hnab hcat 5 Nat.prime_five (by norm_num) T hTcyc hΓ hrk)

end Certified

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
