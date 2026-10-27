module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S213Rest15UnitaryEndgame
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4 PartIAt)


theorem rest15_false_of_linear_lie_nonexceptional
    {G : Type} [Group G] [Finite G]
    (_hS : Standing4 G) (_hU : uniqueFourUnique G) (S : Setup4 G)
    (_hMS : S.InMSigma) (_hPart : PartIAt S.M)
    {L X H K P : Subgroup G} (_hL : L ∈ calC S.M)
    (_hLN : S.M ≤ normalizer (L : Set G)) (_hthin : ¬ F08.Thin8 L)
    (_hXL : X ≤ L) (_hsupp : X ⊔ pCoreOf 2 L = L)
    (_hHtop : H ≠ ⊤) (_hHr : CFSG.Open.pRank 3 H ≤ 3)
    (_hnotStrong : ¬ CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 S.M)
    (hXcomp : CFSG.Open.IsComponentOf X (H ⊓ S.M))
    (hKcomp : CFSG.Open.IsComponentOf K H) (hXK : X ≤ K) (hKM : ¬ K ≤ S.M)
    (hX : CFSG.Blueprint.LieModel X .PSL 3 2 2)
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P X)
    (hGamma : rankThreeGamma 1 3 P ≤ S.M)
    (_hNormal : (X.subgroupOf (H ⊓ S.M)).Normal)
    (_hGammaH : rankThreeGamma 1 3 (P.subgroupOf H) ≤
      (normalizer (X : Set G)).subgroupOf H)
    (hZK : ¬ 3 ∣ Nat.card (center K))
    (_hAlt : ¬ ∃ n : ℕ, 5 ≤ n ∧
      Nonempty (K ⧸ center K ≃* alternatingGroup (Fin n)))
    {d : TauCeti.ValidLieTypeIndex}
    (e : K ⧸ center K ≃* (TauCeti.CFSGIndex.lie d).Group)
    (hchar : 3 ≠ d.1.characteristic)
    (hex : ¬ CFSG.AGLEmbeddingD2.IsD2SeitzException 3 d.1) : False := by
  have hXr : 2 ≤ CFSG.Open.pRank 3 X := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup]
    exact hX.two_le_pRank_psl3_of_dvd Nat.prime_three (by norm_num)
  have hPr : 2 ≤ CFSG.Open.pRank 3 P := by
    rwa [CFSG.LocalAnalysis.RankThreeUC.PrimeRankSylowTransport.pRank_sylow
      Nat.prime_three hP]
  obtain ⟨E, hEP, hE, hEc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank Nat.prime_three hPr
  have hEX : E ≤ X := hEP.trans hP.le
  have hXs : IsSimpleGroup X := hX.isSimpleGroup_of_mem_classicalTags
    (by simp [CFSG.Blueprint.classicalTags])
  exact false_of_unitary_plane_generation hEP hE hGamma hKM
    (plane_generation_of_coprime_center hXK hXcomp.2.2 hXs hKcomp.2.2 hEX
      hE hEc hZK d e hchar hex CFSG.LieType.SeitzGeneration.kFactSeitzRankTwo_holds)

end CFSG.LocalAnalysis.UniquenessCase.UC22
