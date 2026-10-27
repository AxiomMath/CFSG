module

public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallIdent
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieMSideDefsAux
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.J3InvolveCore
public import CFSG.LocalAnalysis.SectionRank.Framework.SylowRank
public import CFSG.RankThree.PartOne.CTP.StrongPGlue

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

theorem exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded {X : Type} [Group X] [Finite X]
    {p : ℕ} [Fact p.Prime] (hO : CFSG.pPrimeCore p X = ⊥) {N K : Subgroup X} [K.Normal]
    (hK : K ≠ ⊥) (hN : IsStronglyPEmbedded p N) :
    ∃ P : Sylow p X, (P : Subgroup X) ≤ N ∧ (P : Subgroup X) ⊓ K ≠ ⊥ ∧
      ∃ T : Sylow p ↥K, (T : Subgroup ↥K) = ((P : Subgroup X) ⊓ K).subgroupOf K ∧
        CFSG.Open.GLBCore p 1 (T : Subgroup ↥K) ≠ ⊤ := by
  obtain ⟨P₀, ⟨-, hP₀p, hP₀i⟩, hP₀N⟩ := hN.exists_isSylowOf_le
  set P : Sylow p X := hP₀p.toSylow (by simpa [Subgroup.relIndex_top_right] using hP₀i) with hPdef
  have hPN : (P : Subgroup X) ≤ N := by rw [hPdef, IsPGroup.toSylow_coe]; exact hP₀N
  have hPK : (P : Subgroup X) ⊓ K ≠ ⊥ :=
    CFSG.LocalAnalysis.UniquenessCase.UCK.inf_ne_bot_of_pPrimeCore hO hK P
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal P (N := K)
  exact ⟨P, hPN, hPK, T, hT,
    CFSG.LocalAnalysis.UniquenessCase.UCK.glbCore_sylow_ne_top hN P hPN hPK T hT⟩

theorem identification_of_isStronglyPEmbedded (hId : CFSG.AGLEmbedding.KFactSmallIdent)
    (hLie : CFSG.AGLEmbedding.KFactOneLieIdent)
    (hCyc : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact)
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.IsKGroup X) (hO : CFSG.pPrimeCore p X = ⊥)
    (h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) {N : Subgroup X}
    (hN : IsStronglyPEmbedded p N) :
    CFSG.AGLEmbedding.IsSmallStrongP p ↥(CFSG.generalizedFitting X) ∨
      (∃ d : TauCeti.ValidLieTypeIndex,
        ((∃ n : ℕ, 3 ≤ n ∧ CFSG.AGLEmbedding.IsLinTwoIndex p n d) ∨
          (CFSG.AGLEmbedding.IsUnitaryIndex p d ∧ 2 ≤ d.1.fieldExponent) ∨
          CFSG.AGLEmbedding.IsReeGTwoIndex p d) ∧
        Nonempty (↥(CFSG.generalizedFitting X) ≃* CFSG.AGLEmbedding.CatGroup d)) ∨
      (p = 5 ∧ CFSG.RankThree.PartOne.Census3.IsoLie ↥(CFSG.generalizedFitting X) (.suzuki 2)) := by
  classical
  haveI : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hKs, hKnab, hKn, hKC⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar hp hO hN
  set K := CFSG.generalizedFitting X with hKdef
  haveI : K.Normal := hKn
  haveI : IsSimpleGroup ↥K := hKs
  have hcat : CFSG.Open.IsCatalogGroup ↥K :=
    hX.isCatalogGroup_of_surjective K hKnab (MonoidHom.id _) Function.surjective_id
  have hK1 : K ≠ ⊥ := (Subgroup.nontrivial_iff_ne_bot K).1 inferInstance
  obtain ⟨P, hPN, hPK, T, hT, hΓT⟩ :=
    exists_sylow_glbCore_ne_top_of_isStronglyPEmbedded hO hK1 hN
  have hrk : 2 ≤ CFSG.Open.pRank p (P : Subgroup X) := by
    rw [(CFSG.SectionRank.pRank_sylow P).1]
    exact h2
  have hΓ : CFSG.Open.rankThreeGamma 1 p (P : Subgroup X) ≠ ⊤ :=
    ne_top_of_le_ne_top hN.1
      (CFSG.LocalAnalysis.UniquenessCase.UCK.glbCore_le_of_isStronglyPEmbedded hN P.isPGroup' hPN)
  by_cases hcyc : IsCyclic (T : Subgroup ↥K)
  ·
    have hcycP : IsCyclic ↥((P : Subgroup X) ⊓ K) := by
      rw [hT] at hcyc
      exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe inf_le_right)
        (Subgroup.subgroupOfEquivOfLe inf_le_right).surjective
    rcases hCyc X K hKn hKs hKnab hcat hKC p hp hp2 P hcycP hrk hΓ with ⟨h3, -⟩ | h5
    · omega
    · exact Or.inr (Or.inr h5)
  · by_cases hAut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 2
    ·
      left
      have hK2 : CFSG.Open.pRank p (⊤ : Subgroup ↥K) ≤ 2 :=
        (CFSG.AGLEmbedding.pRank_le_pRank_mulAut_of_nonabelian hKnab hp.one_lt
          (le_refl (CFSG.Open.pRank p (⊤ : Subgroup ↥K)))).trans hAut
      have hrank : CFSG.pRank p ↥(⊤ : Subgroup ↥K) = CFSG.Open.pRank p (⊤ : Subgroup ↥K) :=
        (CFSG.SectionRank.pRank_eq_open_pRank_top p ↥(⊤ : Subgroup ↥K)).trans
          (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (⊤ : Subgroup ↥K)).symm
      refine hId ↥K hKs hKnab hcat p hp hp2 T hcyc hΓT ?_
      rw [hrank]
      exact hK2
    ·
      exact Or.inr (Or.inl (hLie ↥K hKs hKnab hcat p hp hp2 T hcyc hΓT hAut))

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
