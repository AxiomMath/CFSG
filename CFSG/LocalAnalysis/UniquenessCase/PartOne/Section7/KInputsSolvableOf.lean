module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableQ
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsIdent
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableBorel
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableKID
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableAltTen
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SzFiveTrans
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTitsLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallMcLLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactReduceTorus
public import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBasic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.AGLEmbedding.KFactProofs.SmallIdent

variable {G : Type} [Group G] [Finite G]


theorem stronglyEmbeddedSolvableQ_of_kFacts
    (hId : CFSG.AGLEmbedding.KFactSmallIdent)
    (hTor : CFSG.AGLEmbedding.KFactOneLieTorus)
    (hCyc : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hJ4 : CFSG.AGLEmbeddingD2.D2HeisLocalAt (.sporadic .J4) fun q => q = 11) :
    StronglyEmbeddedSolvableQ := by
  classical
  intro p hp hp5 X _ _ hX hO h2 N hN hcov
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
  have hout : Group.IsSolvable (Outer ↥K) := hSch ↥K hKs hKnab hcat
  have hle : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤ N.subgroupOf K := by
    rw [hT]
    exact normalizer_subgroupOf_le_of_isStronglyPEmbedded hN hPK
      (P.isPGroup'.to_le inf_le_left) (inf_le_left.trans hPN) inf_le_right
  have hne : N.subgroupOf K ≠ ⊤ := fun h =>
    CFSG.LocalAnalysis.UniquenessCase.UCK.not_le_of_isStronglyPEmbedded hN P hPN hPK T hT
      (Subgroup.subgroupOf_eq_top.mp h)
  by_cases hcyc : IsCyclic (T : Subgroup ↥K)
  ·
    have hcycP : IsCyclic ↥((P : Subgroup X) ⊓ K) := by
      rw [hT] at hcyc
      exact isCyclic_of_surjective (Subgroup.subgroupOfEquivOfLe inf_le_right)
        (Subgroup.subgroupOfEquivOfLe inf_le_right).surjective
    rcases hCyc X K hKn hKs hKnab hcat hKC p hp hp2 P hcycP hrk hΓ with ⟨h3, -⟩ | h5
    · omega
    · obtain ⟨rfl, hv, ⟨e⟩⟩ := h5
      have hSz := CFSG.AGLEmbeddingD2.sz32Normal_of_mulEquiv ⟨.suzuki 2, hv⟩ rfl hKn hKC e
      have hD := hSz.data T
      refine Or.inl (isSolvable_of_isCoatom_normalizer hKC hout ?_ ?_ hle hne)
      · refine ⟨?_, fun Y hY => ?_⟩
        · intro htop
          have h1 := hD.card_normalizer
          rw [htop, Subgroup.card_top, hSz.card] at h1
          norm_num at h1
        · rcases hD.maximal hY.le with h | h
          · exact absurd h hY.ne'
          · exact h
      · exact hD.isSolvable_normalizer
  · by_cases hAut : CFSG.Open.pRank p (⊤ : Subgroup (MulAut ↥K)) ≤ 2
    ·
      have hK2 : CFSG.Open.pRank p (⊤ : Subgroup ↥K) ≤ 2 :=
        (CFSG.AGLEmbedding.pRank_le_pRank_mulAut_of_nonabelian hKnab hp.one_lt
          (le_refl (CFSG.Open.pRank p (⊤ : Subgroup ↥K)))).trans hAut
      have hrank : CFSG.pRank p ↥(⊤ : Subgroup ↥K) =
          CFSG.Open.pRank p (⊤ : Subgroup ↥K) :=
        (CFSG.SectionRank.pRank_eq_open_pRank_top p ↥(⊤ : Subgroup ↥K)).trans
          (CFSG.SectionRank.pRank_eq_pRank_top_subgroup (⊤ : Subgroup ↥K)).symm
      have hsmall : CFSG.AGLEmbedding.IsSmallStrongP p ↥K := by
        refine hId ↥K hKs hKnab hcat p hp hp2 T hcyc hΓT ?_
        rw [hrank]
        exact hK2
      rcases hsmall with hlin | huni | halt | h34 | h5spor | h11J4
      ·
        have hD := CFSG.AGLEmbedding.smallRankOneData_of_small hp hp5 (Or.inl hlin) T
        exact Or.inl (isSolvable_of_isCoatom_normalizer hKC hout hD.maximal hD.solvable hle hne)
      ·
        have hD := CFSG.AGLEmbedding.smallRankOneData_of_small hp hp5 (Or.inr huni) T
        exact Or.inl (isSolvable_of_isCoatom_normalizer hKC hout hD.maximal hD.solvable hle hne)
      ·
        obtain ⟨e⟩ := halt
        by_cases hp5' : p = 5
        · subst p
          have hA := altTen_alternative hKC (by simpa using e) T hle hne
          exact Or.inr ⟨rfl, hA⟩
        · have hp7 : 7 ≤ p := by
            by_contra h7
            have hp6 : p ≤ 6 := by omega
            interval_cases p
            · exact hp5' rfl
            · norm_num at hp
          exact absurd
            (coverHasLargeTwoLocal_of_mulEquiv_alternatingGroup (n := 2 * p) (by omega) e) hcov
      ·
        omega
      ·
        rcases h5spor with ⟨rfl, hTits | hMcL | hFi22⟩
        · have hD := sporCore_of_isTitsGroup hKs hKnab hTits T
          exact Or.inl (isSolvable_of_isCoatom_normalizer hKC hout hD.maximal hD.solvable hle hne)
        · have hD := sporCore_of_isMcL hKs hKnab hMcL T
          exact Or.inl (isSolvable_of_isCoatom_normalizer hKC hout hD.maximal hD.solvable hle hne)
        · exact absurd (coverHasLargeTwoLocal_of_isFi22 hKs hFi22) hcov
      ·
        rcases h11J4 with ⟨rfl, hJ4K⟩
        have hD := sporCore_of_d2HeisLocalAt hp (by norm_num) hJ4 hKs hKnab hJ4K T
        exact Or.inl (isSolvable_of_isCoatom_normalizer hKC hout hD.maximal hD.solvable hle hne)
    ·
      obtain ⟨n, e, hF⟩ := hTor ↥K hKs hKnab hcat p hp2 T hcyc hΓT hAut
      have hTbot : (T : Subgroup ↥K) ≠ ⊥ := by
        intro h
        exact hcyc (h ▸ inferInstance)
      have hdvd : p ∣ Nat.card (T : Subgroup ↥K) := by
        obtain ⟨k, hk⟩ := T.isPGroup'.exists_card_eq
        have hk0 : k ≠ 0 := by
          rintro rfl
          refine hTbot (Subgroup.card_eq_one.1 ?_)
          simpa using hk
        rw [hk]
        exact dvd_pow_self p hk0
      have hleΓ : Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) ≤
          CFSG.Open.GLBCore p 1 (T : Subgroup ↥K) :=
        le_sSup ⟨T, le_rfl,
          CFSG.AGLEmbedding.KFactProofs.GLBCoreNormalizer.one_le_pRank_of_dvd hp hdvd, rfl⟩
      have heq : CFSG.Open.GLBCore p 1 (T : Subgroup ↥K) =
          Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K) :=
        (hF.borel_coatom.le_iff.1 hleΓ).resolve_left hΓT
      have hsol : Group.IsSolvable
          (Subgroup.normalizer ((T : Subgroup ↥K) : Set ↥K)) :=
        heq ▸ (CFSG.AGLEmbedding.kFactOneLieBorelSolvable_of_torus hTor
          ↥K hKs hKnab hcat p hp hp2 T hcyc hΓT hAut)
      exact Or.inl (isSolvable_of_isCoatom_normalizer hKC hout hF.borel_coatom hsol hle hne)

theorem stronglyEmbeddedSolvable_of_kFacts
    (hId : CFSG.AGLEmbedding.KFactSmallIdent)
    (hTor : CFSG.AGLEmbedding.KFactOneLieTorus)
    (hCyc : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hJ4 : CFSG.AGLEmbeddingD2.D2HeisLocalAt (.sporadic .J4) fun q => q = 11) :
    StronglyEmbeddedSolvable :=
  (stronglyEmbeddedSolvableQ_of_kFacts hId hTor hCyc hSch hJ4).toStronglyEmbeddedSolvable

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
