module

public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallBOneKFacts
import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2
import CFSG.LocalAnalysis.UniquenessCase.UC22P22ry
import CFSG.Holt.H78.BridgeCases
import CFSG.GroupTheory.PElementSubgroup
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallBasic
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallMcLLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallTitsLocal
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SmallRankOneKFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SzFiveTrans
public import CFSG.LocalAnalysis.AGLEmbedding.KFactReduceTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsIdent
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvableBorel
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs
public import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.AGLEmbedding.KFactProofs.SmallIdent
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Opp IsSpor)

theorem opp_top_eq_of_forall_mem {X : Type} [Group X] [Finite X] {p : ℕ} [hp : Fact p.Prime]
    {K : Subgroup X} [K.Normal] [IsSimpleGroup ↥K] (hKC : Subgroup.centralizer (K : Set X) = ⊥)
    (hpK : ∀ (x : X) (n : ℕ), x ^ p ^ n = 1 → x ∈ K) {P : Subgroup X} (hP : IsPGroup p ↥P)
    (hP1 : P ≠ ⊥) :
    Opp p (⊤ : Subgroup X) = K := by
  refine le_antisymm (CFSG.LocalAnalysis.UniquenessCase.UCK.opp_le_of_forall hpK) ?_
  have : (Opp p (⊤ : Subgroup X)).Normal := by
    simpa [Opp] using CFSG.LocalAnalysis.UniquenessCase.UC22.uc22p22r_pElementSubgroup_normal
  refine CFSG.Holt.H78.le_of_normal_of_centralizer_eq_bot hKC ?_
  intro hbot
  apply hP1
  have hle : P ≤ Opp p (⊤ : Subgroup X) :=
    CFSG.le_pElementSubgroup_of_isPGroup hp.out hP le_top
  rw [hbot] at hle
  exact le_bot_iff.mp hle


theorem isSolvable_or_opp_alt_or_fi22_of_kFacts
    (hId : CFSG.AGLEmbedding.KFactSmallIdent)
    (hTor : CFSG.AGLEmbedding.KFactOneLieTorus)
    (hCyc : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact)
    (hSch : CFSG.AGLEmbedding.KFactCatalogSchreier)
    (hJ4 : CFSG.AGLEmbeddingD2.D2HeisLocalAt (.sporadic .J4) fun q => q = 11)
    (hOutP : CFSG.AGLEmbedding.KFactSmallOutPPrime)
    (hbr : Nonempty
      (CFSG.Blueprint.NativeSporadic.Carrier .Fi22 ≃* (TauCeti.CFSGIndex.sporadic .Fi22).Group))
    {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {X : Type} [Group X] [Finite X]
    (hX : CFSG.Open.IsKGroup X) (hO : CFSG.pPrimeCore p X = ⊥)
    (h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X)) {N : Subgroup X}
    (hN : IsStronglyPEmbedded p N) :
    IsSolvable ↥N ∨ Nonempty (↥(Opp p (⊤ : Subgroup X)) ≃* alternatingGroup (Fin (2 * p))) ∨
      (p = 5 ∧ IsSpor ↥(Opp p (⊤ : Subgroup X)) .Fi22) := by
  classical
  have : Fact p.Prime := ⟨hp⟩
  have hp2 : p ≠ 2 := by omega
  obtain ⟨hKs, hKnab, hKn, hKC⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar hp hO hN
  set K := CFSG.generalizedFitting X with hKdef
  have : K.Normal := hKn
  have : IsSimpleGroup ↥K := hKs
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
      have hinn := hOutP ↥K hKs hKnab hcat p hp hp2 T hcyc hΓT hAut (fun h => by omega)
      have hPK1 : (P : Subgroup X) ⊓ K ≠ ⊥ := hPK
      have hOppK : Opp p (⊤ : Subgroup X) = K :=
        opp_top_eq_of_forall_mem hKC
          (fun x n hx => CFSG.LocalAnalysis.UniquenessCase.UCK.mem_of_forall_inner K hKC hinn hx)
          (P.isPGroup'.to_le inf_le_left) hPK1
      rcases hsmall with hlin | huni | halt | h34 | h5spor | h11J4
      ·
        have hD := CFSG.AGLEmbedding.smallRankOneData_of_small hp hp5 (Or.inl hlin) T
        exact Or.inl (isSolvable_of_isCoatom_normalizer hKC hout hD.maximal hD.solvable hle hne)
      ·
        have hD := CFSG.AGLEmbedding.smallRankOneData_of_small hp hp5 (Or.inr huni) T
        exact Or.inl (isSolvable_of_isCoatom_normalizer hKC hout hD.maximal hD.solvable hle hne)
      ·
        obtain ⟨e⟩ := halt
        exact Or.inr (Or.inl ⟨(MulEquiv.subgroupCongr hOppK).trans e⟩)
      ·
        omega
      ·
        rcases h5spor with ⟨rfl, hTits | hMcL | hFi22⟩
        · have hD := sporCore_of_isTitsGroup hKs hKnab hTits T
          exact Or.inl (isSolvable_of_isCoatom_normalizer hKC hout hD.maximal hD.solvable hle hne)
        · have hD := sporCore_of_isMcL hKs hKnab hMcL T
          exact Or.inl (isSolvable_of_isCoatom_normalizer hKC hout hD.maximal hD.solvable hle hne)
        · obtain ⟨f⟩ := hFi22
          exact Or.inr (Or.inr ⟨rfl,
            ⟨((MulEquiv.subgroupCongr hOppK).trans f).trans hbr.some.symm⟩⟩)
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

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
