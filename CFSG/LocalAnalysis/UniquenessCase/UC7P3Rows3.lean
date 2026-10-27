module

public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus
import CFSG.LocalAnalysis.UniquenessCase.UC6K35Red2
import CFSG.LocalAnalysis.UniquenessCase.UC7P3ThreeOCSetup
import CFSG.LocalAnalysis.UniquenessCase.UC22S13xj
import CFSG.RankThree.PartOne.S12.Sec1511SPEFStar
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Quotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3ConclusionPlus Gls3StronglyThreeEmbeddedPlus gammaCore)

theorem gammaCore_eq_of_gls3ConclusionPlus {X : Type} [Group X] [Finite X] {K P : Subgroup X}
    (h : Gls3ConclusionPlus X K P) :
    gammaCore 3 1 K (P ⊓ K) = K ⊓ normalizer ((P ⊓ K : Subgroup X) : Set X) := by
  obtain ⟨-, -, h⟩ := h
  rcases h with ⟨-, -, -, -, hN, -⟩ | ⟨-, -, -, -, hN, -⟩ | ⟨-, -, -, hN, -⟩ |
      ⟨-, -, -, -, hN, -⟩ | ⟨-, -, -, -, hN, -⟩ | ⟨-, -, -, -, -, hN, -⟩ | ⟨-, -, -, -, hN, -⟩ <;>
    exact hN

theorem gls3ConclusionPlus_of_isStronglyPEmbedded (hG3 : Gls3StronglyThreeEmbeddedPlus)
    {p : ℕ} (hp3 : p = 3) {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsKGroup X)
    (hO : CFSG.pPrimeCore p X = ⊥) (h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X))
    {N : Subgroup X} (hN : IsStronglyPEmbedded p N) (P : Sylow p X) :
    Gls3ConclusionPlus X (CFSG.generalizedFitting X) (P : Subgroup X) := by
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hKs, hKnab, hKn, hKC⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar Nat.prime_three hO hN
  obtain ⟨g, hg⟩ := hN.exists_conj_ge (P := (P : Subgroup X))
    ⟨le_top, P.isPGroup', by rw [Subgroup.relIndex_top_right]; exact P.not_dvd_index⟩
  have hΓ : gammaCore 3 1 ⊤ (P : Subgroup X) < ⊤ := by
    refine lt_top_iff_ne_top.2 fun h => (hN.conj g).1 (top_le_iff.1 ?_)
    rw [← h]
    exact CFSG.LocalAnalysis.UniquenessCase.UCK.gammaCore_le_of_isStronglyPEmbedded (hN.conj g)
      P.isPGroup' hg
  have hrk : 2 ≤ CFSG.Open.pRank 3 (P : Subgroup X) := by
    rw [(CFSG.SectionRank.pRank_sylow P).1]
    exact h2
  exact hG3 X hX _ hKn hKs hKnab hKC P hrk hΓ

theorem inf_eq_and_le_normalizer_of_isStronglyPEmbedded (hG3 : Gls3StronglyThreeEmbeddedPlus)
    {p : ℕ} (hp3 : p = 3) {X : Type} [Group X] [Finite X] (hX : CFSG.Open.IsKGroup X)
    (hO : CFSG.pPrimeCore p X = ⊥) (h2 : 2 ≤ CFSG.Open.pRank p (⊤ : Subgroup X))
    {N : Subgroup X} (hN : IsStronglyPEmbedded p N) (P : Sylow p X)
    (hPN : (P : Subgroup X) ≤ N) :
    N ⊓ CFSG.generalizedFitting X = CFSG.generalizedFitting X ⊓
        normalizer (((P : Subgroup X) ⊓ CFSG.generalizedFitting X : Subgroup X) : Set X) ∧
      N ≤ normalizer (((P : Subgroup X) ⊓ CFSG.generalizedFitting X : Subgroup X) : Set X) := by
  have h := gls3ConclusionPlus_of_isStronglyPEmbedded hG3 hp3 hX hO h2 hN P
  subst hp3
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨hKs, -, hKn, -⟩ := CFSG.RankThree.PartOne.Sec1511.spe_fstar Nat.prime_three hO hN
  haveI := hKn
  haveI := hKs
  obtain ⟨T, hT⟩ := CFSG.Glauberman.sylow_inf_normal P (N := CFSG.generalizedFitting X)
  exact ThreeOC.inf_eq_and_le_normalizer hN P hPN
    (CFSG.LocalAnalysis.UniquenessCase.UCK.inf_ne_bot_of_pPrimeCore hO
      ((Subgroup.nontrivial_iff_ne_bot _).1 inferInstance) P) T hT h.2.1
    (gammaCore_eq_of_gls3ConclusionPlus h)

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem gls3ConclusionPlus_quotient (hG3 : Gls3StronglyThreeEmbeddedPlus) (k : Sec7Core4 G)
    (hp3 : k.p = 3) {H : Subgroup G} (hH : Config k H)
    (P : Sylow k.p (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) :
    Gls3ConclusionPlus (↥H ⧸ CFSG.pPrimeCore k.p ↥H)
      (CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H))
      (P : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) :=
  gls3ConclusionPlus_of_isStronglyPEmbedded hG3 hp3
    ((k.standing.kProper.isKGroup H hH.ne_top).quotient _)
    (CFSG.pPrimeCore_quotient_eq_bot k.prime) (k.two_le_pRank_quotient_pPrimeCore hH)
    (k.isStronglyPEmbedded_map_quotient_pPrimeCore hH) P

theorem inf_eq_and_le_normalizer_quotient (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (k : Sec7Core4 G) (hp3 : k.p = 3) {H : Subgroup G} (hH : Config k H)
    (P : Sylow k.p (↥H ⧸ CFSG.pPrimeCore k.p ↥H))
    (hPN : (P : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) ≤
      ((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))) :
    ((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) ⊓
        CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H) =
      CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H) ⊓
        normalizer (((P : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) ⊓
          CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H) :
            Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) : Set (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) ∧
      ((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) ≤
        normalizer (((P : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) ⊓
          CFSG.generalizedFitting (↥H ⧸ CFSG.pPrimeCore k.p ↥H) :
            Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) : Set (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) :=
  inf_eq_and_le_normalizer_of_isStronglyPEmbedded hG3 hp3
    ((k.standing.kProper.isKGroup H hH.ne_top).quotient _)
    (CFSG.pPrimeCore_quotient_eq_bot k.prime) (k.two_le_pRank_quotient_pPrimeCore hH)
    (k.isStronglyPEmbedded_map_quotient_pPrimeCore hH) P hPN

theorem exists_sylow_map_of_isSylowOf (k : Sec7Core4 G) {H : Subgroup G} (hH : Config k H)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf k.p P (H ⊓ k.M)) :
    ∃ P' : Sylow k.p (↥H ⧸ CFSG.pPrimeCore k.p ↥H),
      (P' : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) =
          (P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) ∧
        (P' : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) ≤
          ((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) := by
  haveI : Fact k.p.Prime := ⟨k.prime⟩
  have hPH : P ≤ H := hP.le.trans inf_le_left
  have hP1 : P ≠ ⊥ := by
    rintro rfl
    obtain ⟨-, -, hi⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hP
    rw [Subgroup.relIndex_bot_left] at hi
    exact hi ((dvd_pow_self k.p two_ne_zero).trans ((pow_dvd_pow k.p hH.two_le_pRank).trans
      (CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card k.p k.prime _)))
  obtain ⟨Q, hQ⟩ :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.uc22s13xj_isSylowOf_of_inf k.strong hP hP1
  have hQP : (Q : Subgroup ↥H) = P.subgroupOf H :=
    Subgroup.map_subtype_inj.mp (hQ.trans (Subgroup.map_subgroupOf_eq_of_le hPH).symm)
  refine ⟨Q.mapSurjective (QuotientGroup.mk'_surjective _), ?_, ?_⟩
  · rw [Sylow.coe_mapSurjective, hQP]
  · rw [Sylow.coe_mapSurjective, hQP]
    exact Subgroup.map_mono (Subgroup.subgroupOf_mono H hP.le)

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
