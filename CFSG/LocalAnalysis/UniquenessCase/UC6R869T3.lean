module

public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.UC6R869NS3
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.GroupTheory.PCore.PrimeSetCore
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.SectionRank.SubgroupRank
public import CFSG.RankThree.PartOne.CTP.StrongPQuotient
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

namespace R869S

theorem two_le_pRank_quotient_pPrimeCore {p : ℕ} (hp : p.Prime) {M H : Subgroup G}
    (hrank : 2 ≤ CFSG.Open.pRank p (H ⊓ M)) :
    2 ≤ CFSG.Open.pRank p (⊤ : Subgroup (↥H ⧸ CFSG.pPrimeCore p ↥H)) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have h1 : CFSG.Open.pRank p (H ⊓ M) ≤ CFSG.Open.pRank p (⊤ : Subgroup ↥H) := by
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup H]
    exact CFSG.SectionRank.pRank_mono hp.one_lt inf_le_left
  rw [CFSG.SectionRank.pRank_quotient_eq (CFSG.pPrimeCore p ↥H)
    ((hp.coprime_iff_not_dvd).mp (CFSG.pPrimeCore_coprime_card (G := ↥H) (p := p)))]
  exact hrank.trans h1

theorem isStronglyPEmbedded_map_quotient_pPrimeCore {p : ℕ} (hp : p.Prime) {M H : Subgroup G}
    (hM : IsStronglyPEmbedded p M) (hHM : ¬ H ≤ M) (hrank : 2 ≤ CFSG.Open.pRank p (H ⊓ M)) :
    IsStronglyPEmbedded p
      (((H ⊓ M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) := by
  haveI : Fact p.Prime := ⟨hp⟩
  have hdvd : p ∣ Nat.card (H ⊓ M : Subgroup G) :=
    (dvd_pow_self p (by norm_num : (2 : ℕ) ≠ 0)).trans
      ((pow_dvd_pow p hrank).trans
        (CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card p hp (H ⊓ M)))
  have hKle : CFSG.pPrimeCore p ↥H ≤ (H ⊓ M).subgroupOf H := fun x hx =>
    Subgroup.mem_subgroupOf.mpr ⟨x.2,
      CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.pPrimeCore_le hM hp hrank
        (Subgroup.mem_map_of_mem H.subtype hx)⟩
  exact (hM.subgroupOf hHM hdvd).map_quotient hKle
    ((hp.coprime_iff_not_dvd).mp (CFSG.pPrimeCore_coprime_card (G := ↥H) (p := p)))

theorem normalizer_le_of_strongThree (hS : Standing4 G) (hK3 : StronglyEmbeddedThree)
    {M L A : Subgroup G} (hM : IsStronglyPEmbedded 3 M) (hLM : L ≤ M) (hLperf : ⁅L, L⁆ = L)
    (h2 : 2 ≤ CFSG.Open.pRank 3 L) {r : ℕ} (hr : r.Prime) (hAM : A ≤ M)
    (hAr : Nat.card A = r) (hY : (L ⊓ centralizer (A : Set G)) ⊔ pCoreOf 2 L = L) :
    normalizer (A : Set G) ≤ M := by
  refine normalizer_le_of_solvable_or hS.simple Nat.prime_three (by norm_num) hLM hLperf h2
    (fun h => absurd h (by norm_num)) hr hAM hAr hY fun H htop hHM hrank => Or.inl ?_
  have hKH : CFSG.Open.IsKGroup ↥H :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper hS.kProper htop
  exact (hK3 _ (CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hKH (CFSG.pPrimeCore 3 ↥H))
    (CFSG.pPrimeCore_quotient_eq_bot Nat.prime_three)
    (two_le_pRank_quotient_pPrimeCore Nat.prime_three hrank) _
    (isStronglyPEmbedded_map_quotient_pPrimeCore Nat.prime_three hM hHM hrank)).2.2.2

end R869S

end CFSG.LocalAnalysis.UniquenessCase.UC6
