module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Config
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
import CFSG.RankThree.PartOne.CTP.StrongPQuotient

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem two_le_pRank_quotient_pPrimeCore (k : Sec7Core4 G) {H : Subgroup G}
    (hH : Config k H) :
    2 ≤ CFSG.Open.pRank k.p (⊤ : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) := by
  have hp : k.p.Prime := k.prime
  haveI : Fact k.p.Prime := ⟨hp⟩
  obtain ⟨E, hEHM, hE, hEcard⟩ := CFSG.SectionRank.exists_pRank hp.one_lt (H ⊓ k.M)
  have hEH : E ≤ H := hEHM.trans inf_le_left
  have hEsub : CFSG.Open.IsElemAbelian k.p (E.subgroupOf H) :=
    CFSG.Open.IsElemAbelian.subgroupOf hE H
  have hcard : Nat.card (E.subgroupOf H) = k.p ^ CFSG.Open.pRank k.p (H ⊓ k.M) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hEH).toEquiv, hEcard]
  have hmono : CFSG.Open.pRank k.p (H ⊓ k.M) ≤ CFSG.Open.pRank k.p (⊤ : Subgroup ↥H) :=
    CFSG.SectionRank.le_pRank hp.one_lt le_top hEsub hcard
  have hquot : CFSG.Open.pRank k.p (⊤ : Subgroup (↥H ⧸ CFSG.pPrimeCore k.p ↥H)) =
      CFSG.Open.pRank k.p (⊤ : Subgroup ↥H) :=
    CFSG.SectionRank.pRank_quotient_eq (CFSG.pPrimeCore k.p ↥H)
      ((hp.coprime_iff_not_dvd).mp
        (CFSG.pPrimeCore_coprime_card (G := ↥H) (p := k.p)))
  exact hquot.symm ▸ hH.two_le_pRank.trans hmono

theorem isStronglyPEmbedded_map_quotient_pPrimeCore (k : Sec7Core4 G)
    {H : Subgroup G} (hH : Config k H) :
    CFSG.RankThree.PartOne.IsStronglyPEmbedded k.p
      (((H ⊓ k.M).subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))) := by
  have hp : k.p.Prime := k.prime
  haveI : Fact k.p.Prime := ⟨hp⟩
  have hM : IsStronglyPEmbedded k.p k.M := k.strong
  have hdvd : k.p ∣ Nat.card (H ⊓ k.M : Subgroup G) := by
    have hpow : k.p ^ 2 ∣ Nat.card (H ⊓ k.M : Subgroup G) :=
      (pow_dvd_pow k.p hH.two_le_pRank).trans
        (CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card k.p hp
          (H ⊓ k.M))
    exact (dvd_pow_self k.p (by norm_num : (2 : ℕ) ≠ 0)).trans hpow
  have hY : IsStronglyPEmbedded k.p ((H ⊓ k.M).subgroupOf H) :=
    hM.subgroupOf hH.not_le hdvd
  have hKle : CFSG.pPrimeCore k.p ↥H ≤ (H ⊓ k.M).subgroupOf H := by
    intro x hx
    refine Subgroup.mem_subgroupOf.mpr ⟨x.2, ?_⟩
    exact k.pPrimeCore_le_of_not_le hH.not_le hH.two_le_pRank
      (Subgroup.mem_map_of_mem H.subtype hx)
  have hKcop : ¬ k.p ∣ Nat.card (CFSG.pPrimeCore k.p ↥H) :=
    (hp.coprime_iff_not_dvd).mp (CFSG.pPrimeCore_coprime_card (G := ↥H) (p := k.p))
  exact hY.map_quotient hKle hKcop

end Sec7Core4


end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
