module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Good
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputsSolvable
import CFSG.GroupTheory.PCore.PrimeSetCore
import CFSG.GroupTheory.PRankMapOfKerPrimeNotDvd
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight70Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open CFSG.RankThree.PartOne (IsStronglyPEmbedded)

variable {G : Type} [Group G] [Finite G]

namespace Sec7Core4

theorem pRank_le_two_of_perfect_in_config (k : Sec7Core4 G) (h5 : 5 ≤ k.p)
    (hno : KIDExcluded k) (h75 : Step75 k) (hS : StronglyEmbeddedSolvable)
    {H X : Subgroup G} (hH : Config k H) (hXHM : X ≤ H ⊓ k.M)
    (hXperf : ⁅X, X⁆ = X) : CFSG.Open.pRank k.p X ≤ 2 := by
  by_contra hle
  have hX3 : 3 ≤ CFSG.Open.pRank k.p X := by omega
  have hp : k.p.Prime := k.prime
  let O : Subgroup ↥H := CFSG.pPrimeCore k.p ↥H
  let π : ↥H →* (↥H ⧸ O) := QuotientGroup.mk' O
  let Y : Subgroup ↥H := (H ⊓ k.M).subgroupOf H
  let Nbar : Subgroup (↥H ⧸ O) := Y.map π
  have hker : ¬ k.p ∣ Nat.card ↥(MonoidHom.ker π) := by
    rw [QuotientGroup.ker_mk']
    exact (hp.coprime_iff_not_dvd).mp
      (@CFSG.pPrimeCore_coprime_card k.p ↥H _ _ ⟨hp⟩)
  have hNbarY : CFSG.Open.pRank k.p Nbar = CFSG.Open.pRank k.p Y :=
    CFSG.pRank_map_eq_of_not_dvd_card_ker π (QuotientGroup.mk'_surjective O) hp hker Y
  have hYHM : CFSG.Open.pRank k.p Y = CFSG.Open.pRank k.p (H ⊓ k.M) := by
    rw [CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := k.p) Y]
    rw [CFSG.SectionRank.pRank_top_eq_of_mulEquiv hp.one_lt
      (Subgroup.subgroupOfEquivOfLe (inf_le_left : H ⊓ k.M ≤ H))]
    rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (p := k.p) (H ⊓ k.M)]
  have hmono : CFSG.Open.pRank k.p X ≤ CFSG.Open.pRank k.p (H ⊓ k.M) :=
    CFSG.SectionRank.pRank_mono hp.one_lt hXHM
  have hNbar3 : 3 ≤ CFSG.Open.pRank k.p Nbar := by
    rw [hNbarY, hYHM]
    omega
  have hKH : CFSG.Open.IsKGroup ↥H :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper k.standing.kProper hH.ne_top
  have hKQ : CFSG.Open.IsKGroup (↥H ⧸ O) :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient' hKH O
  have hO : CFSG.pPrimeCore k.p (↥H ⧸ O) = ⊥ := CFSG.pPrimeCore_quotient_eq_bot hp
  have hrankQ : 2 ≤ CFSG.Open.pRank k.p (⊤ : Subgroup (↥H ⧸ O)) :=
    k.two_le_pRank_quotient_pPrimeCore hH
  have hN : IsStronglyPEmbedded k.p Nbar :=
    k.isStronglyPEmbedded_map_quotient_pPrimeCore hH
  rcases hS k.p hp h5 (↥H ⧸ O) hKQ hO hrankQ Nbar hN (hno H hH h75) with
    hsol | ⟨hp5, hfac, _⟩
  · exact CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.eight70_not_isSolvable hp
      hXHM hXperf (by omega) hsol
  · have hNbar3' : 3 ≤ CFSG.Open.pRank 5 Nbar := by
      simpa [hp5] using hNbar3
    have hdvd : 5 ^ 3 ∣ Nat.card Nbar :=
      (Nat.pow_dvd_pow 5 hNbar3').trans
        (CFSG.RankThreeEvenClassification.Helpers.prime_power_pRank_dvd_card 5
          Nat.prime_five Nbar)
    have hfac3 : 3 ≤ (Nat.card Nbar).factorization 5 :=
      (Nat.prime_five.pow_dvd_iff_le_factorization Nat.card_pos.ne').mp hdvd
    omega

theorem le_of_perfect_subgroup_of_three_le_pRank (k : Sec7Core4 G) (h5 : 5 ≤ k.p)
    (hno : KIDExcluded k) (h75 : Step75 k) (hS : StronglyEmbeddedSolvable)
    {H X : Subgroup G} (hH : H ≠ ⊤) (hXHM : X ≤ H ⊓ k.M)
    (hXperf : ⁅X, X⁆ = X) (hXrank : 3 ≤ CFSG.Open.pRank k.p X) : H ≤ k.M := by
  by_contra hHM
  have hmono : CFSG.Open.pRank k.p X ≤ CFSG.Open.pRank k.p (H ⊓ k.M) :=
    CFSG.SectionRank.pRank_mono k.prime.one_lt hXHM
  have hHcfg : Config k H := ⟨hH, hHM, by omega⟩
  have hbound := k.pRank_le_two_of_perfect_in_config h5 hno h75 hS hHcfg hXHM hXperf
  omega

end Sec7Core4

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
