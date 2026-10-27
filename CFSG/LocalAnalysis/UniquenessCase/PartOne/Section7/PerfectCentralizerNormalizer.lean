module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Theorem76
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight70Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight70Layer
public import CFSG.LocalAnalysis.AGL81TheoremCD.Section8.AltTen
public import CFSG.RankThree.PartTwo.Sec12.Hering129HBasic
import CFSG.LocalAnalysis.UniquenessCase.UC6S9

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Sec7Core4

open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

variable {G : Type} [Group G] [Finite G]

theorem normalizer_zpowers_le_of_perfect_centralizer
    (hSE : StronglyEmbeddedFive)
    (hSAlt : StronglyEmbeddedSolvableAltTen)
    (hKSM : CFSG.LocalAnalysis.RankThreeUC.S15.KSMAlt)
    (k : Sec7Core4 G) (he : CFSG.Open.evenRank G ≤ 3) (h5 : 5 ≤ k.p)
    {b : G} (hb3 : orderOf b = 3) {X : Subgroup G}
    (hXM : X ≤ k.M)
    (hXC : X ≤ Subgroup.centralizer ({b} : Set G))
    (hXperf : ⁅X, X⁆ = X)
    (hXrank : 2 ≤ CFSG.Open.pRank k.p X) :
    Subgroup.normalizer (Subgroup.zpowers b : Set G) ≤ k.M := by
  classical
  let H : Subgroup G := Subgroup.normalizer (Subgroup.zpowers b : Set G)
  have hXH : X ≤ H :=
    hXC.trans (CFSG.GorensteinWalter.centralizer_singleton_le_normalizer_zpowers b)
  have hHne : H ≠ ⊤ := by
    change Subgroup.normalizer (Subgroup.zpowers b : Set G) ≠ ⊤
    exact CFSG.LocalAnalysis.UniquenessCase.UC6.normalizer_ne_top_of_card_prime_uc6
      k.standing.simple k.standing.nonab Nat.prime_three (by rw [Nat.card_zpowers, hb3])
  by_contra hHnotM
  have hXHM : X ≤ H ⊓ k.M := le_inf hXH hXM
  have hrankHM : 2 ≤ CFSG.Open.pRank k.p (H ⊓ k.M) :=
    hXrank.trans (CFSG.SectionRank.pRank_mono k.prime.one_lt hXHM)
  have hHconf : k.Config H := ⟨hHne, hHnotM, hrankHM⟩
  have h75 : k.Step75 := k.step75 h5 hSE
  have hno : k.KIDExcluded := k.kIDExcluded_of_evenRank_le_three he
  have hnotSolv : ¬ IsSolvable ↥(((H ⊓ k.M).subgroupOf H).map
      (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))) :=
    eight70_not_isSolvable k.prime hXHM hXperf (by omega)
  have hcase := eight70_solvable_or_altTen k h5 hno hHconf h75 hSAlt
  rcases hcase with hsol | ⟨-, hF, -⟩
  · exact hnotSolv hsol
  obtain ⟨⟨eJ⟩, -⟩ := eight70_layer_equiv k hHconf h75 hF
  let J : Subgroup G := layerLift k.p H
  have hJH : J ≤ H := layerLift_le k.p H
  have hJperf : Group.IsPerfect ↥J :=
    Subgroup.isPerfect_iff.mpr (commutator_layerLift k.p H)
  have hJcent : J ≤ Subgroup.centralizer ({b} : Set G) :=
    CFSG.RankThree.PartTwo.Sec12.le_centralizer_of_isPerfect_of_le_normalizer_zpowers
      hJperf hJH
  have hcomm : ∀ j ∈ J, b * j = j * b := by
    intro j hj
    exact Subgroup.mem_centralizer_iff.mp (hJcent hj) b (Set.mem_singleton b)
  have hker : eJ.toMonoidHom.ker ≤ Subgroup.center ↥J := by
    rw [(MonoidHom.ker_eq_bot_iff eJ.toMonoidHom).mpr eJ.injective]
    exact bot_le
  have hodd : Odd (Nat.card eJ.toMonoidHom.ker) := by
    rw [(MonoidHom.ker_eq_bot_iff eJ.toMonoidHom).mpr eJ.injective, Subgroup.card_bot]
    exact ⟨0, by norm_num⟩
  have h4 : 4 ≤ CFSG.Open.rankThreeLocalRank 3 G :=
    CFSG.LocalAnalysis.AGL81TheoremCD.Section8.four_le_localRank_of_altTen
      hKSM hJperf eJ.toMonoidHom eJ.surjective hker hodd hb3 hcomm
  have hle : CFSG.Open.rankThreeLocalRank 3 G ≤ CFSG.Open.evenRank G :=
    CFSG.RankThreeCoreUniqueness.Helpers.rankThreeLocalRank_le_evenRank 3
      Nat.prime_three (by norm_num) (G := G)
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Sec7Core4
