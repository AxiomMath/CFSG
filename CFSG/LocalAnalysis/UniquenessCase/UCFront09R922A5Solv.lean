module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
import CFSG.LocalAnalysis.QuasithinUnique.CharTwoTransport
import CFSG.Adapters.GeneralizedFitting
import CFSG.RankThree.GroupTheory.SteinbergBMCrossPrimeLocalCore
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.QuasithinUnique.CharTwoInheritance
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
import CFSG.RankThree.PartOne.K1214.Basic

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F09

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf isSylowOf_iff)

variable {G : Type} [Group G] [Finite G]

theorem charTwo_sup_I9 {H R : Subgroup G} (hF : Fstar H = pCoreOf 2 H) (hRH : R ≤ H)
    (hR2 : IsPGroup 2 R) : CFSG.QuasithinUnique.CharTwo (R ⊔ I9 H) := by
  have hHI : H ≤ normalizer (I9 H : Set G) :=
    CFSG.RankThree.GroupTheory.SteinbergBM.le_normalizer_inSubgroup_pPrimeCore 3 H
  have hIH : I9 H ≤ H := map_subtype_le _
  have hHc : CFSG.QuasithinUnique.CharTwo H := by
    rintro y ⟨hyH, hyc⟩
    have hc : (⟨y, hyH⟩ : ↥H) ∈ centralizer (CFSG.Open.genFittingFStar ↥H : Set ↥H) := by
      rw [mem_centralizer_iff]
      intro w hw
      have hw' : (w : G) ∈ pCoreOf 2 H := by
        rw [← hF]
        exact mem_map_of_mem _ hw
      exact Subtype.ext ((mem_centralizer_iff.1 hyc) _ hw')
    rw [← hF]
    exact mem_map_of_mem H.subtype (CFSG.Adapters.generalized_fitting_self_centralizing ↥H hc)
  rw [sup_comm]
  exact (hHc.of_normal hIH ((normal_subgroupOf_iff_le_normalizer hIH).2 hHI)).sup_of_le_normalizer
    hR2 (hRH.trans hHI)

theorem not_three_dvd_card_sup_I9 {H R : Subgroup G} (hRH : R ≤ H) (hR2 : IsPGroup 2 R) :
    ¬ 3 ∣ Nat.card ↥(R ⊔ I9 H) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hcard := CFSG.RankThree.PartOne.K1214.card_sup_mul_card_inf_of_le_normalizer
    (hRH.trans (CFSG.RankThree.GroupTheory.SteinbergBM.le_normalizer_inSubgroup_pPrimeCore 3 H))
  intro h3
  rw [sup_comm] at h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 (hcard ▸ h3.mul_right _) with h | h
  · exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).1
      (CFSG.RankThree.GroupTheory.SteinbergBM.coprime_card_inSubgroup_pPrimeCore H) h
  · obtain ⟨k, hk⟩ := hR2.exists_card_eq
    rw [hk] at h
    exact absurd ((Nat.prime_dvd_prime_iff_eq Nat.prime_three Nat.prime_two).1
      (Nat.prime_three.dvd_of_dvd_pow h)) (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.UC22.F09
