module

public import CFSG.RankThree.PartTwo.Sec16.Item1621StepsProofEnd
public import CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProofRank
public import CFSG.RankThree.PartTwo.Sec16.SuzukiSectionProofComp
import CFSG.CGT.PushingUpLit.ThmOne.ThreeOneFStar

public section

namespace CFSG.RankThree.PartTwo.Sec16

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open Subgroup


theorem ks1623SzCent_holds : KS1623SzCent := by
  intro G _ _ X A W c hXK hX3 hX2 hA hAX hWX hW hW16 hAW hcA hWc hrank hodd
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hE : ∀ J : Subgroup X, CFSG.IsComponent J → ⁅J, W.subgroupOf X⁆ = ⊥ := fun J hJ =>
    absurd hodd (SuzukiSectionProof.not_odd_card_inf_centralizer_of_isComponent hXK hX3 hA.2
      hAX hJ)
  have h2 : CFSG.pCore 2 X = ⊥ := by
    exact (Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective).mp hX2
  set W' := W.subgroupOf X with hW'
  have hW'map : W'.map X.subtype = W := by
    rw [hW', Subgroup.subgroupOf_map_subtype, inf_eq_left.mpr hWX]
  have hW2 : IsPGroup 2 W := IsPGroup.of_card (n := 4) (by rw [hW16]; norm_num)
  have hW'2 : IsPGroup 2 W' := hW2.comap_subtype
  have hcomm_iff : ∀ Y Z : Subgroup X,
      ⁅Y, Z⁆ = ⊥ ↔ ⁅Y.map X.subtype, Z.map X.subtype⁆ = ⊥ := by
    intro Y Z
    rw [← Subgroup.map_commutator, Subgroup.map_eq_bot_iff_of_injective _ X.subtype_injective]
  have hF : ⁅CFSG.fittingSubgroup X, W'⁆ = ⊥ := by
    rw [CFSG.LocalCores.fittingSubgroup_eq_iSup_pCore,
      Subgroup.commutator_eq_bot_iff_le_centralizer]
    refine iSup_le fun p => ?_
    rw [← Subgroup.commutator_eq_bot_iff_le_centralizer, hcomm_iff, hW'map]
    have hp : (p : ℕ).Prime := Nat.prime_of_mem_primeFactors p.2
    have : Fact (p : ℕ).Prime := ⟨hp⟩
    by_cases hp2 : (p : ℕ) = 2
    · have h0 : (CFSG.Open.pCore (p : ℕ) X).map X.subtype = ⊥ := by
        rw [hp2]
        exact hX2
      rw [h0, Subgroup.commutator_bot_left]
    by_cases hp3 : (p : ℕ) = 3
    · have h0 : (CFSG.Open.pCore (p : ℕ) X).map X.subtype = ⊥ := by
        have hR : IsPGroup (p : ℕ) (CFSG.Open.pCoreOf (p : ℕ) X) :=
          CFSG.LieType.BorelTits.pCoreOf_isPGroup (p : ℕ) X
        obtain ⟨n, hn⟩ := hR.exists_card_eq
        have hdvd : Nat.card (CFSG.Open.pCoreOf (p : ℕ) X) ∣ Nat.card X :=
          Subgroup.card_dvd_of_le (CFSG.LieType.BorelTits.pCoreOf_le (p : ℕ) X)
        have hn0 : n = 0 := by
          by_contra hne
          apply hX3
          rw [← hp3]
          exact (dvd_pow_self (p : ℕ) hne).trans (hn ▸ hdvd)
        rw [hn0, pow_zero] at hn
        exact Subgroup.card_eq_one.mp hn
      rw [h0, Subgroup.commutator_bot_left]
    exact SuzukiSectionProof.commutator_eq_bot_of_isPGroup hp hp2
      (CFSG.LieType.BorelTits.pCoreOf_isPGroup (p : ℕ) X)
      (CFSG.LieType.BorelTits.pCoreOf_le (p : ℕ) X)
      (hWX.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf (p : ℕ) X))
      (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf (p : ℕ) X (hAX hcA)) hW hW16
      (hAW hcA) (hA.2 c hcA) hWc
      (fun t ht ht1 => hrank t ht ht1 p hp (by have := hp.two_le; omega))
  have hW'bot : W' = ⊥ := CFSG.CGT.PushingUpLit.ThmOne.eq_bot_of_commutator_eq_bot h2 hW'2 hE hF
  rw [← hW'map, hW'bot, Subgroup.map_bot, Subgroup.card_bot] at hW16
  norm_num at hW16

theorem step1623End_of_endS (hS : Step1623EndS) : Step1623End :=
  step1623End_of_S hS ks1623SzCent_holds

end CFSG.RankThree.PartTwo.Sec16
