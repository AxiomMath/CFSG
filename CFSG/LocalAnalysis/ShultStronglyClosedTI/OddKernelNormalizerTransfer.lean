module

public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddKernelNormalizerTransferLift
public import CFSG.LocalAnalysis.ProperTwoGeneratedCore.LocalCriterionProperHullDatum
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.OddCorePrimeComplementGrowthSylow

public noncomputable section

namespace CFSG.ShultStronglyClosedTI.OddKernelNormalizerTransfer

open CFSG.Open CFSG.BenderSuzuki
open CFSG.BenderSuzuki.PFAppendixIII
open CFSG.BenderSuzuki.PFchapter1section1
open CFSG.RankThreeEvenClassification.Helpers
open CFSG.ProperTwoGeneratedCore.LocalCriterionGeometry
open CFSG.ProperTwoGeneratedCore.LocalCriterionProperHull

universe u

variable {G : Type u} [Group G] [Finite G]

theorem odd_kernel_normalizer_rank_and_noncentral_action_transfer
    (p : ℕ) (hp : p.Prime) (_hpodd : Odd p)
    (hrank : 2 ≤ twoRank G) (z : G) (hz : IsInvolution z)
    (hclass : ∀ x : G, IsInvolution x → x ∈ involutionPointClass z)
    (W : Subgroup G) [W.Normal] (hWodd : Odd (Nat.card W))
    (hWcop : Nat.Coprime p (Nat.card W)) (Q : Sylow p G)
    (R : Subgroup G) (hRQ : R ≤ (Q : Subgroup G))
    (hRchar : (R.subgroupOf (Q : Subgroup G)).Characteristic)
    (hsup : W ⊔ Subgroup.normalizer (R : Set G) = ⊤)
    (A : Subgroup G) (hAQ : A ≤ (Q : Subgroup G))
    (hAz : rightConjugate A z = A)
    (hnoncentral : ¬ A ≤ Subgroup.centralizer ({z} : Set G)) :
    let N := Subgroup.normalizer (R : Set G)
    ∃ w : G, w ∈ W ∧
      let s := rightConjugateElem z w
      s ∈ N ∧ s ∈ Subgroup.normalizer (A : Set G) ∧
      ¬ A ≤ Subgroup.centralizer ({s} : Set G) ∧ IsInvolution s ∧
      2 ≤ CFSG.Open.pRank 2 (Subgroup.closure (conjugacyWithin N s)) ∧
      (∀ u v : N, IsInvolution u → IsInvolution v →
        ∃ n : N, rightConjugateElem u n = v) ∧
      ∃ P : Sylow 2 G, (P : Subgroup G) ≤ N := by
  let : Fact p.Prime := ⟨hp⟩
  let : (R.subgroupOf (Q : Subgroup G)).Characteristic := hRchar
  let N := Subgroup.normalizer (R : Set G)
  have hQN : (Q : Subgroup G) ≤ N := by
    have hQmap := primeComplementGrowth_normalizer_le_characteristic_image_normalizer
      (Q : Subgroup G) (R.subgroupOf (Q : Subgroup G))
    rw [Subgroup.map_subgroupOf_eq_of_le hRQ] at hQmap
    exact Subgroup.le_normalizer.trans hQmap
  have hAN : A ≤ N := hAQ.trans hQN
  have hAp : IsPGroup p A := Q.isPGroup'.to_le hAQ
  have hzA : z ∈ Subgroup.normalizer (A : Set G) :=
    primeComplementGrowth_mem_normalizer_of_conjugate_eq A z hAz
  obtain ⟨w, hw, hsN, hsA, hsnoncentral, hs⟩ :=
    odd_prime_normal_supplement_simultaneous_normalizer_lift p hp W N
      hWodd hWcop hsup A hAN hAp z hz hzA hnoncentral
  let s := rightConjugateElem z w
  let sN : N := ⟨s, hsN⟩
  have hNclass := odd_normal_supplement_single_involution_class W N hWodd hsup z hclass
  have hclasss : ∀ x : N, IsInvolution x → x ∈ involutionPointClass sN := by
    intro x hx
    have hsNinv : IsInvolution sN :=
      ⟨fun heq => hs.1 (congrArg Subtype.val heq), Subtype.ext hs.2⟩
    exact hNclass sN x hsNinv hx
  have hNrank : 2 ≤ twoRank N := by
    rw [← odd_normal_supplement_two_rank W N hWodd hsup]
    exact hrank
  have hhullrank : 2 ≤ CFSG.Open.pRank 2
      (Subgroup.closure (conjugacyWithin N s)) := by
    have hmaprank := pRank_eq_of_subgroup_equiv 2 Nat.prime_two
      (involutionPointHull sN) ((involutionPointHull sN).map N.subtype)
      ((involutionPointHull sN).equivMapOfInjective N.subtype N.subtype_injective)
    rw [internal_hull_map N hsN] at hmaprank
    have hinternal : 2 ≤ CFSG.Open.pRank 2 (involutionPointHull sN) := by
      rw [← CFSG.ComponentClassification.TwoRankTransport.subgroup,
        single_involution_class_hull_two_rank sN hclasss]
      exact hNrank
    exact hinternal.trans (le_of_eq hmaprank)
  let PN : Sylow 2 N := Classical.choice inferInstance
  obtain ⟨P, hP⟩ := odd_normal_supplement_full_two_sylow W N hWodd hsup PN
  have hPle : (P : Subgroup G) ≤ N := by
    rw [hP]
    exact Subgroup.map_subtype_le _
  exact ⟨w, hw, hsN, hsA, hsnoncentral, hs, hhullrank, hNclass, P, hPle⟩

end CFSG.ShultStronglyClosedTI.OddKernelNormalizerTransfer
