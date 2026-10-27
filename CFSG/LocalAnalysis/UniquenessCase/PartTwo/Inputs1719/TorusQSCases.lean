module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TorusQSL2Sq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S19
open scoped Pointwise commutatorElement

@[expose] def K_19_19_torusQS_sp4 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (I A J : Subgroup X) (n p : ℕ), 3 ≤ n → p.Prime → p ≠ 2 →
    (IsSp4 (Bar2 I) n ∧ Odd n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] ∧ IsQuasisimple (Bar2 J)) →
    A ≤ I → IsZModSq A n → J ≤ I → A ≤ normalizer J → S17.oUpperTwo J = J →
    pRank p J ≤ 1 →
    ((IsPGroup 3 (Bar2 J) ∧ Nat.card (Bar2 J) ∣ 9) ∨ IsQuasisimple (Bar2 J)) →
    3 ∣ Nat.card (Bar2 J) →
    (J : Set X) ⊆ (pCoreOf 2 J : Set X) * (A : Set X) ∨
      (IsL2 (Bar2 J) n ∧ ∃ K ≤ I, (K.subgroupOf I).Normal ∧ ⁅K, K⁆ = K ∧
        IsQuasisimple (Bar2 K) ∧ J ≤ K ∧
        (J ⊔ pCoreOf 2 K = K ∨ IsSp4 (Bar2 K) n ∨ IsU3 (Bar2 K) n))

@[expose] def K_19_19_torusQS_l2u3 : Prop :=
  ∀ (X : Type) [Group X] [Finite X] (I A J : Subgroup X) (n p : ℕ), 3 ≤ n → p.Prime → p ≠ 2 →
    (S17.IsL2U3Product (Bar2 I) n ∧ IsPowTwo n ∧ (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) →
    A ≤ I → IsZModSq A n → J ≤ I → A ≤ normalizer J → S17.oUpperTwo J = J →
    pRank p J ≤ 1 →
    ((IsPGroup 3 (Bar2 J) ∧ Nat.card (Bar2 J) ∣ 9) ∨ IsQuasisimple (Bar2 J)) →
    3 ∣ Nat.card (Bar2 J) →
    (J : Set X) ⊆ (pCoreOf 2 J : Set X) * (A : Set X) ∨
      (IsL2 (Bar2 J) n ∧ ∃ K ≤ I, (K.subgroupOf I).Normal ∧ ⁅K, K⁆ = K ∧
        IsQuasisimple (Bar2 K) ∧ J ≤ K ∧
        (J ⊔ pCoreOf 2 K = K ∨ IsSp4 (Bar2 K) n ∨ IsU3 (Bar2 K) n))

theorem k_19_19_torusQS_of_cases (hS : K_19_19_torusQS_sp4)
    (hU : K_19_19_torusQS_l2u3) : K_19_19_torusQS := by
  intro X _ _ I A J n p hn hp hp2 hshape hAI hA hJI hAJ hO hpr hcase h3
  rcases hshape with hsp | hsq | hu
  · exact hS X I A J n p hn hp hp2 hsp hAI hA hJI hAJ hO hpr hcase h3
  · exact TorusQS.torusQS_l2sq I A J n hn hsq hAI hA hJI hAJ hO hcase h3
  · exact hU X I A J n p hn hp hp2 hu hAI hA hJI hAJ hO hpr hcase h3

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
