module

public import CFSG.RankThree.PartTwo.Sec18.Item187Min
import CFSG.RankThree.PartTwo.Sec18.Item187Gen
import CFSG.RankThree.PartTwo.Sec18.Item187Syl
import CFSG.RankThree.PartTwo.Sec18.Item187Core
import CFSG.RankThree.PartTwo.Sec18.Item187Pigeon
import CFSG.RankThree.PartTwo.Sec18.Item187Triple
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.Main

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open CFSG.HardMathSupport.Solomon.UniquenessMaximal

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G}

theorem MinCex.false_of_isSolvable_of_not_five_dvd (h1813 : Item181_3) (h184 : Item184_1)
    (h186 : Item186H) {X : Subgroup G} (hX : MinCex A M H c X) (hsol : Group.IsSolvable ↥X)
    (h5 : ¬ 5 ∣ Nat.card X) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := CFSG.Open.pCoreOf 2 (H ⊓ M)
  have hXM : X ≤ M :=
    le_of_le_normalizer_of_isPiSubgroup hX.sec18H.toSec18Std hX.isPiSubgroup
      (le_sup_left.trans hX.le_normalizer)
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S X :=
    isSylowOf_of_mem_scriptX h186 hX.sec18H hX.hyp187 hX.mem
  have hSX : S ≤ X := hX.pCoreOf_le
  have hS2 : IsPGroup 2 S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M)
  have hrel : ¬ 2 ∣ S.relIndex X := not_dvd_relIndex_of_isSylowOf hSyl
  have hO := eq_bot_of_inf_centralizer_le
    (inf_centralizer_le_of_mem_scriptX h186 hX.sec18H hX.hyp187 hX.mem hXM)
  have h3 : ¬ 3 ∣ Nat.card X := fun h3 => by
    have hmem : (⟨3, Nat.prime_three⟩ : Nat.Primes) ∈ piCompl 3 :=
      hX.isPiSubgroup ⟨3, Nat.prime_three⟩ h3
    exact hmem rfl
  have hTF : CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1Factorization :=
    CFSG.HardMathSupport.Solomon.Coordinator.I28_8.th1_of_th1J1
      CFSG.HardMathSupport.Solomon.Coordinator.I28_8.th1J1Factorization
  have hF := hTF G X S hsol h3 h5 hO hSX hS2 hrel
  have hSA : ∀ k : Fin 4, A ⊔ S ≤ Subgroup.normalizer (fourChar S k : Set G) := fun k =>
    (le_normalizer_pCoreOf hX.sec18H).trans (normalizer_le_normalizer_fourChar S k)
  have hT0 : A ⊔ S ≤ Subgroup.normalizer (tripleOf S 0 : Set G) := by
    rw [tripleOf_zero_eq S]
    exact hSA 1
  have hT2 : A ⊔ S ≤ Subgroup.normalizer (tripleOf S 2 : Set G) := by
    rw [tripleOf_two_eq S]
    exact hSA 0
  have hP02 := MinCex.le_normalizer_or_le_normalizer hX hT0 hT2 (hF 0 2 (by decide))
  by_cases hm : 2 ≤ CFSG.pRank 2 S
  ·
    have hT1 : A ⊔ S ≤ Subgroup.normalizer (tripleOf S 1 : Set G) := by
      rw [tripleOf_one_eq hm]
      exact hSA 2
    have hP01 := MinCex.le_normalizer_or_le_normalizer hX hT0 hT1 (hF 0 1 (by decide))
    have hP12 := MinCex.le_normalizer_or_le_normalizer hX hT1 hT2 (hF 1 2 (by decide))
    rw [tripleOf_zero_eq S, tripleOf_one_eq hm] at hP01
    rw [tripleOf_zero_eq S, tripleOf_two_eq S] at hP02
    rw [tripleOf_one_eq hm, tripleOf_two_eq S] at hP12
    have hmaj : ∀ P0 P1 P2 : Prop, (P1 ∨ P2) → (P1 ∨ P0) → (P2 ∨ P0) →
        (P0 ∧ P1) ∨ (P1 ∧ P2) ∨ (P0 ∧ P2) := by
      intro P0 P1 P2 h1 h2 h3
      tauto
    rcases hmaj _ _ _ hP01 hP02 hP12 with ⟨h0, h1⟩ | ⟨h1, h2⟩ | ⟨h0, h2⟩
    · exact hX.not_le (le_of_le_normalizer_fourChar h1813 h184 h186 hX.sec18H hX.hyp187
        (i := 0) (j := 1) (by decide) (by decide) (by decide) h0 h1)
    · exact hX.not_le (le_of_le_normalizer_fourChar h1813 h184 h186 hX.sec18H hX.hyp187
        (i := 1) (j := 2) (by decide) (by decide) (by decide) h1 h2)
    · exact hX.not_le (le_of_le_normalizer_fourChar h1813 h184 h186 hX.sec18H hX.hyp187
        (i := 0) (j := 2) (by decide) (by decide) (by decide) h0 h2)
  ·
    have hm1 : CFSG.pRank 2 S ≤ 1 := by omega
    have hS1 : S ≠ ⊥ := by
      intro hbot
      apply hX.hyp187.2.1
      have hAH : A ≤ H :=
        le_trans (le_trans le_sup_right le_sup_left) hX.sec18H.mem_scriptH.2.1.ge
      have hOH : CFSG.Open.pCoreOf 2 H ≤ S :=
        CFSG.RankThree.PartTwo.Sec18.pCoreOf_le_pCoreOf_inf hX.sec18H.toSec18Std hAH
      exact le_bot_iff.mp (hOH.trans hbot.le)
    have he : fourChar S 0 = fourChar S 1 := fourChar_zero_eq_one hS2 hS1 hm1
    rw [tripleOf_zero_eq S, tripleOf_two_eq S] at hP02
    have h0 : X ≤ Subgroup.normalizer (fourChar S 0 : Set G) := by
      rcases hP02 with h | h
      · rw [he]
        exact h
      · exact h
    have h1 : X ≤ Subgroup.normalizer (fourChar S 1 : Set G) := by
      rw [← he]
      exact h0
    exact hX.not_le (le_of_le_normalizer_fourChar h1813 h184 h186 hX.sec18H hX.hyp187
      (i := 0) (j := 1) (by decide) (by decide) (by decide) h0 h1)

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
