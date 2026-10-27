module

public import CFSG.RankThree.PartTwo.Sec18.Item187Pigeon
public import CFSG.RankThree.PartTwo.Sec18.Item187Triple
import CFSG.RankThree.PartTwo.Sec18.Item187Core
public import CFSG.RankThree.PartTwo.Sec18.Item187NMain
import CFSG.HardMathSupport.Solomon.Coordinator.Th1J1.Zero
import CFSG.RankThree.PartTwo.Sec18.Item187F14Bad

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late
open CFSG.HardMathSupport.Solomon.UniquenessMaximal (tripleOf)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G} {X : Subgroup G}

theorem th1J1_zero_one_of_not_three (R S : Subgroup G) (hRs : Group.IsSolvable ↥R)
    (h3 : ¬ 3 ∣ Nat.card R)
    (hO : ∀ N : Subgroup G, N ≤ R → R ≤ Subgroup.normalizer (N : Set G) → ¬ 2 ∣ Nat.card N → N = ⊥)
    (hSR : S ≤ R) (hS2 : IsPGroup 2 S) (hSidx : ¬ 2 ∣ S.relIndex R) :
    ((Subgroup.normalizer (tripleOf S 0 : Set G) ⊓ R : Subgroup G) : Set G) *
      ((Subgroup.normalizer (tripleOf S 1 : Set G) ⊓ R : Subgroup G) : Set G) = (R : Set G) :=
  CFSG.HardMathSupport.Solomon.Coordinator.I28_8.Th1J1.fac_zero_one0
    ⟨hRs, h3, hO, hSR, hS2, hSidx⟩

section Certified

theorem MinCex.le_normalizer_one_or_two (h1812 : Item181_2) (h184 : Item184_1)
    (h186 : Item186H) (hX : MinCex A M H c X) (hsol : Group.IsSolvable ↥X)
    (h5 : 5 ∣ Nat.card X) (hm : 2 ≤ CFSG.pRank 2 ↥(CFSG.Open.pCoreOf 2 (H ⊓ M))) :
    X ≤ Subgroup.normalizer (tripleOf (CFSG.Open.pCoreOf 2 (H ⊓ M)) 1 : Set G) ∨
      X ≤ Subgroup.normalizer (tripleOf (CFSG.Open.pCoreOf 2 (H ⊓ M)) 2 : Set G) := by
  by_contra hcon
  rw [not_or] at hcon
  exact MinCex.false_of_bad h1812 h184 h186 hX hsol h5
    (by unfold BadCase; exact ⟨hm, hcon.1, hcon.2⟩)

theorem MinCex.false_of_isSolvable_of_five_dvd (h1812 : Item181_2) (h1813 : Item181_3)
    (h184 : Item184_1) (h186 : Item186H) (hX : MinCex A M H c X)
    (hsol : Group.IsSolvable ↥X) (h5 : 5 ∣ Nat.card X) : False := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := CFSG.Open.pCoreOf 2 (H ⊓ M)
  have hXM : X ≤ M := MinCex.le_M hX
  have hSyl : CFSG.ABGLocalTools.IsSylowOf 2 S X :=
    isSylowOf_of_mem_scriptX h186 hX.sec18H hX.hyp187 hX.mem
  have hSX : S ≤ X := hX.pCoreOf_le
  have hS2 : IsPGroup 2 S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M)
  have hrel : ¬ 2 ∣ S.relIndex X := not_dvd_relIndex_of_isSylowOf hSyl
  have hO := eq_bot_of_inf_centralizer_le
    (inf_centralizer_le_of_mem_scriptX h186 hX.sec18H hX.hyp187 hX.mem hXM)
  have h3 : ¬ 3 ∣ Nat.card X := MinCex.not_three_dvd hX
  have hF02 := CFSG.HardMathSupport.Solomon.Coordinator.I28_8.pair_zero_two
    hsol h3 hO hSX hS2 hrel
  have hF01 := th1J1_zero_one_of_not_three X S hsol h3 hO hSX hS2 hrel
  have hSA : ∀ k : Fin 4, A ⊔ S ≤ Subgroup.normalizer (fourChar S k : Set G) := fun k =>
    (le_normalizer_pCoreOf hX.sec18H).trans (normalizer_le_normalizer_fourChar S k)
  have hT0 : A ⊔ S ≤ Subgroup.normalizer (tripleOf S 0 : Set G) := by
    rw [tripleOf_zero_eq S]
    exact hSA 1
  have hT2 : A ⊔ S ≤ Subgroup.normalizer (tripleOf S 2 : Set G) := by
    rw [tripleOf_two_eq S]
    exact hSA 0
  have hP02 := MinCex.le_normalizer_or_le_normalizer hX hT0 hT2 hF02
  by_cases hm : 2 ≤ CFSG.pRank 2 S
  · have hT1 : A ⊔ S ≤ Subgroup.normalizer (tripleOf S 1 : Set G) := by
      rw [tripleOf_one_eq hm]
      exact hSA 2
    have hP01 := MinCex.le_normalizer_or_le_normalizer hX hT0 hT1 hF01
    have hP12 := MinCex.le_normalizer_one_or_two h1812 h184 h186 hX hsol h5 hm
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
  · have hm1 : CFSG.pRank 2 S ≤ 1 := by omega
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

end Certified

section Wiring

theorem item187_holds_of (h1812 : Item181_2) (h1813 : Item181_3) (h184 : Item184_1)
    (h1842 : Item184_2) (h186 : Item186H) : Item187 :=
  item187_of_five_case h1812 h1813 h184 h1842 h186
    (fun G _ _ A M H c X hX hs h5 =>
      MinCex.false_of_isSolvable_of_five_dvd h1812 h1813 h184 h186 hX hs h5)

end Wiring

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
