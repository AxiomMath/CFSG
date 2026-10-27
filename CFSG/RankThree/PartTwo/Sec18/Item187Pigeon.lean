module

public import CFSG.RankThree.PartTwo.Sec18.Item187Min
import CFSG.RankThree.PartTwo.Sec18.Tools
import CFSG.RankThree.PartTwo.Sec18.Item181ThreeProofThompson
import CFSG.RankThree.PartTwo.Sec20.Item20Res5ProofNormal

public section

namespace CFSG.RankThree.PartTwo.Sec18.Item187Proof

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Late

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G}

theorem le_of_le_normalizer_fourChar (h1813 : Item181_3) (h184 : Item184_1) (h186 : Item186H)
    (hH : Sec18H G A M H c) (h187 : Hyp187 A M H c) {X : Subgroup G} {i j : Fin 4}
    (hi : i ≠ 3) (hj : j ≠ 3) (hij : i ≠ j)
    (hXi : X ≤ Subgroup.normalizer (fourChar (CFSG.Open.pCoreOf 2 (H ⊓ M)) i : Set G))
    (hXj : X ≤ Subgroup.normalizer (fourChar (CFSG.Open.pCoreOf 2 (H ⊓ M)) j : Set G)) :
    X ≤ Subgroup.normalizer (inSubgroup perfectResidual H : Set G) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set S := CFSG.Open.pCoreOf 2 (H ⊓ M)
  have hT : ThreeOfFourNormal H (fourChar S) :=
    (h1813 G A M hH.toSec18Std H hH.mem_scriptH (h186 G A M H c hH h187).1).2
      (h184 G A M hH.toSec18Std H hH.mem_scriptH).1
  have hS2 : IsPGroup 2 S := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 (H ⊓ M)
  have hAH : A ≤ H := le_trans (le_trans le_sup_right le_sup_left) hH.mem_scriptH.2.1.ge
  have hS1 : S ≠ ⊥ := by
    intro hbot
    apply h187.2.1
    have hOH : CFSG.Open.pCoreOf 2 H ≤ S :=
      CFSG.RankThree.PartTwo.Sec18.pCoreOf_le_pCoreOf_inf hH.toSec18Std hAH
    exact le_bot_iff.mp (hOH.trans hbot.le)
  have hSH : S ≤ H := (CFSG.LieType.BorelTits.pCoreOf_le 2 (H ⊓ M)).trans inf_le_left
  have hfc : ∀ k : Fin 4, fourChar S k ≤ S := by
    intro k
    fin_cases k <;> exact Subgroup.map_subtype_le _
  have hne0 : fourChar S 0 ≠ ⊥ := by
    rw [CFSG.RankThree.PartTwo.Sec18.Item181ThreeProof.fourChar_zero]
    exact CFSG.RankThree.PartTwo.Sec18.Item181ThreeProof.omegaG_ne_bot hS2 hS1
  have hne1 : fourChar S 1 ≠ ⊥ := by
    rw [CFSG.RankThree.PartTwo.Sec18.Item181ThreeProof.fourChar_one]
    exact CFSG.RankThree.PartTwo.Sec18.Item181ThreeProof.jG_zero_ne_bot hS2 hS1
  have hT01 : fourChar S 2 = ⊥ → fourChar S 0 = fourChar S 1 := by
    intro h
    rw [CFSG.RankThree.PartTwo.Sec18.Item181ThreeProof.fourChar_two] at h
    rw [CFSG.RankThree.PartTwo.Sec18.Item181ThreeProof.fourChar_zero,
      CFSG.RankThree.PartTwo.Sec18.Item181ThreeProof.fourChar_one]
    exact CFSG.RankThree.PartTwo.Sec20.Res5.omegaG_eq_jG_zero_of_omegaG_jG_one_eq_bot hS2 hS1 h
  have key : ∀ m : Fin 4, fourChar S m ≠ ⊥ → X ≤ Subgroup.normalizer (fourChar S m : Set G) →
      H ≤ Subgroup.normalizer (fourChar S m : Set G) →
      X ≤ Subgroup.normalizer (inSubgroup perfectResidual H : Set G) := fun m hm hXm hHm =>
    hXm.trans (CFSG.RankThree.PartTwo.Sec18.Item187Proof.normalizer_le_of_le_normalizer
      h186 hH h187 hm ((hfc m).trans hSH) hHm)
  have hcase : ∀ a : Fin 4, a ≠ 3 → a = 0 ∨ a = 1 ∨ a = 2 := by decide
  have hmin : ∀ a b : Fin 4, a ≠ 3 → b ≠ 3 → a ≠ b → a = 0 ∨ a = 1 ∨ b = 0 ∨ b = 1 := by
    decide
  by_cases h2 : fourChar S 2 = ⊥
  ·
    have h01 := hT01 h2
    have hX0 : X ≤ Subgroup.normalizer (fourChar S 0 : Set G) := by
      rcases hmin i j hi hj hij with h | h | h | h
      · subst h; exact hXi
      · subst h; rw [h01]; exact hXi
      · subst h; exact hXj
      · subst h; rw [h01]; exact hXj
    have hH0 : H ≤ Subgroup.normalizer (fourChar S 0 : Set G) := by
      rcases hT 0 1 (by decide) with h | h
      · exact h
      · rw [h01]; exact h
    exact key 0 hne0 hX0 hH0
  · have hne : ∀ a : Fin 4, a ≠ 3 → fourChar S a ≠ ⊥ := by
      intro a ha
      rcases hcase a ha with rfl | rfl | rfl
      · exact hne0
      · exact hne1
      · exact h2
    rcases hT i j hij with h | h
    · exact key i (hne i hi) hXi h
    · exact key j (hne j hj) hXj h

end CFSG.RankThree.PartTwo.Sec18.Item187Proof
