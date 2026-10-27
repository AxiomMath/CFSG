module

public import CFSG.RankThree.PartTwo.Sec21.Hering233iStatements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly (IsElemAbelian)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

@[expose] def TerminalE16U58 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I A : Subgroup G), A ≤ I → IsElemAbelian 3 A →
    (Nonempty (I ≃* projSU 5 2 3) ∧ Nat.card A = 3 ^ 4) →
    ∀ B : Subgroup G, B ≤ A → Nat.card B = 3 →
      ∀ X : Subgroup (I ⊓ Subgroup.centralizer (B : Set G) : Subgroup G),
        CFSG.IsComponent X →
        ∃ E : Subgroup G, E ≤ I ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ 4 ∧
          E ≤ Subgroup.normalizer (B : Set G) ∧
          E ≤ Subgroup.normalizer
            ((X.map (I ⊓ Subgroup.centralizer (B : Set G)).subtype : Subgroup G) : Set G)

@[expose] def TerminalE16L44 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I A : Subgroup G), A ≤ I → IsElemAbelian 3 A →
    (Nonempty (I ≃* projSL 4 (GaloisField 2 2)) ∧ Nat.card A = 3 ^ 3) →
    ∀ B : Subgroup G, B ≤ A → Nat.card B = 3 →
      ∀ X : Subgroup (I ⊓ Subgroup.centralizer (B : Set G) : Subgroup G),
        CFSG.IsComponent X →
        (∃ E : Subgroup G, E ≤ I ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ 4 ∧
            E ≤ Subgroup.normalizer (B : Set G) ∧
            E ≤ Subgroup.normalizer
              ((X.map (I ⊓ Subgroup.centralizer (B : Set G)).subtype : Subgroup G) : Set G)) ∨
          ((∀ X' : Subgroup (I ⊓ Subgroup.centralizer (B : Set G) : Subgroup G),
              CFSG.IsComponent X' → X' = X) ∧ Nat.card X = 60)

@[expose] def TerminalE16Sp64 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (I A : Subgroup G), A ≤ I → IsElemAbelian 3 A →
    (Nonempty (I ≃* projSp 3 (GaloisField 2 2)) ∧ Nat.card A = 3 ^ 3) →
    ∀ B : Subgroup G, B ≤ A → Nat.card B = 3 →
      ∀ X : Subgroup (I ⊓ Subgroup.centralizer (B : Set G) : Subgroup G),
        CFSG.IsComponent X →
        ∃ E : Subgroup G, E ≤ I ∧ IsElemAbelian 2 E ∧ Nat.card E = 2 ^ 4 ∧
          E ≤ Subgroup.normalizer (B : Set G) ∧
          E ≤ Subgroup.normalizer
            ((X.map (I ⊓ Subgroup.centralizer (B : Set G)).subtype : Subgroup G) : Set G)

theorem terminalE16_of (hU : TerminalE16U58) (hL : TerminalE16L44) (hS : TerminalE16Sp64) :
    TerminalE16 := by
  intro G _ _ I A hAI hA hI B hBA hB3 X hX
  rcases hI with hU' | hL' | hS'
  · exact Or.inl (hU G I A hAI hA hU' B hBA hB3 X hX)
  · rcases hL G I A hAI hA hL' B hBA hB3 X hX with h | ⟨hu, h60⟩
    · exact Or.inl h
    · exact Or.inr ⟨hL'.1, hL'.2, hu, h60⟩
  · exact Or.inl (hS G I A hAI hA hS' B hBA hB3 X hX)

end CFSG.RankThree.PartTwo.Sec21
