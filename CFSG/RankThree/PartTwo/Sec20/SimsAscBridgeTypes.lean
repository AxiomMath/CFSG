module

public import CFSG.RankThree.PartTwo.Sec20.OneSteps
import CFSG.RankThree.PartTwo.Sec20.Item20Res6ProofTools

public section

namespace CFSG.RankThree.PartTwo.Sec20

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL projSU)

@[expose] def Step204AscJ1 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 →
        (∀ m : ℕ, ¬ Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField 2 m))) →
        ¬ yTwenty X c ≤ kTwenty M c ⊔ oThreePrimeYR M X T c →
        Nonempty (↥(yAlpha M X T c) ≃* CFSG.Blueprint.NativeSporadic.J1) →
          CoveredByNormalizer M X T c i ∨ CoveredByNormalizer M X T c j

@[expose] def Step204AscL2Odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 →
        (∀ m : ℕ, ¬ Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField 2 m))) →
        ¬ yTwenty X c ≤ kTwenty M c ⊔ oThreePrimeYR M X T c →
        (∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ p ≠ 3 ∧ 1 ≤ e ∧
          Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField p e))) →
          CoveredByNormalizer M X T c i ∨ CoveredByNormalizer M X T c j

@[expose] def Step204AscL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 →
        (∀ m : ℕ, ¬ Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField 2 m))) →
        ¬ yTwenty X c ≤ kTwenty M c ⊔ oThreePrimeYR M X T c →
        ((∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ p ^ e % 3 = 2 ∧
            Nonempty (↥(yAlpha M X T c) ≃* projSL 3 (GaloisField p e))) ∨
          (∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧ p ^ e % 3 = 1 ∧
            Nonempty (↥(yAlpha M X T c) ≃* projSU 3 p e))) →
          CoveredByNormalizer M X T c i ∨ CoveredByNormalizer M X T c j

@[expose] def Step204AscL3Even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 →
        (∀ m : ℕ, ¬ Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField 2 m))) →
        ¬ yTwenty X c ≤ kTwenty M c ⊔ oThreePrimeYR M X T c →
        (∃ m : ℕ, Odd m ∧ Nonempty (↥(yAlpha M X T c) ≃* projSL 3 (GaloisField 2 m))) →
          CoveredByNormalizer M X T c i ∨ CoveredByNormalizer M X T c j

@[expose] def Step204AscL3Odd : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 →
        (∀ m : ℕ, ¬ Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField 2 m))) →
        ¬ yTwenty X c ≤ kTwenty M c ⊔ oThreePrimeYR M X T c →
        ((∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧ p ^ e % 3 = 2 ∧
            Nonempty (↥(yAlpha M X T c) ≃* projSL 3 (GaloisField p e))) ∨
          (∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧ p ^ e % 3 = 1 ∧
            Nonempty (↥(yAlpha M X T c) ≃* projSU 3 p e))) →
          CoveredByNormalizer M X T c i ∨ CoveredByNormalizer M X T c j

theorem odd_of_two_pow_mod_three {m : ℕ} (h : 2 ^ m % 3 = 2) : Odd m := by
  rcases Nat.even_or_odd m with ⟨k, rfl⟩ | ho
  · exfalso
    rw [← two_mul, pow_mul, Nat.pow_mod] at h
    norm_num at h
  · exact ho

theorem step204AscL3_of_split (hE : Step204AscL3Even) (hO : Step204AscL3Odd) : Step204AscL3 := by
  intro G _ _ A M L N c T i j P hset X hX hXM hm hL2m hYK h
  rcases h with ⟨p, e, hp, he, hpe, hiso⟩ | h
  · by_cases hp2 : p = 2
    · subst hp2
      exact hE G A M L N c T i j P hset X hX hXM hm hL2m hYK
        ⟨e, odd_of_two_pow_mod_three hpe, hiso⟩
    · exact hO G A M L N c T i j P hset X hX hXM hm hL2m hYK
        (Or.inl ⟨p, e, hp, hp2, he, hpe, hiso⟩)
  · exact hO G A M L N c T i j P hset X hX hXM hm hL2m hYK (Or.inr h)

@[expose] def Step204AscU3Even : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 →
        (∀ m : ℕ, ¬ Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField 2 m))) →
        ¬ yTwenty X c ≤ kTwenty M c ⊔ oThreePrimeYR M X T c →
        (∃ m : ℕ, Even m ∧ 0 < m ∧ Nonempty (↥(yAlpha M X T c) ≃* projSU 3 2 m)) →
          CoveredByNormalizer M X T c i ∨ CoveredByNormalizer M X T c j

@[expose] def Step204YAlphaClass : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A M L N : Subgroup G) (c : G) (T : Subgroup G)
    (i j : Fin 4) (P : Subgroup G), Setting204 G A M L N c T i j P →
      ∀ X ∈ scriptM ((kTwenty M c ⊔ T : Subgroup G) : Set G), X ≠ M →
        CFSG.Open.pRank 3 (yTwenty X c) ≤ 1 →
        (∀ m : ℕ, ¬ Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField 2 m))) →
        ¬ yTwenty X c ≤ kTwenty M c ⊔ oThreePrimeYR M X T c →
          Nonempty (↥(yAlpha M X T c) ≃* CFSG.Blueprint.NativeSporadic.J1) ∨
          (∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ p ≠ 3 ∧ 1 ≤ e ∧
            Nonempty (↥(yAlpha M X T c) ≃* projSL 2 (GaloisField p e))) ∨
          ((∃ (p e : ℕ) (_ : Fact p.Prime), 1 ≤ e ∧ p ^ e % 3 = 2 ∧
              Nonempty (↥(yAlpha M X T c) ≃* projSL 3 (GaloisField p e))) ∨
            (∃ (p e : ℕ) (_ : Fact p.Prime), p ≠ 2 ∧ 1 ≤ e ∧ p ^ e % 3 = 1 ∧
              Nonempty (↥(yAlpha M X T c) ≃* projSU 3 p e))) ∨
          (∃ m : ℕ, Even m ∧ 0 < m ∧ Nonempty (↥(yAlpha M X T c) ≃* projSU 3 2 m))

theorem step204Asc1411_of_types (hcls : Step204YAlphaClass) (hJ1 : Step204AscJ1)
    (hL2 : Step204AscL2Odd) (hL3 : Step204AscL3) (hU3 : Step204AscU3Even) : Step204Asc1411 := by
  intro G _ _ A M L N c T i j P hset X hX hXM hm hL2m
  by_cases hYK : yTwenty X c ≤ kTwenty M c ⊔ oThreePrimeYR M X T c
  ·
    have hKX : kTwenty M c ≤ X := fun x hx => hX.2 (Subgroup.mem_sup_left hx)
    have hKN : kTwenty M c ≤ yTwenty X c ⊓ Subgroup.normalizer
        (Sec18.fourChar (CFSG.Open.pCoreOf 2 (kTwenty M c ⊔ T)) i : Set G) :=
      le_inf (Res6.kTwenty_le_yTwenty hset hKX) (le_sup_left.trans (le_sup_left.trans
        hset.normal_left))
    exact Or.inl (hYK.trans (sup_le_sup_right hKN _))
  rcases hcls G A M L N c T i j P hset X hX hXM hm hL2m hYK with h | h | h | h
  · exact hJ1 G A M L N c T i j P hset X hX hXM hm hL2m hYK h
  · exact hL2 G A M L N c T i j P hset X hX hXM hm hL2m hYK h
  · exact hL3 G A M L N c T i j P hset X hX hXM hm hL2m hYK h
  · exact hU3 G A M L N c T i j P hset X hX hXM hm hL2m hYK h

end CFSG.RankThree.PartTwo.Sec20
