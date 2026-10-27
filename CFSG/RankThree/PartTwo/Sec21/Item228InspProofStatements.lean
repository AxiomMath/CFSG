module

public import CFSG.RankThree.PartTwo.Sec21.Item221Proof228Statements

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)

variable {G : Type} [Group G]

@[expose] def Insp228Comm (A : Subgroup G) (φ ψ : MulAut A) : Prop :=
  ψ * φ = φ * ψ →
    ⁅kOf A φ, kOf A ψ⁆ = ⊥ ∨
    (kOf A φ ⊔ kOf A ψ ∈ lStar A ∧ ∃ m : ℕ, 0 < m ∧ m % 4 = 0 ∧
      Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) ∧
      Nonempty (kOf A ψ ≃* projSL 2 (GaloisField 2 m)) ∧
      Nonempty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* projSU 4 2 (m / 2)) ∧
      ∃ w ∈ wStar A, w * φ * w⁻¹ = ψ) ∨
    (Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 4)) ∧
      Nonempty (kOf A ψ ≃* projSL 2 (GaloisField 2 4)) ∧
      Nonempty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* projSU 4 2 2) ∧
      (∃ X' ∈ lStar A, kOf A φ ⊔ kOf A ψ ≤ X' ∧ Nonempty (X' ≃* projSU 5 2 2)) ∧
      ∃ w ∈ wStar A, w * φ * w⁻¹ = ψ)

@[expose] def Insp228NonComm (A : Subgroup G) (φ ψ : MulAut A) : Prop :=
  ψ * φ ≠ φ * ψ →
    (kOf A φ ⊔ kOf A ψ ∈ lStar A ∧ Case222 A (kOf A φ ⊔ kOf A ψ) (kOf A φ) ∧
      IsEmpty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* projSU 5 2 2)) ∨
    (Nonempty ((kOf A φ ⊔ kOf A ψ : Subgroup G) ≃* projSU 4 2 2) ∧
      ∃ X' ∈ lStar A, kOf A φ ⊔ kOf A ψ ≤ X' ∧ Nonempty (X' ≃* projSU 5 2 2))

@[expose] def Fam228SL3 (A : Subgroup G) (φ : MulAut A) (X : Subgroup G) : Prop :=
  ∃ m : ℕ, 0 < m ∧ Even m ∧ Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) ∧
    Nonempty (X ≃* SL3 m)

@[expose] def Fam228Sp4 (A : Subgroup G) (φ : MulAut A) (X : Subgroup G) : Prop :=
  ∃ m : ℕ, 0 < m ∧ Even m ∧ Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) ∧
    Nonempty (X ≃* projSp 2 (GaloisField 2 m))

@[expose] def Fam228U4 (A : Subgroup G) (φ : MulAut A) (X : Subgroup G) : Prop :=
  ∃ m : ℕ, 0 < m ∧ Even m ∧ Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) ∧
    Nonempty (X ≃* projSU 4 2 m)

@[expose] def Fam228U4Half (A : Subgroup G) (φ : MulAut A) (X : Subgroup G) : Prop :=
  ∃ m : ℕ, 0 < m ∧ Even m ∧ Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) ∧
    m % 4 = 0 ∧ Nonempty (X ≃* projSU 4 2 (m / 2))

@[expose] def Fam228U54 (A : Subgroup G) (φ : MulAut A) (X : Subgroup G) : Prop :=
  ∃ m : ℕ, 0 < m ∧ Even m ∧ Nonempty (kOf A φ ≃* projSL 2 (GaloisField 2 m)) ∧
    (m = 2 ∨ m = 4) ∧ Nonempty (X ≃* projSU 5 2 2)

theorem item228OneConcl_iff (A : Subgroup G) (φ : MulAut A) (X : Subgroup G) :
    Item228OneConcl A φ X ↔ Fam228SL3 A φ X ∨ Fam228Sp4 A φ X ∨ Fam228U4 A φ X ∨
      Fam228U4Half A φ X ∨ Fam228U54 A φ X := by
  constructor
  · rintro ⟨m, hm0, hme, hK, h | h | h | ⟨h4, h⟩ | ⟨h24, h⟩⟩
    · exact Or.inl ⟨m, hm0, hme, hK, h⟩
    · exact Or.inr (Or.inl ⟨m, hm0, hme, hK, h⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨m, hm0, hme, hK, h⟩))
    · exact Or.inr (Or.inr (Or.inr (Or.inl ⟨m, hm0, hme, hK, h4, h⟩)))
    · exact Or.inr (Or.inr (Or.inr (Or.inr ⟨m, hm0, hme, hK, h24, h⟩)))
  · rintro (⟨m, hm0, hme, hK, h⟩ | ⟨m, hm0, hme, hK, h⟩ | ⟨m, hm0, hme, hK, h⟩ |
      ⟨m, hm0, hme, hK, h4, h⟩ | ⟨m, hm0, hme, hK, h24, h⟩)
    · exact ⟨m, hm0, hme, hK, Or.inl h⟩
    · exact ⟨m, hm0, hme, hK, Or.inr (Or.inl h)⟩
    · exact ⟨m, hm0, hme, hK, Or.inr (Or.inr (Or.inl h))⟩
    · exact ⟨m, hm0, hme, hK, Or.inr (Or.inr (Or.inr (Or.inl ⟨h4, h⟩)))⟩
    · exact ⟨m, hm0, hme, hK, Or.inr (Or.inr (Or.inr (Or.inr ⟨h24, h⟩)))⟩

@[expose] def Insp228SL3 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
      ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ψ ≠ φ → ∀ X ∈ lStar A, kOf A φ ≤ X → kOf A ψ ≤ X →
        Fam228SL3 A φ X → Item228OneConcl A ψ X →
          Insp228Comm A φ ψ ∧ Insp228NonComm A φ ψ

@[expose] def Insp228Sp4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
      ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ψ ≠ φ → ∀ X ∈ lStar A, kOf A φ ≤ X → kOf A ψ ≤ X →
        Fam228Sp4 A φ X → Item228OneConcl A ψ X →
          Insp228Comm A φ ψ ∧ Insp228NonComm A φ ψ

@[expose] def Insp228U4 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
      ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ψ ≠ φ → ∀ X ∈ lStar A, kOf A φ ≤ X → kOf A ψ ≤ X →
        Fam228U4 A φ X → Item228OneConcl A ψ X →
          Insp228Comm A φ ψ ∧ Insp228NonComm A φ ψ

@[expose] def Insp228U4Half : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
      ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ψ ≠ φ → ∀ X ∈ lStar A, kOf A φ ≤ X → kOf A ψ ≤ X →
        Fam228U4Half A φ X → Item228OneConcl A ψ X →
          Insp228Comm A φ ψ ∧ Insp228NonComm A φ ψ

@[expose] def Insp228U54 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A E U : Subgroup G) (c : G) (L : Subgroup G),
    Sec21Pair G A E U c L → Nat.card A = 3 ^ 3 →
      ∀ φ ∈ dStar A, ∀ ψ ∈ dStar A, ψ ≠ φ → ∀ X ∈ lStar A, kOf A φ ≤ X → kOf A ψ ≤ X →
        Fam228U54 A φ X → Item228OneConcl A ψ X →
          Insp228Comm A φ ψ ∧ Insp228NonComm A φ ψ

theorem item228Inspection_of_families (hSL3 : Insp228SL3) (hSp4 : Insp228Sp4)
    (hU4 : Insp228U4) (hU4h : Insp228U4Half) (hU54 : Insp228U54) : Item228Inspection := by
  intro G _ _ A E U c L hpair hA27 φ hφ ψ hψ hne X hX hKX hJX hφX hψX
  rcases (item228OneConcl_iff A φ X).mp hφX with h | h | h | h | h
  · exact hSL3 G A E U c L hpair hA27 φ hφ ψ hψ hne X hX hKX hJX h hψX
  · exact hSp4 G A E U c L hpair hA27 φ hφ ψ hψ hne X hX hKX hJX h hψX
  · exact hU4 G A E U c L hpair hA27 φ hφ ψ hψ hne X hX hKX hJX h hψX
  · exact hU4h G A E U c L hpair hA27 φ hφ ψ hψ hne X hX hKX hJX h hψX
  · exact hU54 G A E U c L hpair hA27 φ hφ ψ hψ hne X hX hKX hJX h hψX

end CFSG.RankThree.PartTwo.Sec21
