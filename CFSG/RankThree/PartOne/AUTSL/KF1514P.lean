module

public import CFSG.RankThree.PartOne.S12.Sec1514Defs

public section

namespace CFSG.RankThree.PartOne

open CFSG CFSG.Assembly CFSG.Assembly.RankThreeEven CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory

namespace AUTSL

@[expose] def KF1514PRow (r : ℕ) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (I H T A₀ : Subgroup G),
    Config1514 p I H T A₀ → LieRow r p I → (r = 3 ∨ r = 4 → T ≤ I) →
    (∃ h ∈ H, ∃ B : Subgroup G, B ≤ A₀ ∧ Nat.card ↥A₀ ≤ p * Nat.card ↥B ∧
      B.map (MulAut.conj h).toMonoidHom ≤ I ⊓ Subgroup.normalizer (pushingUpS T : Set G)) ∧
    (∃ x ∈ omegaOneCenterIn T, x ≠ 1 ∧ ∃ h ∈ H, ∃ B : Subgroup G, B ≤ A₀ ∧
      Nat.card ↥A₀ ≤ p * Nat.card ↥B ∧
      B.map (MulAut.conj h).toMonoidHom ≤ I ⊓ Subgroup.centralizer ({x} : Set G))

@[expose] def KF1514P : Prop := ∀ r : ℕ, 1 ≤ r → r ≤ 4 → KF1514PRow r

end AUTSL

end CFSG.RankThree.PartOne
