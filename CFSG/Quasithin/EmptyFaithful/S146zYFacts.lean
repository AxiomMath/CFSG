module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeBasicBase

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native
open scoped commutatorElement

@[expose] def OutAbelianFact : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L : Subgroup A), SQTKHypCat A →
    CFSG.IsComponent L → A38Types ↥L → ∀ a ∈ Subgroup.normalizer (L : Set A),
      ∀ b ∈ Subgroup.normalizer (L : Set A), ⁅a, b⁆ ∈ L ⊔ Subgroup.centralizer (L : Set A)

@[expose] def Psl2BorelFact : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L B U : Subgroup A) (m p : ℕ) (y : A),
    p.Prime → 5 ≤ p → IsPSL 2 2 m ↥L → U ≤ B → B ≤ L → IsSylowTwoOf U L →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = p) → y ∈ B → orderOf y = p →
      p ∣ 2 ^ m - 1

@[expose] def SzNoFiveFact : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L B U : Subgroup A) (m : ℕ) (y : A),
    IsSz m ↥L → U ≤ B → B ≤ L → IsSylowTwoOf U L →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = 5) → y ∈ B → orderOf y = 5 → False

@[expose] def J1NoFiveFact : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (L B U : Subgroup A) (y : A),
    IsSporadic .J1 ↥L → U ≤ B → B ≤ L → IsSylowTwoOf U L →
      (∀ q : ℕ, q.Prime → q ∣ Nat.card B → q = 2 ∨ q = 5) → y ∈ B → orderOf y = 5 → False

end CFSG.Quasithin.S146zY
