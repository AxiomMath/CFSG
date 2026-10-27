module

public import CFSG.Quasithin.H13.NQCoreP134Inputs

public section

namespace CFSG.Quasithin.S146zY

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.QuasithinUnique.Vol2Native CFSG.Quasithin.H13.NQCore

@[expose] def NormalOutcome {A : Type} [Group A] (p : ℕ) [Fact p.Prime] (L P T : Subgroup A) :
    Prop :=
  (StatedClassicalModel ↥L .PSL 3 p 1 ∨ Nonempty (↥L ≃* ↥(StatedSL 3 (ZMod p)))) ∨
    EmptyFaithfulMultiple.AutCyclic T P

@[expose] def OutNoE25Fact : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 5 → ∀ (A : Type) [Group A] [Finite A]
    (L P : Subgroup A), SQTKHypCat A → L.Normal → CFSG.IsComponent L →
    ¬ p ∣ Nat.card L → P ≤ commutator A → (∀ x ∈ P, x ^ p = 1) → Nat.card P = p ^ 2 →
    P ⊓ (L ⊔ Subgroup.centralizer (L : Set A)) ≠ ⊥

@[expose] def NormalFiveFact : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p = 5 → ∀ (A : Type) [Group A] [Finite A]
    (L P T : Subgroup A), OddConfig p L P T → Nat.card P = p ^ 2 → NormalOutcome p L P T

structure NormalInputs : Prop where
  outNoE25 : OutNoE25Fact
  normal : NormalFiveFact

end CFSG.Quasithin.S146zY
