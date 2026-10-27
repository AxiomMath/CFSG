module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13Stmts

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LocalAnalysis.UniquenessCase.PartTwo CFSG.Quasithin CFSG.Open Subgroup
open scoped commutatorElement

structure Cfg132 {W : Type} [CommGroup W] [Finite W] (t : MulAut W)
    (P : Subgroup (MulAut W)) : Prop where
  hW : ∀ w : W, w ^ 2 = 1
  ht : orderOf t = 2
  hrk : rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3
  hP : IsPGroup 3 ↥P
  hne : P ≠ ⊥
  hn : ∀ x ∈ P, t * x * t⁻¹ ∈ P
  hc : ⁅P, Subgroup.zpowers t⁆ = P

@[expose] def MinFaith132 {W : Type} [CommGroup W] (t : MulAut W) (P : Subgroup (MulAut W)) :
    Prop :=
  ∀ U : Subgroup W, StableUnder (P ⊔ Subgroup.zpowers t) U →
    (∀ y ∈ P ⊔ Subgroup.zpowers t, (∀ u ∈ U, y u = u) → y = 1) → U = ⊤

@[expose] def NoDecomp132 {W : Type} [CommGroup W] (t : MulAut W) (P : Subgroup (MulAut W)) :
    Prop :=
  ∀ U U' : Subgroup W, StableUnder (P ⊔ Subgroup.zpowers t) U →
    StableUnder (P ⊔ Subgroup.zpowers t) U' → U ⊓ U' = ⊥ → U ⊔ U' = ⊤ → U = ⊤ ∨ U' = ⊤

@[expose] def Concl132Min {W : Type} [CommGroup W] [Finite W] (t : MulAut W)
    (P : Subgroup (MulAut W)) : Prop :=
  (IsCyclic ↥P ∧ Nat.card P ≤ 9) ∨
  (∃ k : ℕ, k ≤ 3 ∧ IsElemAbelianOfRank 3 k ↥P) ∨
  (IsPOnePlusTwo 3 ↥P ∧ rk ↥(commSub ⊤ P) = 6) ∨
  ((IsZ3TimesPOnePlusTwo ↥P ∨ IsZ3WrZ3 ↥P) ∧
    rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3 ∧
    ∃! Q : Subgroup (MulAut W), Q ≤ P ∧ IsPOnePlusTwo 3 ↥Q ∧ rk ↥(commSub ⊤ Q) = 6)

@[expose] def W4Lem13_2MinLe (n : ℕ) : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ t : MulAut W, orderOf t = 2 → rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3 →
      ∀ (p : ℕ) (P : Subgroup (MulAut W)), p.Prime → IsPGroup p ↥P → P ≠ ⊥ →
        (∀ x ∈ P, t * x * t⁻¹ ∈ P) → ⁅P, Subgroup.zpowers t⁆ = P → Nat.card P ≤ n →
          MinFaith132 t P →
          (IsCyclic ↥P ∧ Nat.card P ≤ 9) ∨
          (∃ k : ℕ, k ≤ 3 ∧ IsElemAbelianOfRank 3 k ↥P) ∨
          (IsPOnePlusTwo 3 ↥P ∧ rk ↥(commSub ⊤ P) = 6) ∨
          ((IsZ3TimesPOnePlusTwo ↥P ∨ IsZ3WrZ3 ↥P) ∧
            rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3 ∧
            ∃! Q : Subgroup (MulAut W), Q ≤ P ∧ IsPOnePlusTwo 3 ↥Q ∧ rk ↥(commSub ⊤ Q) = 6)

@[expose] def W4Lem13_2ShapeLe (n : ℕ) : Prop :=
  ∀ (W : Type) [CommGroup W] [Finite W], (∀ w : W, w ^ 2 = 1) →
    ∀ t : MulAut W, orderOf t = 2 → rk ↥(commSub ⊤ (Subgroup.zpowers t)) ≤ 3 →
      ∀ (p : ℕ) (P : Subgroup (MulAut W)), p.Prime → IsPGroup p ↥P → P ≠ ⊥ →
        (∀ x ∈ P, t * x * t⁻¹ ∈ P) → ⁅P, Subgroup.zpowers t⁆ = P → Nat.card P ≤ n →
          (IsCyclic ↥P ∧ Nat.card P ≤ 9) ∨
          (∃ k : ℕ, k ≤ 3 ∧ IsElemAbelianOfRank 3 k ↥P) ∨
          IsPOnePlusTwo 3 ↥P ∨
          ((IsZ3TimesPOnePlusTwo ↥P ∨ IsZ3WrZ3 ↥P) ∧
            rk ↥(commSub ⊤ (Subgroup.zpowers t)) = 3)

end CFSG.LocalAnalysis.WeakClosure81
