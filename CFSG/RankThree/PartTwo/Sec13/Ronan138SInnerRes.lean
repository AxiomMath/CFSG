module

public import CFSG.RankThree.PartTwo.Sec13.Ronan138SBase

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open scoped commutatorElement

@[expose] def Step138ENeDBase : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (x y t : G),
    Ronan138S.Frame138Base A L E F c x y t → Subgroup.zpowers ⁅x, y⁆ ∉ omegaA E

@[expose] def Step138KStrIn : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L E F : Subgroup G) (x y t : G),
    Ronan138S.Frame138Base A L E F c x y t → E ≤ Subgroup.zpowers c ⊔ L →
    Subgroup.zpowers ⁅x, y⁆ ∉ omegaA E →
    (∃ n ∈ L ⊓ Subgroup.centralizer (E : Set G), (∃ k : ℕ, n ^ 3 ^ k = 1) ∧
      n ^ 3 ∈ Subgroup.zpowers ⁅x, y⁆ ∧ n ^ 3 ≠ 1) →
    ∃ (e : G) (K : Subgroup G), Subgroup.zpowers e ∈ omegaA E ∧ K ∈ lA E e ∧ e ∈ F ∧
      e ∉ Subgroup.zpowers c ∧ e ∉ L ∧
      (Sec8.IsZ3PGLThreePi (lBarA e K E) ∨
        Nonempty (lBarA e K E ≃* Multiplicative (ZMod 3) × CFSG.Blueprint.NativeSporadic.M12))

@[expose] def KF138OutAbelian : Prop :=
  ∀ (X : Type) [Group X] [Finite X], IsLThreePi X → IsQuasisimple X →
    ∀ σ τ : MulAut X, (∃ k : ℕ, σ ^ 3 ^ k = 1) → (∃ k : ℕ, τ ^ 3 ^ k = 1) →
      σ * τ * σ⁻¹ * τ⁻¹ ∈ (MulAut.conj : X →* MulAut X).range

end CFSG.RankThree.PartTwo.Sec13
