module

public import CFSG.RankThree.GF2n.Stroth80.Sec8Defs

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

@[expose] def Sec8StrongClosureStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    StronglyClosedMod M Z0 (LB M Q B ⊓ hc.CN t)

@[expose] def Sec8V1InterDimStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → ∀ r : G, Sec7A hc t r → ∀ m : ℕ, SpMNat hc t m →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    ∀ s ∈ Z0, s ∉ Q → ∀ g ∈ M,
      (∀ w ∈ Sec8W1 M Q Z B t r, ⁅g * s * g⁻¹, w⁆ ∈ Sec8V1 M Q Z B t r) →
      Nat.card Z ^ (m + 1) ≤
        Nat.card ↥(Sec8V1 M Q Z B t r ⊓ conjSubgroup g (Vt M (LB M Q B) B Z t))

@[expose] def Sec84CommUpperStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → SpMNat hc t 4 →
    ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    Nat.card ↥(hc.CN t) = Nat.card ↥Z0 * Nat.card Z ^ (2 ^ 4) →
    ⁅hc.CN t, hc.CN t⁆ ≤ Q → (∀ c ∈ hc.CN t, c ^ 2 ∈ Q) →
    StronglyClosedMod M Z0 (LB M Q B ⊓ hc.CN t) →
    (∀ g ∈ M, ∀ u ∈ Z0, u ∉ Q → g * u * g⁻¹ ∈ Z0 → g ∈ Subgroup.normalizer (Z0 : Set G)) →
    ∀ ν ∈ M, ν ∈ Subgroup.normalizer (LB M Q B : Set G) →
      ν ∉ Subgroup.normalizer (Z0 : Set G) →
    ∀ x ∈ conjSubgroup ν Z0, x ∉ Q →
      Nat.card ↥(CommSec (hc.CN t) Q x) ≤ Nat.card ↥Q * Nat.card Z ^ 3

@[expose] def Sp6NoEmbeddingStatement : Prop :=
  ∀ (K : Type) [Field K] [Finite K] [CharP K 2], 4 ≤ Nat.card K →
  ∀ (N : Type) [AddCommGroup N] [Finite N] [DistribMulAction ↥(CFSG.Open.StatedSp 3 K) N],
    Nat.card N = Nat.card K ^ 8 → (∃ (g : ↥(CFSG.Open.StatedSp 3 K)) (a : N), g • a ≠ a) →
    (∀ S : AddSubgroup N, (∀ (g : ↥(CFSG.Open.StatedSp 3 K)), ∀ a ∈ S, g • a ∈ S) →
      S = ⊥ ∨ S = ⊤) →
  ∀ (X : Type) [AddCommGroup X] [Module K X] [Module.Finite K X]
    [DistribMulAction ↥(CFSG.Open.StatedSp 3 K) X],
    (∀ (g : ↥(CFSG.Open.StatedSp 3 K)) (c : K) (x : X), g • (c • x) = c • (g • x)) →
    Module.finrank K X = 8 →
  ∀ f : N →+ ((Fin 3 ⊕ Fin 3 → K) →ₗ[K] X),
    (∀ (g : ↥(CFSG.Open.StatedSp 3 K)) (a : N) (v : Fin 3 ⊕ Fin 3 → K),
      f (g • a) v = g • f a ((((g⁻¹ : ↥(CFSG.Open.StatedSp 3 K)) : GL (Fin 3 ⊕ Fin 3) K) :
        Matrix (Fin 3 ⊕ Fin 3) (Fin 3 ⊕ Fin 3) K) *ᵥ v)) →
    Function.Injective f → False

@[expose] def Sec84NAbelianStatement : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (M Q Z B : Subgroup G) (hc : Ctx M Q Z B) (n : ℕ) (t : G),
    Sec8Hyp hc n t → SpMNat hc t 3 → ∀ Z0 : Subgroup G, IsCentrePre Z0 (Rt M (LB M Q B) t) Q →
    Nat.card ↥(hc.CN t) = Nat.card ↥Z0 * Nat.card Z ^ 8 →
    IsIrredModule (Rt M (LB M Q B) t) (hc.CN t) Z0 →
    ⁅hc.CN t, hc.CN t⁆ ≤ Q → (∀ c ∈ hc.CN t, c ^ 2 ∈ Q) → False

@[expose] def PSU6OutSolvableStatement : Prop :=
  ∀ (q : ℕ) (Y : Type) [Group Y] [Finite Y] (F : Subgroup Y) [F.Normal],
    IsPSUModel 6 q ↥F → Subgroup.centralizer (F : Set Y) ≤ F → IsSolvable (Y ⧸ F)

@[expose] def PSU6TwoPartStatement : Prop :=
  ∀ (f : ℕ) (X : Type) [Group X] [Finite X], 1 ≤ f → IsPSUModel 6 (2 ^ f) X →
    ∃ o : ℕ, Odd o ∧ Nat.card X = (2 ^ f) ^ 15 * o

end CFSG.RankThree.GF2n.Stroth80
