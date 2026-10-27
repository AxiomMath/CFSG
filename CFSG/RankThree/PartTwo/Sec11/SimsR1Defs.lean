module

public import CFSG.RankThree.PartTwo.Sec11.Item116H3KFact

public section

namespace CFSG.RankThree.PartTwo.Sec11

open CFSG.Assembly.RankThreeEven (projSL)

@[expose] def SimsR1L38FaithfulFix : Prop :=
  ∀ (r : ℕ) [Fact r.Prime], 5 ≤ r → ∀ (V : Type) [AddCommGroup V] [Module (ZMod r) V]
    [Module.Finite (ZMod r) V] (ρ : projSL 3 (GaloisField 2 3) →* (V →ₗ[ZMod r] V)),
    Function.Injective ρ → ∃ t : projSL 3 (GaloisField 2 3), orderOf t = 2 ∧
      3 ≤ Module.finrank (ZMod r) (LinearMap.ker (ρ t - 1))

@[expose] def SimsR1L38SolvableFix : Prop :=
  ∀ (r : ℕ) [Fact r.Prime], 5 ≤ r →
    ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
      ∀ (N : Subgroup X) [N.Normal], Group.IsSolvable N → ¬ 3 ∣ Nat.card N →
        Nonempty (X ⧸ N ≃* projSL 3 (GaloisField 2 3)) →
      ∀ (V : Type) [AddCommGroup V] [Module (ZMod r) V] [Module.Finite (ZMod r) V]
        (ρ : X →* (V →ₗ[ZMod r] V)), ¬ N ≤ ρ.ker →
          ∃ t : X, ρ t ≠ 1 ∧ (∃ k : ℕ, t ^ 2 ^ k = 1) ∧
            3 ≤ Module.finrank (ZMod r) (LinearMap.ker (ρ t - 1))

@[expose] def SimsR1L38AutFacts : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Sec8.IsoLThreeMinusPi X 2 3 →
    (∀ x : X, orderOf x = 3 → ∀ P : Subgroup (MulAut X), IsPGroup 2 P →
      (∀ τ ∈ P, τ x = x) → IsCyclic P) ∧
    (∀ σ : MulAut X, orderOf σ = 3 → σ ∉ (MulAut.conj : X →* MulAut X).range →
      CFSG.pCore 2 (Sec11.fixedSub σ) = ⊥) ∧
    (∀ σ τ : MulAut X, orderOf σ = 3 → σ ∉ (MulAut.conj : X →* MulAut X).range →
      (∃ k : ℕ, τ ^ 2 ^ k = 1) → (∀ x ∈ Sec11.fixedSub σ, τ x = x) → τ = 1)

@[expose] def SimsR1L2CubeFaithfulFix : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (r : ℕ) [Fact r.Prime], 5 ≤ r →
    ∀ (V : Type) [AddCommGroup V] [Module (ZMod r) V] [Module.Finite (ZMod r) V]
      (ρ : projSL 2 (GaloisField p (3 * 1)) →* (V →ₗ[ZMod r] V)), Function.Injective ρ →
        ∃ t : projSL 2 (GaloisField p (3 * 1)), orderOf t = 2 ∧
          3 ≤ Module.finrank (ZMod r) (LinearMap.ker (ρ t - 1))

@[expose] def SimsR1L2CubeSolvableFix : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (r : ℕ) [Fact r.Prime], 5 ≤ r →
    ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X →
      ∀ (N : Subgroup X) [N.Normal], Group.IsSolvable N → Odd (Nat.card N) →
        ¬ 3 ∣ Nat.card N → Nonempty (X ⧸ N ≃* projSL 2 (GaloisField p (3 * 1))) →
      ∀ (V : Type) [AddCommGroup V] [Module (ZMod r) V] [Module.Finite (ZMod r) V]
        (ρ : X →* (V →ₗ[ZMod r] V)), ¬ N ≤ ρ.ker →
          ∃ t : X, ρ t ≠ 1 ∧ (∃ k : ℕ, t ^ 2 ^ k = 1) ∧
            3 ≤ Module.finrank (ZMod r) (LinearMap.ker (ρ t - 1))

@[expose] def SimsR1L2CubeTwoLocal : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (X : Type) [Group X] [Finite X],
    Nonempty (X ≃* projSL 2 (GaloisField p (3 * 1))) →
    ∀ P : Subgroup (MulAut X), IsPGroup 2 P → P ≠ ⊥ → ∀ S : Subgroup X,
      (∀ s ∈ S, MulAut.conj s ∈ Subgroup.normalizer (P : Set (MulAut X))) → Group.IsSolvable S

@[expose] def SimsR1L2CubeCentThree : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], 5 ≤ p → ∀ (X : Type) [Group X] [Finite X],
    Nonempty (X ≃* projSL 2 (GaloisField p (3 * 1))) → ∀ x : X, orderOf x = 3 →
      ∀ P : Subgroup (MulAut X), IsPGroup 2 P → (∀ τ ∈ P, τ x = x) → IsCyclic P

end CFSG.RankThree.PartTwo.Sec11
