module

public import CFSG.Open.Defs
public import CFSG.GroupTheory.Fitting.WholeGroupConstruction

public section

namespace CFSG.Open

@[expose] def signalizerFixedSubgroup {X : Type*} [Group X] (f : MulAut X) : Subgroup X where
  carrier := {x | f x = x}
  one_mem' := map_one f
  mul_mem' := by
    intro x y hx hy
    change f (x * y) = x * y
    rw [map_mul, hx, hy]
  inv_mem' := by
    intro x hx
    change f x⁻¹ = x⁻¹
    rw [map_inv, hx]

@[expose] def signalizerGeneralizedFitting (X : Type*) [Group X] : Subgroup X :=
  CFSG.WholeGroup.fstarOf (CFSG.WholeGroup.layerOf fun L : Subgroup X => IsComponentOf L ⊤)

theorem signalizerGeneralizedFitting.eq_sup (X : Type*) [Group X] :
    signalizerGeneralizedFitting X = sSup {N : Subgroup X | N.Normal ∧ Group.IsNilpotent N} ⊔
      sSup {L : Subgroup X | IsComponentOf L ⊤} :=
  rfl

attribute [eqns signalizerGeneralizedFitting.eq_sup] signalizerGeneralizedFitting

@[expose] def signalizerNearSimpleModel (p : ℕ) (X : Type*) [Group X] : Prop :=
  Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 2 p)) ∨
  Nonempty (X ≃* Matrix.ProjectiveSpecialLinearGroup (Fin 2) (GaloisField 3 p)) ∨
  (∃ n : ℕ, p = 2 * n + 1 ∧ Nonempty (X ≃* Sz n)) ∨
  Nonempty (X ≃* PSU3 2 p)

@[expose] def signalizerNearPSolvable (p : ℕ) (X : Type*) [Group X] : Prop :=
  Nat.Coprime p (Nat.card X) ∧
    ∀ (K L : Subgroup X), L ≤ K → ∀ [(L.subgroupOf K).Normal],
      IsSimpleGroup (K ⧸ L.subgroupOf K) →
      (∃ a b : K ⧸ L.subgroupOf K, a * b ≠ b * a) →
      signalizerNearSimpleModel p (K ⧸ L.subgroupOf K)

@[expose] def signalizerMcBrideHypothesisA (p : ℕ) (X : Type*) [Group X] [Finite X] : Prop :=
  p.Prime ∧ IsSimpleGroup X ∧ (∃ a b : X, a * b ≠ b * a) ∧
    Nat.Coprime p (Nat.card X) ∧
    (∀ P : Subgroup (MulAut X), IsPGroup p P → IsCyclic P) ∧
    (signalizerNearPSolvable p X ∨
      ∀ f : MulAut X, orderOf f = p →
        let C := signalizerFixedSubgroup f
        (∀ T : Subgroup X, T ≠ ⊥ → Group.IsSolvable T →
          ¬ C ≤ Subgroup.normalizer (T : Set X)) ∧
        (IsSimpleGroup (signalizerGeneralizedFitting C) ∧
          ∃ a b : signalizerGeneralizedFitting C, a * b ≠ b * a) ∧
        (∀ g : MulAut X, Nat.Coprime p (orderOf g) →
          (∀ x ∈ C, g x = x) → g = 1))

@[expose] def signalizerMcBrideHypothesisB {G : Type*} [Group G] [Finite G]
    (p : ℕ) (H : Subgroup G) : Prop :=
  p.Prime ∧ Nat.Coprime p (Nat.card H) ∧
    ∀ (K L : Subgroup G), K ≤ H → L ≤ K → ∀ [(L.subgroupOf K).Normal],
      IsSimpleGroup (K ⧸ L.subgroupOf K) →
      (∃ a b : K ⧸ L.subgroupOf K, a * b ≠ b * a) →
      signalizerMcBrideHypothesisA p (K ⧸ L.subgroupOf K)

end CFSG.Open
