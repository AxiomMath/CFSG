module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClDefs

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

@[expose] def LemmaPSubStatement : Prop :=
  ∀ (K V : Type) [Field K] [Finite K] [CharP K 2] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] (F : LinearMap.BilinForm K V), 4 ≤ Nat.card K → F.Nondegenerate →
    F.IsAlt → ∀ (e f x x' : V), F e f = 1 → F x x' = 1 → F x e = 0 → F x f = 0 → F x' e = 0 →
    F x' f = 0 → ∀ (A A' : Subgroup (V ≃ₗ[K] V)), A ≤ pointRadSubgroup F e →
    A' ≤ pointRadSubgroup F f → (∀ g ∈ A, g f - f ∈ Submodule.span K {e, x, x'}) →
    (∀ g ∈ A', g e - e ∈ Submodule.span K {f, x, x'}) →
    (∀ w ∈ Submodule.span K {x, x'}, ∃ g ∈ A, ∃ c : K, g f - f = w + c • e) →
    (∀ w ∈ Submodule.span K {x, x'}, ∃ g ∈ A', ∃ c : K, g e - e = w + c • f) →
      ((∀ c : K, ∃ g ∈ A ⊔ A', ∀ v, g v = v + (c * F v e) • e) ∨
        ∃ q : V → K,
          (∀ (c : K) (u : V), u ∈ Submodule.span K {e, f, x, x'} → q (c • u) = c ^ 2 * q u) ∧
          (∀ u u' : V, u ∈ Submodule.span K {e, f, x, x'} →
            u' ∈ Submodule.span K {e, f, x, x'} → q (u + u') = q u + q u' + F u u') ∧
          q e = 0 ∧ q f = 0 ∧ (∀ g ∈ A, q (g f) = q f) ∧ (∀ g ∈ A', q (g e) = q e))

@[expose] def BlockQ {K V : Type} [Field K] [AddCommGroup V] [Module K V]
    (F : LinearMap.BilinForm K V) (H : Subgroup (V ≃ₗ[K] V)) (e f : V) : Prop :=
  ∀ x x' : V, F x x' = 1 → F x e = 0 → F x f = 0 → F x' e = 0 → F x' f = 0 →
    ∃ q : V → K,
      (∀ (c : K) (u : V), u ∈ Submodule.span K {e, f, x, x'} → q (c • u) = c ^ 2 * q u) ∧
      (∀ u u' : V, u ∈ Submodule.span K {e, f, x, x'} → u' ∈ Submodule.span K {e, f, x, x'} →
        q (u + u') = q u + q u' + F u u') ∧
      q e = 0 ∧ q f = 0 ∧
      (∀ g ∈ H ⊓ pointRadSubgroup F e, g f - f ∈ Submodule.span K {e, x, x'} → q (g f) = q f) ∧
      (∀ g ∈ H ⊓ pointRadSubgroup F f, g e - e ∈ Submodule.span K {f, x, x'} → q (g e) = q e)

end CFSG.RankThree.GF2n.Stroth80.Classify
