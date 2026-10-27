module

public import CFSG.Quasithin.Background.F7Geometry
public import CFSG.Quasithin.Recognition.GoldschmidtFan86TutteSubdiv

public section

namespace CFSG.Quasithin.F112Crit

variable {G : Type} [Group G]

open CosetGeom (graph stab ballStab nbrs vtype)

variable {G₀ G₁ G₂ : Subgroup G}

@[expose] def IsEdgeHall (μ δ : CosetGeom G₀ G₁ G₂) (X : Subgroup G) : Prop :=
  X ≤ stab μ ⊓ stab δ ∧ Odd (Nat.card X) ∧ ∃ k : ℕ, X.relIndex (stab μ ⊓ stab δ) = 2 ^ k

@[expose] def torusComp (X : Subgroup G) (δ : CosetGeom G₀ G₁ G₂) : Set (CosetGeom G₀ G₁ G₂) :=
  {v | Relation.ReflTransGen (fun a b => X ≤ stab a ∧ X ≤ stab b ∧ (graph G₀ G₁ G₂).Adj a b) δ v}

structure TorusGraph (X : Subgroup G) (δ : CosetGeom G₀ G₁ G₂) : Prop where
  small_le : ∀ y ∈ torusComp X δ, vtype y = true → X ≤ ballStab 1 y
  subdiv : Fan86.Tutte.SubdivCubic (graph G₀ G₁ G₂) (torusComp X δ) (fun v => vtype v = true)
  trans : ∀ y ∈ torusComp X δ, vtype y = true → ∀ y' ∈ torusComp X δ, vtype y' = true →
    ∃ n : ↥G₀, (n : G) ∈ Subgroup.normalizer (X : Set G) ∧ n • y = y'
  loc : ∀ y ∈ torusComp X δ, vtype y = true → ∀ e e' : CosetGeom G₀ G₁ G₂,
    (graph G₀ G₁ G₂).Adj y e → (graph G₀ G₁ G₂).Adj y e' →
    ∃ n : ↥G₀, (n : G) ∈ Subgroup.normalizer (X : Set G) ∧ n • y = y ∧ n • e = e'

end CFSG.Quasithin.F112Crit

end
