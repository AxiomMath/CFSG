module

public import CFSG.Timmesfeld.Bridge.Asc72Basic

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity

variable {G : Type*} [Group G]

@[expose] def commSet (D : Set G) (d : G) : Set G := {e | e ∈ D ∧ Commute e d ∧ e ≠ d}

@[expose] def orbitIn (D : Set G) (d e : G) : Set G :=
  {f | ∃ g ∈ Subgroup.closure (commSet D d), f = g * e * g⁻¹}

@[expose] def IsMaxOrbit (D : Set G) (d : G) (E : Set G) : Prop :=
  ∃ e ∈ commSet D d, E = orbitIn D d e ∧ ∀ e' ∈ commSet D d, (orbitIn D d e').ncard ≤ E.ncard

@[expose] def normSet (D E : Set G) : Set G := {f | f ∈ D ∧ f ∈ Subgroup.normalizer E}

@[expose] def IsMaxBlock (D F : Set G) : Prop :=
  F.Nonempty ∧ F ⊆ D ∧ F ≠ D ∧ MulAction.IsBlock (ConjAct G) F ∧
    ∀ L : Set G, F ⊆ L → L ⊆ D → L ≠ D → MulAction.IsBlock (ConjAct G) L → L = F

@[expose] def rootGen (D : Set G) (d x : G) : Subgroup G :=
  Subgroup.closure (insert x (rootSet D d))

@[expose] def qd (D : Set G) (d : G) : Subgroup G :=
  Subgroup.closure {g | ∃ a ∈ rootSet D d, ∃ b ∈ rootSet D d, a * b ∉ D ∧ g = a * b}

@[expose] def CommonNeighbourStmt : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (D : Set G), Asc72.Setup G D →
    (∀ a ∈ D, ∀ b ∈ D, Reach D a b) → (∃ u ∈ D, ∃ v ∈ D, u ≠ v ∧ Commute u v ∧ u * v ∈ D) →
    ∀ d ∈ D, ∀ x ∈ D, ¬ Commute d x → ∃ e ∈ D, Commute e d ∧ Commute e x

end CFSG.Timmesfeld.Bridge
