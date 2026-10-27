module

public import CFSG.Milestones.ASVolI.H1
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

@[expose] def IsMaximalIn {G : Type*} [Group G] (X L : Subgroup G) : Prop :=
  X < L ∧ ∀ Y : Subgroup G, X ≤ Y → Y ≤ L → Y = X ∨ Y = L

@[expose] def IsIntDirect {G : Type*} [Group G] (N X Z : Subgroup G) : Prop :=
  X ≤ N ∧ Z ≤ N ∧ (∀ x ∈ X, ∀ z ∈ Z, x * z = z * x) ∧ X ⊓ Z = ⊥ ∧ X ⊔ Z = N

@[expose] def IsExtHatOf {X : Type*} [Group X] (C E : Subgroup X) (S : Type) [Group S] : Prop :=
  E ≤ C ∧ ∃ (Q : Type) (_ : Group Q) (f : ↥C →* Q), Function.Surjective f ∧
    f.ker = E.subgroupOf C ∧ IsHat Q S

@[expose] def IsFaithIrr12 {G : Type*} [Group G] {V : Type*} [CommGroup V] (ρ : G →* MulAut V) :
    Prop :=
  (∀ v : V, v ^ 2 = 1) ∧ Nat.card V = 2 ^ 12 ∧ Function.Injective ρ ∧ IsIrredOn ρ.range ⊤

@[expose] def kSmul {V : Type*} [CommGroup V] {K : Type*} [Field K]
    (ι : K →+* AddMonoid.End (Additive V)) (c : K) (v : V) : V :=
  Additive.toMul (ι c (Additive.ofMul v))

@[expose] def kLine {V : Type*} [CommGroup V] {K : Type*} [Field K]
    (ι : K →+* AddMonoid.End (Additive V)) (v : V) : Subgroup V :=
  Subgroup.closure {x | ∃ c : K, x = kSmul ι c v}

@[expose] def IsUnitaryForm {V : Type*} [CommGroup V] {K : Type*} [Field K]
    (ι : K →+* AddMonoid.End (Additive V)) (f : V → V → K) : Prop :=
  (∀ u u' v : V, f (u * u') v = f u v + f u' v) ∧ (∀ u v v' : V, f u (v * v') = f u v + f u v') ∧
  (∀ (c : K) (u v : V), f (kSmul ι c u) v = c * f u v) ∧
  (∀ (c : K) (u v : V), f u (kSmul ι c v) = c ^ 2 * f u v) ∧
  (∀ u v : V, f v u = f u v ^ 2) ∧ (∀ u : V, u ≠ 1 → ∃ v : V, f u v ≠ 0)

@[expose] def IsIsoPoint {V : Type*} [CommGroup V] {K : Type*} [Field K]
    (ι : K →+* AddMonoid.End (Additive V)) (f : V → V → K) (P : Subgroup V) : Prop :=
  ∃ v : V, v ≠ 1 ∧ f v v = 0 ∧ P = kLine ι v

@[expose] def IsQuadFormOn {V : Type*} [CommGroup V] (q : V → ZMod 2) : Prop :=
  q 1 = 0 ∧ ∀ x x' y : V,
    q (x * x' * y) + q (x * x') + q y = (q (x * y) + q x + q y) + (q (x' * y) + q x' + q y)

@[expose] def ptStab {G : Type*} [Group G] {V : Type*} [CommGroup V] (ρ : G →* MulAut V)
    (X : Subgroup G) (P : Subgroup V) : Subgroup G :=
  X ⊓ (stabSub P).comap ρ

@[expose] def cenIn {G : Type*} [Group G] {V : Type*} [CommGroup V] (ρ : G →* MulAut V)
    (X : Subgroup G) (W : Subgroup V) : Subgroup G :=
  X ⊓ (centSub W).comap ρ

@[expose] def IsConjPt {G : Type*} [Group G] {V : Type*} [CommGroup V] (ρ : G →* MulAut V)
    (X : Subgroup G) (P P' : Subgroup V) : Prop :=
  ∃ g ∈ X, P.map (ρ g).toMonoidHom = P'

end CFSG.ASVolI.ChH
