module

public import CFSG.LocalAnalysis.StandardType.GGHdRo7A3Defs

public section

namespace CFSG.StandardType.HdRo7A3.Small

open CFSG.StandardType.HdRo7C CFSG.StandardType.HdRo7SU CFSG.StandardType.HdRo7A3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

@[expose] def a9E (i j : Fin 9) : Fin 9 → ZMod 3 := Pi.single i 1 - Pi.single j 1

@[expose] def a9Const (u : Fin 9 → ZMod 3) : Prop := ∀ i, u i = u 0

instance (u : Fin 9 → ZMod 3) : Decidable (a9Const u) :=
  inferInstanceAs (Decidable (∀ i, u i = u 0))

@[expose] def a9Act (hh f : Fin 9 → ZMod 3) (d : ZMod 3) (v : (Fin 9 → ZMod 3) × ZMod 3) :
    (Fin 9 → ZMod 3) × ZMod 3 :=
  (v.1 - (∑ i, f i * v.1 i + v.2 * d) • hh, v.2 - (∑ i, f i * v.1 i + v.2 * d))

@[expose] def a9Perm (σ : Equiv.Perm (Fin 9)) (v : (Fin 9 → ZMod 3) × ZMod 3) :
    (Fin 9 → ZMod 3) × ZMod 3 :=
  (fun i => v.1 (σ.symm i), v.2)

@[expose] def A9Lift {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : (Fin 9 → ZMod 3) →ₗ[ZMod 3] V) (z : V) (g : V ≃ₗ[ZMod 3] V)
    (ρ : (Fin 9 → ZMod 3) × ZMod 3 → (Fin 9 → ZMod 3) × ZMod 3) : Prop :=
  ∀ u ∈ a3Aug 3 9, ∀ c : ZMod 3, g (θ u + c • z) = θ (ρ (u, c)).1 + (ρ (u, c)).2 • z

@[expose] def A9Real {V : Type} [AddCommGroup V] [Module (ZMod 3) V]
    (θ : (Fin 9 → ZMod 3) →ₗ[ZMod 3] V) (z : V) (hh f : Fin 9 → ZMod 3) (d : ZMod 3)
    (r : V ≃ₗ[ZMod 3] V) : Prop :=
  A9Lift θ z r (a9Act hh f d)

@[expose] def A9Wit (ρ : (Fin 9 → ZMod 3) × ZMod 3 → (Fin 9 → ZMod 3) × ZMod 3) (a b : Fin 9) :
    Prop :=
  (ρ (0, 1)).2 = 1 ∧ a9Const (ρ (0, 1)).1 ∧ ∑ i, (ρ (a9E a b, 0)).1 i = 0 ∧
    ((ρ (a9E a b, 0)).2 ≠ 0 ∨
      ∀ k l : Fin 9, ∀ s : ZMod 3, s ≠ 0 → ¬ a9Const ((ρ (a9E a b, 0)).1 - s • a9E k l))

instance (ρ : (Fin 9 → ZMod 3) × ZMod 3 → (Fin 9 → ZMod 3) × ZMod 3) (a b : Fin 9) :
    Decidable (A9Wit ρ a b) := by
  unfold A9Wit; infer_instance

@[expose] def a9T : Fin 9 → ZMod 3 := ![1, 1, 1, 0, 0, 0, 0, 0, 0]

@[expose] def a9Tn : Fin 9 → ZMod 3 := ![2, 2, 2, 0, 0, 0, 0, 0, 0]

@[expose] def a9C : Fin 9 → ZMod 3 := ![0, 0, 0, 1, 1, 1, 2, 2, 2]

inductive A9Class
  | cz
  | ep
  | em
  | bpm
  | bmp
  | cp
  | cm
  | d
  | e
  | f

@[expose] def a9H : A9Class → Fin 9 → ZMod 3
  | .cz => 0
  | .ep => a9T
  | .em => a9Tn
  | .bpm => a9T
  | .bmp => a9Tn
  | .cp => a9C
  | .cm => a9C
  | .d => ![1, 2, 0, 0, 0, 0, 0, 0, 0]
  | .e => ![1, 1, 1, 1, 2, 2, 2, 2, 0]
  | .f => ![1, 1, 2, 2, 0, 0, 0, 0, 0]

@[expose] def a9F : A9Class → Fin 9 → ZMod 3
  | .cz => 0
  | .ep => a9T
  | .em => a9Tn
  | .bpm => a9Tn
  | .bmp => a9T
  | .cp => a9C
  | .cm => ![0, 0, 0, 2, 2, 2, 1, 1, 1]
  | .d => ![2, 1, 0, 0, 0, 0, 0, 0, 0]
  | .e => ![2, 2, 2, 2, 1, 1, 1, 1, 0]
  | .f => ![1, 1, 2, 2, 0, 0, 0, 0, 0]

@[expose] def a9D : A9Class → ZMod 3
  | .cz => 2
  | .ep => 2
  | .em => 2
  | .bpm => 2
  | .bmp => 2
  | .cp => 2
  | .cm => 2
  | .d => 1
  | .e => 1
  | .f => 1

@[expose] def A9RealLeaf : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V] (θ : (Fin 9 → ZMod 3) →ₗ[ZMod 3] V) (z : V)
    (H A : Subgroup (V ≃ₗ[ZMod 3] V)), A3LinData 3 9 V θ z H A → θ (fun _ => 1) = 0 →
    ∀ r ∈ H, GGLinRefl r → r z ≠ z →
    ∃ (hh f : Fin 9 → ZMod 3) (d : ZMod 3), hh ∈ a3Aug 3 9 ∧ ∑ i, f i = 0 ∧
      ∑ i, f i * hh i + d = 2 ∧ (∀ i j, f i = f j ↔ hh i = hh j) ∧ A9Real θ z hh f d r

@[expose] def A9NormLeaf : Prop :=
  ∀ (hh f : Fin 9 → ZMod 3) (d : ZMod 3), hh ∈ a3Aug 3 9 → ∑ i, f i = 0 →
    ∑ i, f i * hh i + d = 2 → d ≠ 0 → (∀ i j, f i = f j ↔ hh i = hh j) →
    ∃ (σ : Equiv.Perm (Fin 9)) (X : A9Class),
      a9Const ((fun i => hh (σ.symm i)) - a9H X) ∧ a9Const ((fun i => f (σ.symm i)) - a9F X) ∧
        d = a9D X

@[expose] def A9WitLeaf : Prop :=
  A3NormalizerLeaf → ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V]
    (θ : (Fin 9 → ZMod 3) →ₗ[ZMod 3] V) (z : V) (H A : Subgroup (V ≃ₗ[ZMod 3] V)),
    A3LinData 3 9 V θ z H A → θ (fun _ => 1) = 0 →
    ∀ g ∈ A, ∀ (ρ : (Fin 9 → ZMod 3) × ZMod 3 → (Fin 9 → ZMod 3) × ZMod 3), A9Lift θ z g ρ →
      ∀ a b : Fin 9, ¬ A9Wit ρ a b

@[expose] def A9E8Leaf : Prop :=
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod 3) V] (θ : (Fin 9 → ZMod 3) →ₗ[ZMod 3] V) (z : V),
    A3Frame 3 9 θ z → θ (fun _ => 1) = 0 → ∀ r : V ≃ₗ[ZMod 3] V, A9Real θ z a9T a9T 2 r →
    ZS.LinWeyl 3 (Subgroup.closure ({a | A3P 3 9 θ z a} ∪ {r}))

end CFSG.StandardType.HdRo7A3.Small
