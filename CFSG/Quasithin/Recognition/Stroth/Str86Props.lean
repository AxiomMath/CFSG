module

public import CFSG.Quasithin.Recognition.Stroth.F112Tree
public import CFSG.Quasithin.Recognition.Stroth.BenderH7

public section

namespace CFSG.Quasithin.Stroth

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.F112R
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def f112CosetSMul {X : Type} [Group X] {A B : Subgroup X} (g : ↥(A ⊔ B))
    (v : CosetGeom (A ⊔ B) A B) : CosetGeom (A ⊔ B) A B :=
  g • v

@[simp] theorem f112CosetSMul_eq_smul {X : Type} [Group X] {A B : Subgroup X} (g : ↥(A ⊔ B))
    (v : CosetGeom (A ⊔ B) A B) : f112CosetSMul g v = g • v := rfl

@[expose] def u3X1 (L1 L2 S : Subgroup G) : Subgroup G :=
  conjClosure (Z2 L1 L2 S ⊓ Q1 L1 L2 S) L1

@[expose] def Str86ZNotLe : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → bigB L1 L2 S ≤ Subgroup.normalizer (S : Set G) →
    VU3Big L1 → VBig L2 → VL2 L2 →
    L1 ⊔ Q1 L1 L2 S ≤ Subgroup.centralizer (Z1 L1 L2 S : Set G) →
      ¬ Z2 L1 L2 S ≤ Q1 L1 L2 S

@[expose] def Str86PathFix : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (L1 L2 S : Subgroup G),
    F112Hyp L1 L2 S → VU3Big L1 → VBig L2 → VL2 L2 →
      let c := f112Completion L1 L2 S
      ∀ p : GPath c.graph 5, p.NoBack →
      ∀ g : ↥(c.φ1.range ⊔ c.φ2.range),
        (∀ i, i ≤ 5 → f112CosetSMul g (p i) = p i) →
          (∃ k : ℕ, orderOf g = 2 ^ k) → g = 1

@[expose] def Str86NF (Lj Qj Zj : Subgroup G) : Prop :=
  ∀ g : G, (∃ n : ℕ, orderOf g = 2 ^ n) → g ∈ Subgroup.normalizer (Lj : Set G) →
    g ∈ Subgroup.normalizer (Qj : Set G) → (∀ l ∈ Lj, g * l * g⁻¹ * l⁻¹ ∈ Qj) →
      (∀ x ∈ Qj, g * x * g⁻¹ * x⁻¹ ∈ Zj) ∧ ∀ z ∈ Zj, g * z = z * g

structure Str86Shape (L1 L2 S : Subgroup G) (k : ℕ) : Prop where
  l2 : IsL2Quot (2 * k) (oTwoQuot ↥L2)
  card_q1 : Nat.card (Q1 L1 L2 S) = (2 ^ k) ^ 7
  card_q2 : Nat.card (Q2 L1 L2 S) = (2 ^ k) ^ 8
  card_s : Nat.card S = (2 ^ k) ^ 10
  q1q2 : Q1 L1 L2 S ⊔ Q2 L1 L2 S = S
  nf1 : Str86NF L1 (Q1 L1 L2 S) (Z1 L1 L2 S)
  nf2 : Str86NF L2 (Q2 L1 L2 S) (Z2 L1 L2 S)
  bprime : ∀ g ∈ L2 ⊔ bigB L1 L2 S, g ∉ bigB L1 L2 S →
    ∀ h ∈ L1 ⊔ bigB L1 L2 S, h ∉ bigB L1 L2 S →
      (MulAut.conj g • Q1 L1 L2 S) ⊓ Q2 L1 L2 S ⊓ Q1 L1 L2 S ⊓
        (MulAut.conj h • Q2 L1 L2 S) = ⊥

end CFSG.Quasithin.Stroth
