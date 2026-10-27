module

public import CFSG.Monster.GMS.S35

public section

namespace CFSG.Monster.GMS

variable {G : Type*} [Group G]

@[expose] def ThreeCInvolutions (a z₀ : G) : Prop :=
  ∀ b x t : G, IsConj a b → x ∈ typeSet a z₀ b .threeC →
    t ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G) →
      orderOf t = 2 → IsConj z₀ t ∧ IsConj z₀ (b * t) ∧ IsConj z₀ (x * t)

@[expose] def A12InFiveA (a z₀ : G) : Prop :=
  ∀ b x : G, IsConj a b → x ∈ typeSet a z₀ b .fiveA →
    ∃ φ : alternatingGroup (Fin 12) →* G, Function.Injective φ ∧
      (∀ σ, φ σ ∈ Subgroup.centralizer ({b} : Set G) ⊓ Subgroup.centralizer ({x} : Set G)) ∧
      (∀ σ : alternatingGroup (Fin 12),
        (σ : Equiv.Perm (Fin 12)).cycleType = {2, 2} ∨
          (σ : Equiv.Perm (Fin 12)).cycleType = {2, 2, 2, 2, 2, 2} → IsConj a (φ σ)) ∧
      (∀ σ : alternatingGroup (Fin 12),
        (σ : Equiv.Perm (Fin 12)).cycleType = {2, 2, 2, 2} → IsConj z₀ (φ σ))

@[expose] def IsLineTriple (a x y : G) : Prop := IsConj a x ∧ IsConj a y ∧ IsConj a (x * y)

@[expose] def IsEightExt (x y t : G) : Prop :=
  t * t = 1 ∧ t * x = x * t ∧ t * y = y * t ∧ t ≠ 1 ∧ t ≠ x ∧ t ≠ y ∧ t ≠ x * y

open Classical in
@[expose] noncomputable def twoBCount (z₀ x y t : G) : ℕ :=
  ([t, t * x, t * y, t * x * y].filter fun w => decide (IsConj z₀ w)).length

@[expose] def EightGroupLines (a z₀ : G) : Prop :=
  (∀ x y t : G, IsLineTriple a x y → IsEightExt x y t →
    twoBCount z₀ x y t = 1 ∨ twoBCount z₀ x y t = 3 ∨ twoBCount z₀ x y t = 4) ∧
  ∀ x y t x' y' t' : G, IsLineTriple a x y → IsEightExt x y t → IsLineTriple a x' y' →
    IsEightExt x' y' t' → twoBCount z₀ x y t = twoBCount z₀ x' y' t' →
      ∃ g : G, g * x * g⁻¹ = x' ∧ g * y * g⁻¹ = y' ∧
        g * t * g⁻¹ ∈ ({t', t' * x', t' * y', t' * x' * y'} : Set G)

end CFSG.Monster.GMS
