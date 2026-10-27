module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Quasithin.Background.Basic

public section

namespace CFSG.Quasithin

open CFSG.Open

variable {G : Type*} [Group G]

@[expose] def IsOrdMaximal (T M : Subgroup G) : Prop :=
  InM T M ∧ ∀ M' : Subgroup G, InM T M' → OrdLE T M M' → M' = M

@[expose] def IsMf (T Mc M : Subgroup G) : Prop :=
  IsOrdMaximal T M ∧ M ≠ Mc ∧ ∀ M' : Subgroup G, InM T M' → M' ≠ Mc → OrdLE T M' M

section Quadratic

variable {V : Type*} [Group V]

@[expose] def quadPolar (q : V → ZMod 2) (x y : V) : ZMod 2 := q (x * y) + q x + q y

@[expose] def IsQuadraticFormOn (q : V → ZMod 2) : Prop :=
  q 1 = 0 ∧ (∀ x y z : V, quadPolar q (x * y) z = quadPolar q x z + quadPolar q y z) ∧
    ∀ x y z : V, quadPolar q x (y * z) = quadPolar q x y + quadPolar q x z

@[expose] def IsNondegQuadratic (q : V → ZMod 2) : Prop :=
  ∀ x : V, (∀ y : V, quadPolar q x y = 0) → x = 1

@[expose] def IsPlusType (q : V → ZMod 2) : Prop :=
  ∃ W : Subgroup V, Nat.card W = 4 ∧ ∀ w ∈ W, q w = 0

@[expose] def orthogonalGroupOf (q : V → ZMod 2) : Subgroup (MulAut V) where
  carrier := {g | ∀ v : V, q (g v) = q v}
  one_mem' := fun _ => rfl
  mul_mem' := fun {a b} ha hb v => by
    change q (a (b v)) = q v
    rw [ha, hb]
  inv_mem' := fun {a} ha v => by
    have := ha (a⁻¹ v)
    simpa using this.symm

end Quadratic

@[expose] def IsOFourPlusAction (M V : Subgroup G) : Prop :=
  Nat.card V = 16 ∧ ∃ q : V → ZMod 2, IsQuadraticFormOn q ∧ IsNondegQuadratic q ∧
    IsPlusType q ∧ autOn M V = orthogonalGroupOf q

@[expose] def SixModels (G : Type) [Group G] : Prop :=
  Nonempty (G ≃* quasithinJ2) ∨ Nonempty (G ≃* quasithinJ3) ∨
    Nonempty (G ≃* quasithinTrialityD4Two) ∨ Nonempty (G ≃* quasithinTits) ∨
    Nonempty (G ≃* PSU3 3 1) ∨ Nonempty (G ≃* quasithinM12)

end CFSG.Quasithin
