module

public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecB.L32

abbrev Γ : Type := Matrix.SpecialLinearGroup (Fin 3) (ZMod 2)

@[expose] def ent (g : Γ) (i j : Fin 3) : ZMod 2 := (g : Matrix (Fin 3) (Fin 3) (ZMod 2)) i j

@[expose] def IsU (g : Γ) : Prop := ent g 1 0 = 0 ∧ ent g 2 0 = 0 ∧ ent g 2 1 = 0

@[expose] def IsPa (g : Γ) : Prop := ent g 1 0 = 0 ∧ ent g 2 0 = 0

@[expose] def IsPb (g : Γ) : Prop := ent g 2 0 = 0 ∧ ent g 2 1 = 0

@[expose] def IsEa (g : Γ) : Prop :=
  IsPa g ∧ ent g 1 1 = 1 ∧ ent g 1 2 = 0 ∧ ent g 2 1 = 0 ∧ ent g 2 2 = 1

@[expose] def IsEb (g : Γ) : Prop :=
  IsPb g ∧ ent g 0 0 = 1 ∧ ent g 0 1 = 0 ∧ ent g 1 0 = 0 ∧ ent g 1 1 = 1

@[expose] def IsKa (g : Γ) : Prop :=
  IsPa g ∧ ((ent g 1 1 = 1 ∧ ent g 1 2 = 0 ∧ ent g 2 1 = 0 ∧ ent g 2 2 = 1) ∨
    (ent g 1 1 = 0 ∧ ent g 1 2 = 1 ∧ ent g 2 1 = 1 ∧ ent g 2 2 = 1) ∨
    (ent g 1 1 = 1 ∧ ent g 1 2 = 1 ∧ ent g 2 1 = 1 ∧ ent g 2 2 = 0))

@[expose] def IsKb (g : Γ) : Prop :=
  IsPb g ∧ ((ent g 0 0 = 1 ∧ ent g 0 1 = 0 ∧ ent g 1 0 = 0 ∧ ent g 1 1 = 1) ∨
    (ent g 0 0 = 0 ∧ ent g 0 1 = 1 ∧ ent g 1 0 = 1 ∧ ent g 1 1 = 1) ∨
    (ent g 0 0 = 1 ∧ ent g 0 1 = 1 ∧ ent g 1 0 = 1 ∧ ent g 1 1 = 0))

instance : DecidablePred IsU := fun g => by unfold IsU ent; infer_instance
instance : DecidablePred IsPa := fun g => by unfold IsPa ent; infer_instance
instance : DecidablePred IsPb := fun g => by unfold IsPb ent; infer_instance
instance : DecidablePred IsEa := fun g => by unfold IsEa IsPa ent; infer_instance
instance : DecidablePred IsEb := fun g => by unfold IsEb IsPb ent; infer_instance
instance : DecidablePred IsKa := fun g => by unfold IsKa IsPa ent; infer_instance
instance : DecidablePred IsKb := fun g => by unfold IsKb IsPb ent; infer_instance

theorem isU_one : IsU 1 := by unfold IsU ent; decide
theorem isU_mul : ∀ a b : Γ, IsU a → IsU b → IsU (a * b) := by unfold IsU ent; decide +kernel
theorem isU_inv : ∀ a : Γ, IsU a → IsU a⁻¹ := by unfold IsU ent; decide +kernel
theorem isPa_one : IsPa 1 := by unfold IsPa ent; decide
theorem isPa_mul : ∀ a b : Γ, IsPa a → IsPa b → IsPa (a * b) := by
  unfold IsPa ent; decide +kernel
theorem isPa_inv : ∀ a : Γ, IsPa a → IsPa a⁻¹ := by unfold IsPa ent; decide +kernel
theorem isPb_one : IsPb 1 := by unfold IsPb ent; decide
theorem isPb_mul : ∀ a b : Γ, IsPb a → IsPb b → IsPb (a * b) := by
  unfold IsPb ent; decide +kernel
theorem isPb_inv : ∀ a : Γ, IsPb a → IsPb a⁻¹ := by unfold IsPb ent; decide +kernel
theorem isEa_one : IsEa 1 := by unfold IsEa IsPa ent; decide
theorem isEa_mul : ∀ a b : Γ, IsEa a → IsEa b → IsEa (a * b) := by
  unfold IsEa IsPa ent; decide +kernel
theorem isEa_inv : ∀ a : Γ, IsEa a → IsEa a⁻¹ := by unfold IsEa IsPa ent; decide +kernel
theorem isEb_one : IsEb 1 := by unfold IsEb IsPb ent; decide
theorem isEb_mul : ∀ a b : Γ, IsEb a → IsEb b → IsEb (a * b) := by
  unfold IsEb IsPb ent; decide +kernel
theorem isEb_inv : ∀ a : Γ, IsEb a → IsEb a⁻¹ := by unfold IsEb IsPb ent; decide +kernel
theorem isKa_one : IsKa 1 := by unfold IsKa IsPa ent; decide
theorem isKa_mul : ∀ a b : Γ, IsKa a → IsKa b → IsKa (a * b) := by
  unfold IsKa IsPa ent; decide +kernel
theorem isKa_inv : ∀ a : Γ, IsKa a → IsKa a⁻¹ := by unfold IsKa IsPa ent; decide +kernel
theorem isKb_one : IsKb 1 := by unfold IsKb IsPb ent; decide
theorem isKb_mul : ∀ a b : Γ, IsKb a → IsKb b → IsKb (a * b) := by
  unfold IsKb IsPb ent; decide +kernel
theorem isKb_inv : ∀ a : Γ, IsKb a → IsKb a⁻¹ := by unfold IsKb IsPb ent; decide +kernel

@[expose] def U3 : Subgroup Γ where
  carrier := {g | IsU g}
  one_mem' := isU_one
  mul_mem' := fun {a b} => isU_mul a b
  inv_mem' := fun {a} => isU_inv a

@[expose] def Pa : Subgroup Γ where
  carrier := {g | IsPa g}
  one_mem' := isPa_one
  mul_mem' := fun {a b} => isPa_mul a b
  inv_mem' := fun {a} => isPa_inv a

@[expose] def Pb : Subgroup Γ where
  carrier := {g | IsPb g}
  one_mem' := isPb_one
  mul_mem' := fun {a b} => isPb_mul a b
  inv_mem' := fun {a} => isPb_inv a

@[expose] def Ea : Subgroup Γ where
  carrier := {g | IsEa g}
  one_mem' := isEa_one
  mul_mem' := fun {a b} => isEa_mul a b
  inv_mem' := fun {a} => isEa_inv a

@[expose] def Eb : Subgroup Γ where
  carrier := {g | IsEb g}
  one_mem' := isEb_one
  mul_mem' := fun {a b} => isEb_mul a b
  inv_mem' := fun {a} => isEb_inv a

@[expose] def Ka : Subgroup Γ where
  carrier := {g | IsKa g}
  one_mem' := isKa_one
  mul_mem' := fun {a b} => isKa_mul a b
  inv_mem' := fun {a} => isKa_inv a

@[expose] def Kb : Subgroup Γ where
  carrier := {g | IsKb g}
  one_mem' := isKb_one
  mul_mem' := fun {a b} => isKb_mul a b
  inv_mem' := fun {a} => isKb_inv a

theorem mem_U3 {g : Γ} : g ∈ U3 ↔ IsU g := Iff.rfl
theorem mem_Pa {g : Γ} : g ∈ Pa ↔ IsPa g := Iff.rfl
theorem mem_Pb {g : Γ} : g ∈ Pb ↔ IsPb g := Iff.rfl
theorem mem_Ea {g : Γ} : g ∈ Ea ↔ IsEa g := Iff.rfl
theorem mem_Eb {g : Γ} : g ∈ Eb ↔ IsEb g := Iff.rfl
theorem mem_Ka {g : Γ} : g ∈ Ka ↔ IsKa g := Iff.rfl
theorem mem_Kb {g : Γ} : g ∈ Kb ↔ IsKb g := Iff.rfl

instance : DecidablePred (· ∈ U3) := fun g => (inferInstance : Decidable (IsU g))
instance : DecidablePred (· ∈ Pa) := fun g => (inferInstance : Decidable (IsPa g))
instance : DecidablePred (· ∈ Pb) := fun g => (inferInstance : Decidable (IsPb g))
instance : DecidablePred (· ∈ Ea) := fun g => (inferInstance : Decidable (IsEa g))
instance : DecidablePred (· ∈ Eb) := fun g => (inferInstance : Decidable (IsEb g))
instance : DecidablePred (· ∈ Ka) := fun g => (inferInstance : Decidable (IsKa g))
instance : DecidablePred (· ∈ Kb) := fun g => (inferInstance : Decidable (IsKb g))

end CFSG.Quasithin.Vol2.Ch10.SecB.L32
