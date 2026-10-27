module

public import Mathlib.GroupTheory.SpecificGroups.Dihedral

public section

namespace CFSG.Quasithin.RuType

structure SD16C where
  a : ZMod 8
  e : ZMod 2
deriving DecidableEq

namespace SD16C

@[expose] def equivProd : SD16C ≃ ZMod 8 × ZMod 2 where
  toFun p := (p.a, p.e)
  invFun p := ⟨p.1, p.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

instance : Fintype SD16C := Fintype.ofEquiv _ equivProd.symm

@[expose] def mul (p q : SD16C) : SD16C := ⟨p.a + (if p.e = 0 then q.a else 3 * q.a), p.e + q.e⟩

@[expose] def inv (p : SD16C) : SD16C := ⟨if p.e = 0 then -p.a else -(3 * p.a), p.e⟩

instance : Group SD16C where
  mul := mul
  one := ⟨0, 0⟩
  inv := inv
  mul_assoc := by decide +kernel
  one_mul := by decide +kernel
  mul_one := by decide +kernel
  inv_mul_cancel := by decide +kernel

theorem one_def : (1 : SD16C) = ⟨0, 0⟩ := rfl

@[expose] def c4 : SD16C := ⟨4, 0⟩

@[expose] def f : SD16C := ⟨1, 1⟩

theorem center_cases : ∀ p : SD16C, (∀ q : SD16C, p * q = q * p) → p = 1 ∨ p = c4 := by
  decide +kernel

theorem f_sq : f * f = c4 := by decide +kernel

theorem f_pow_four : f ^ 4 = 1 := by decide +kernel

@[expose] def SBC : Subgroup SD16C where
  carrier := {p | p.a.val % 2 = 0}
  mul_mem' {a b} ha hb := (by decide +kernel : ∀ a b : SD16C, a.a.val % 2 = 0 →
    b.a.val % 2 = 0 → (a * b).a.val % 2 = 0) a b ha hb
  one_mem' := rfl
  inv_mem' {a} ha := (by decide +kernel : ∀ a : SD16C, a.a.val % 2 = 0 →
    a⁻¹.a.val % 2 = 0) a ha

theorem mem_SBC {p : SD16C} : p ∈ SBC ↔ p.a.val % 2 = 0 := Iff.rfl

instance : DecidablePred (· ∈ SBC) := fun _ => decidable_of_iff _ mem_SBC.symm

theorem f_pow_mem_SBC_iff : ∀ k : Fin 4, f ^ k.val ∈ SBC ↔ k.val % 2 = 0 := by decide +kernel

theorem mem_SBC_of_sq : ∀ p : SD16C, p * p = 1 → p ∈ SBC := by decide +kernel

theorem sq_of_mem_SBC : ∀ p : SD16C, p ∈ SBC → p * p = 1 ∨ p * p = c4 := by decide +kernel

theorem c4_mem_SBC : c4 ∈ SBC := by decide +kernel

theorem conj_mem_SBC : ∀ p q : SD16C, q ∈ SBC → p * q * p⁻¹ ∈ SBC := by decide +kernel

theorem mul_f_inv_mem_SBC : ∀ p : SD16C, p ∉ SBC → p * f⁻¹ ∈ SBC := by decide +kernel

theorem SBC_prod_inv : ∀ p : SD16C, p ∈ SBC → ∃ a b : SD16C, a * a = 1 ∧ b * b = 1 ∧ p = a * b := by
  decide +kernel

@[expose] def parity : SD16C →* Multiplicative (ZMod 2) where
  toFun p := Multiplicative.ofAdd ((p.a.val : ℕ) : ZMod 2)
  map_one' := rfl
  map_mul' := by decide +kernel

theorem parity_eq_one_iff : ∀ p : SD16C, parity p = 1 ↔ p ∈ SBC := by decide +kernel

theorem parity_f : parity f = Multiplicative.ofAdd 1 := by decide +kernel

@[expose] def dihedralFun : DihedralGroup 4 → SD16C
  | .r i => ⟨((2 * i.val : ℕ) : ZMod 8), 0⟩
  | .sr i => ⟨((6 * i.val : ℕ) : ZMod 8), 1⟩

theorem dihedralFun_mul : ∀ a b : DihedralGroup 4,
    dihedralFun (a * b) = dihedralFun a * dihedralFun b := by decide +kernel

theorem dihedralFun_injective : Function.Injective dihedralFun := by
  intro a b h
  revert a b
  decide +kernel

theorem dihedralFun_mem : ∀ a : DihedralGroup 4, dihedralFun a ∈ SBC := by decide +kernel

theorem dihedralFun_surj : ∀ p : SD16C, p ∈ SBC → ∃ a : DihedralGroup 4, dihedralFun a = p := by
  decide +kernel

theorem nonempty_SBC_dihedral : Nonempty (SBC ≃* DihedralGroup 4) := by
  let φ : DihedralGroup 4 →* SBC :=
    { toFun := fun a => ⟨dihedralFun a, dihedralFun_mem a⟩
      map_one' := Subtype.ext (by decide +kernel)
      map_mul' := fun a b => Subtype.ext (dihedralFun_mul a b) }
  have hbij : Function.Bijective φ := by
    refine ⟨fun a b h => dihedralFun_injective (congrArg Subtype.val h), fun p => ?_⟩
    obtain ⟨a, ha⟩ := dihedralFun_surj p.val p.2
    exact ⟨a, Subtype.ext ha⟩
  exact ⟨(MulEquiv.ofBijective φ hbij).symm⟩

end SD16C

end CFSG.Quasithin.RuType
