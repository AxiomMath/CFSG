module

public import CFSG.Quasithin.Background.H16TwoM22PfA
public import CFSG.Quasithin.Background.RonanH143Vocab

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf

structure PG where
  t : Fin 16
  j : Fin 8

namespace PG

instance : DecidableEq PG := fun x y =>
  if h : x.t = y.t ∧ x.j = y.j then
    isTrue (by cases x; cases y; simp_all)
  else
    isFalse (fun e => h (by cases e; exact ⟨rfl, rfl⟩))

@[expose] def equiv : PG ≃ Fin 16 × Fin 8 where
  toFun x := (x.t, x.j)
  invFun p := ⟨p.1, p.2⟩
  left_inv x := by cases x; rfl
  right_inv p := by cases p; rfl

instance : Fintype PG := Fintype.ofEquiv _ equiv.symm

instance : Mul PG := ⟨fun x y => ⟨xorF x.t (ctF x.j y.t), mtF x.j y.j⟩⟩

instance : One PG := ⟨⟨0, 0⟩⟩

instance : Inv PG := ⟨fun x => ⟨ctF (ivF x.j) x.t, ivF x.j⟩⟩

theorem mul_def (x y : PG) : x * y = ⟨xorF x.t (ctF x.j y.t), mtF x.j y.j⟩ := rfl

theorem one_def : (1 : PG) = ⟨0, 0⟩ := rfl

@[ext] theorem ext' {x y : PG} (h1 : x.t = y.t) (h2 : x.j = y.j) : x = y := by
  cases x; cases y; simp_all

@[expose] def toPerm (x : PG) : P24 := koPerm x.t * dPerm x.j

theorem toPerm_mul (x y : PG) : toPerm (x * y) = toPerm x * toPerm y := by
  unfold toPerm
  rw [mul_def]
  simp only
  rw [← koPerm_mul, ← dPerm_mul]
  have h := dPerm_mul_koPerm x.j y.t
  calc koPerm x.t * koPerm (ctF x.j y.t) * (dPerm x.j * dPerm y.j)
      = koPerm x.t * (koPerm (ctF x.j y.t) * dPerm x.j) * dPerm y.j := by group
    _ = koPerm x.t * (dPerm x.j * koPerm y.t) * dPerm y.j := by rw [h]
    _ = koPerm x.t * dPerm x.j * (koPerm y.t * dPerm y.j) := by group

theorem toPerm_one : toPerm (1 : PG) = 1 := by
  unfold toPerm
  rw [one_def]
  simp only
  rw [koPerm_zero, dPerm_zero, mul_one]

theorem toPerm_injective : Function.Injective toPerm := by
  intro x y h
  have h' : koPerm x.t * dPerm x.j = koPerm y.t * dPerm y.j := h
  have hj : x.j = y.j := dPerm_hexad x.j y.j fun i _ hi8 => by
    have := congrArg (fun g => g i) h'
    simp only [Equiv.Perm.mul_apply] at this
    rwa [koPerm_apply_of_lt _ _ (dPerm_lt x.j i hi8),
      koPerm_apply_of_lt _ _ (dPerm_lt y.j i hi8)] at this
  have ht : x.t = y.t := by
    have h2 : koPerm x.t = koPerm y.t := by
      rw [hj] at h'
      exact mul_right_cancel h'
    have e1 := koPerm_eight x.t
    rw [h2, koPerm_eight y.t] at e1
    exact Fin.ext (by omega)
  exact ext' ht hj

theorem mul_inv_cancel_PG : ∀ x : PG, x * x⁻¹ = 1 := by decide +kernel

theorem toPerm_inv (x : PG) : toPerm x⁻¹ = (toPerm x)⁻¹ := by
  have h := toPerm_mul x x⁻¹
  rw [mul_inv_cancel_PG, toPerm_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

instance instGroup : Group PG :=
  Group.ofLeftAxioms
    (fun a b c => toPerm_injective (by rw [toPerm_mul, toPerm_mul, toPerm_mul, toPerm_mul, mul_assoc]))
    (fun a => toPerm_injective (by rw [toPerm_mul, toPerm_one, one_mul]))
    (fun a => toPerm_injective (by rw [toPerm_mul, toPerm_inv, toPerm_one, inv_mul_cancel]))

@[expose] def toPermHom : PG →* P24 where
  toFun := toPerm
  map_one' := toPerm_one
  map_mul' := toPerm_mul

theorem toPerm_mem_PO (x : PG) : toPerm x ∈ PO := ⟨x.t, x.j, rfl⟩

theorem range_toPermHom : toPermHom.range = PO := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact toPerm_mem_PO x
  · rintro ⟨t, j, rfl⟩
    exact ⟨⟨t, j⟩, rfl⟩

theorem card_PG : Nat.card PG = 128 := by
  rw [Nat.card_congr equiv, Nat.card_eq_fintype_card, Fintype.card_prod, Fintype.card_fin,
    Fintype.card_fin]

end PG

end CFSG.Quasithin.RonanH143
