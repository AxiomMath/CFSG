module

public import CFSG.Quasithin.Background.RonanH143Syl

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH143

open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H.Mathieu.H16Pf

structure PG2 where
  t : Fin 16
  j : Fin 8
  ε : Fin 2

namespace PG2

instance : DecidableEq PG2 := fun x y =>
  if h : x.t = y.t ∧ x.j = y.j ∧ x.ε = y.ε then
    isTrue (by cases x; cases y; simp_all)
  else
    isFalse (fun e => h (by cases e; exact ⟨rfl, rfl, rfl⟩))

@[expose] def equiv : PG2 ≃ Fin 16 × Fin 8 × Fin 2 where
  toFun x := (x.t, x.j, x.ε)
  invFun p := ⟨p.1, p.2.1, p.2.2⟩
  left_inv x := by cases x; rfl
  right_inv p := by rcases p with ⟨a, b, c⟩; rfl

instance : Fintype PG2 := Fintype.ofEquiv _ equiv.symm

@[expose] def cj (ε : Fin 2) (t : Fin 16) (j : Fin 8) : Fin 16 := if ε = 1 then eKF t j else t

instance : Mul PG2 := ⟨fun x y => ⟨xorF x.t (ctF x.j (cj x.ε y.t y.j)), mtF x.j y.j, x.ε + y.ε⟩⟩

instance : One PG2 := ⟨⟨0, 0, 0⟩⟩

instance : Inv PG2 := ⟨fun x => ⟨cj x.ε (ctF (ivF x.j) x.t) (ivF x.j), ivF x.j, x.ε⟩⟩

theorem one_def : (1 : PG2) = ⟨0, 0, 0⟩ := rfl

@[ext] theorem ext' {x y : PG2} (h1 : x.t = y.t) (h2 : x.j = y.j) (h3 : x.ε = y.ε) : x = y := by
  cases x; cases y; simp_all

theorem fin2_eq_zero_or_one : ∀ ε : Fin 2, ε = 0 ∨ ε = 1 := by decide

theorem fin2_eq_of_iff : ∀ a b : Fin 2, (a = 0 ↔ b = 0) → a = b := by decide

theorem ePerm_mul_PO (t : Fin 16) (j : Fin 8) :
    ePerm * (koPerm t * dPerm j) = koPerm (eKF t j) * dPerm j * ePerm := by
  have h := ePerm_conj_PO' t j
  rw [ePerm_inv] at h
  rw [← h]
  simp only [mul_assoc, ePerm_sq, mul_one]

theorem ePow_mul_PO (ε : Fin 2) (s : Fin 16) (k : Fin 8) :
    (if ε = 1 then ePerm else 1) * (koPerm s * dPerm k) =
      koPerm (cj ε s k) * dPerm k * (if ε = 1 then ePerm else 1) := by
  rcases fin2_eq_zero_or_one ε with rfl | rfl
  · simp [cj]
  · simp [cj, ePerm_mul_PO]

theorem ePow_mul_ePow (ε δ : Fin 2) :
    (if ε = 1 then ePerm else 1) * (if δ = 1 then ePerm else 1) =
      if ε + δ = 1 then ePerm else 1 := by
  rcases fin2_eq_zero_or_one ε with rfl | rfl <;>
    rcases fin2_eq_zero_or_one δ with rfl | rfl <;> simp [ePerm_sq]

theorem koPerm_dPerm_mul (t : Fin 16) (j : Fin 8) (c : Fin 16) (j' : Fin 8) :
    koPerm t * dPerm j * (koPerm c * dPerm j') =
      koPerm (xorF t (ctF j c)) * dPerm (mtF j j') := by
  rw [← koPerm_mul, ← dPerm_mul]
  have h := dPerm_mul_koPerm j c
  calc koPerm t * dPerm j * (koPerm c * dPerm j')
      = koPerm t * (dPerm j * koPerm c) * dPerm j' := by simp only [mul_assoc]
    _ = koPerm t * (koPerm (ctF j c) * dPerm j) * dPerm j' := by rw [h]
    _ = koPerm t * koPerm (ctF j c) * (dPerm j * dPerm j') := by simp only [mul_assoc]

theorem core_mul (t : Fin 16) (j : Fin 8) (t' : Fin 16) (j' : Fin 8) (c : Fin 16) (a b : P24)
    (hE : a * (koPerm t' * dPerm j') = koPerm c * dPerm j' * a) :
    koPerm t * dPerm j * a * (koPerm t' * dPerm j' * b) =
      koPerm (xorF t (ctF j c)) * dPerm (mtF j j') * (a * b) := by
  have hG := koPerm_dPerm_mul t j c j'
  calc koPerm t * dPerm j * a * (koPerm t' * dPerm j' * b)
      = koPerm t * dPerm j * (a * (koPerm t' * dPerm j')) * b := by simp only [mul_assoc]
    _ = koPerm t * dPerm j * (koPerm c * dPerm j' * a) * b := by rw [hE]
    _ = koPerm t * dPerm j * (koPerm c * dPerm j') * (a * b) := by simp only [mul_assoc]
    _ = koPerm (xorF t (ctF j c)) * dPerm (mtF j j') * (a * b) := by rw [hG]

@[expose] def toPerm (x : PG2) : P24 := koPerm x.t * dPerm x.j * (if x.ε = 1 then ePerm else 1)

theorem toPerm_mul (x y : PG2) : toPerm (x * y) = toPerm x * toPerm y := by
  obtain ⟨t, j, ε⟩ := x
  obtain ⟨t', j', ε'⟩ := y
  have h := core_mul t j t' j' (cj ε t' j') (if ε = 1 then ePerm else 1)
    (if ε' = 1 then ePerm else 1) (ePow_mul_PO ε t' j')
  rw [ePow_mul_ePow] at h
  exact h.symm

theorem toPerm_one : toPerm (1 : PG2) = 1 := by
  rw [one_def]
  simp [toPerm, koPerm_zero, dPerm_zero]

theorem toPerm_mem_PO_iff (x : PG2) : toPerm x ∈ PO ↔ x.ε = 0 := by
  obtain ⟨t, j, ε⟩ := x
  rcases fin2_eq_zero_or_one ε with rfl | rfl
  · have h0 : toPerm ⟨t, j, 0⟩ = koPerm t * dPerm j := by simp [toPerm]
    rw [h0]
    exact ⟨fun _ => rfl, fun _ => ⟨t, j, rfl⟩⟩
  · have h1 : toPerm ⟨t, j, 1⟩ = koPerm t * dPerm j * ePerm := by simp [toPerm]
    rw [h1]
    exact iff_of_false (notMem_PO_mul_ePerm_sylw (y := koPerm t * dPerm j) ⟨t, j, rfl⟩)
      (by simp)

theorem toPerm_injective : Function.Injective toPerm := by
  intro x y h
  have hε : x.ε = y.ε := by
    have hx := toPerm_mem_PO_iff x
    have hy := toPerm_mem_PO_iff y
    rw [h] at hx
    exact fin2_eq_of_iff _ _ (hx.symm.trans hy)
  have h2 : koPerm x.t * dPerm x.j * (if x.ε = 1 then ePerm else 1) =
      koPerm y.t * dPerm y.j * (if y.ε = 1 then ePerm else 1) := h
  rw [hε] at h2
  have h' : koPerm x.t * dPerm x.j = koPerm y.t * dPerm y.j := mul_right_cancel h2
  have hj : x.j = y.j := dPerm_hexad x.j y.j fun i _ hi8 => by
    have := congrArg (fun g => g i) h'
    simp only [Equiv.Perm.mul_apply] at this
    rwa [koPerm_apply_of_lt _ _ (dPerm_lt x.j i hi8),
      koPerm_apply_of_lt _ _ (dPerm_lt y.j i hi8)] at this
  have ht : x.t = y.t := by
    have h4 : koPerm x.t = koPerm y.t := by
      rw [hj] at h'
      exact mul_right_cancel h'
    have e1 := koPerm_eight x.t
    rw [h4, koPerm_eight y.t] at e1
    exact Fin.ext (by omega)
  exact ext' ht hj hε

theorem mul_inv_cancel_PG2 : ∀ x : PG2, x * x⁻¹ = 1 := by decide +kernel

theorem toPerm_inv (x : PG2) : toPerm x⁻¹ = (toPerm x)⁻¹ := by
  have h := toPerm_mul x x⁻¹
  rw [mul_inv_cancel_PG2, toPerm_one] at h
  exact eq_inv_of_mul_eq_one_right h.symm

instance instGroup : Group PG2 :=
  Group.ofLeftAxioms
    (fun a b c =>
      toPerm_injective (by rw [toPerm_mul, toPerm_mul, toPerm_mul, toPerm_mul, mul_assoc]))
    (fun a => toPerm_injective (by rw [toPerm_mul, toPerm_one, one_mul]))
    (fun a => toPerm_injective (by rw [toPerm_mul, toPerm_inv, toPerm_one, inv_mul_cancel]))

@[expose] def toPermHom : PG2 →* P24 where
  toFun := toPerm
  map_one' := toPerm_one
  map_mul' := toPerm_mul

theorem toPermHom_apply (x : PG2) :
    toPermHom x = koPerm x.t * dPerm x.j * (if x.ε = 1 then ePerm else 1) := rfl

theorem toPerm_mem_P2 (x : PG2) : toPerm x ∈ P2 := by
  obtain ⟨t, j, ε⟩ := x
  refine mem_P2_iff.2 ⟨koPerm t * dPerm j, ⟨t, j, rfl⟩, ?_⟩
  by_cases hε : ε = 1
  · subst hε
    right
    simp [toPerm]
  · left
    simp [toPerm, hε]

theorem range_toPermHom : toPermHom.range = P2 := by
  ext y
  constructor
  · rintro ⟨x, rfl⟩
    exact toPerm_mem_P2 x
  · intro hy
    obtain ⟨z, ⟨t, j, rfl⟩, hzy | hzy⟩ := mem_P2_iff.1 hy
    · exact ⟨⟨t, j, 0⟩, by simp [toPermHom_apply, hzy]⟩
    · exact ⟨⟨t, j, 1⟩, by simp [toPermHom_apply, hzy]⟩

@[expose] def all : List PG2 :=
  (List.finRange 16).flatMap fun t => (List.finRange 8).flatMap fun j =>
    (List.finRange 2).map fun ε => ⟨t, j, ε⟩

theorem mem_all (x : PG2) : x ∈ PG2.all := by
  simp only [PG2.all, List.mem_flatMap, List.mem_map, List.mem_finRange, true_and]
  exact ⟨x.t, x.j, x.ε, by cases x; rfl⟩

@[expose] def invs : List PG2 := PG2.all.filter fun x => decide (x ≠ 1) && decide (x * x = 1)

theorem mem_invs {x : PG2} (h1 : x ≠ 1) (h2 : x * x = 1) : x ∈ PG2.invs := by
  simp only [PG2.invs, List.mem_filter, Bool.and_eq_true, decide_eq_true_eq]
  exact ⟨PG2.mem_all x, h1, h2⟩

end PG2

end CFSG.Quasithin.RonanH143
