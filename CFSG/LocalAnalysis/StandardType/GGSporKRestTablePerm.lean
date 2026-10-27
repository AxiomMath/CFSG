module

public import Certificates.Data.CFSGNative.Th.Tables
public import Mathlib.GroupTheory.Perm.Basic

public section

namespace CFSG.StandardType.SporadicShape.PermCover

open Equiv CFSG.Sporadic.Th.Native

@[expose] def tablePermOK (n : ℕ) (T : Table) : Bool :=
  let R := invT n T
  (List.range n).all fun i =>
    decide (ap T i < n) && decide (ap R i < n) && decide (ap R (ap T i) = i) &&
      decide (ap T (ap R i) = i)

theorem tablePermOK_spec {n : ℕ} {T : Table} (h : tablePermOK n T = true) {i : ℕ} (hi : i < n) :
    ap T i < n ∧ ap (invT n T) i < n ∧ ap (invT n T) (ap T i) = i ∧
      ap T (ap (invT n T) i) = i := by
  unfold tablePermOK at h
  dsimp only at h
  simp only [List.all_eq_true, List.mem_range, Bool.and_eq_true, decide_eq_true_eq] at h
  obtain ⟨⟨⟨h1, h2⟩, h3⟩, h4⟩ := h i hi
  exact ⟨h1, h2, h3, h4⟩

@[expose] def tablePerm (n : ℕ) (T : Table) : Perm (Fin n) :=
  let R := invT n T
  if h : tablePermOK n T = true then
    ⟨fun i => ⟨ap T i.1, (tablePermOK_spec h i.2).1⟩, fun i => ⟨ap R i.1, (tablePermOK_spec h i.2).2.1⟩,
      fun i => Fin.ext (tablePermOK_spec h i.2).2.2.1, fun i => Fin.ext (tablePermOK_spec h i.2).2.2.2⟩
  else 1

theorem tablePerm_apply {n : ℕ} {T : Table} (h : tablePermOK n T = true) (i : Fin n) :
    ((tablePerm n T) i).val = ap T i.1 := by
  unfold tablePerm
  rw [dif_pos h]
  simp only [Equiv.coe_fn_mk]

end CFSG.StandardType.SporadicShape.PermCover
