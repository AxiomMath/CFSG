module

public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.Data.ZMod.Defs
public import Mathlib.Data.Fin.VecNotation
public import Mathlib.Data.Fintype.Pi
public import Mathlib.Data.Fintype.Powerset
public import CFSG.Quasithin.H13.L32AC50aPack

public section

namespace CFSG.Quasithin.H13.L32A.C.Alt7

open Equiv Equiv.Perm

@[expose] def ofSwaps (l : List (Fin 7 × Fin 7)) : Perm (Fin 7) :=
  (l.map fun p => swap p.1 p.2).prod

theorem of_all {α : Type*} {l : List α} {p : α → Prop} [DecidablePred p]
    (h : l.all (fun a => decide (p a)) = true) : ∀ a ∈ l, p a :=
  fun a ha => of_decide_eq_true (List.all_eq_true.mp h a ha)

theorem of_all₂ {α β : Type*} {l : List α} {m : List β} {p : α → β → Prop}
    [∀ a, DecidablePred (p a)] (h : l.all (fun a => m.all fun b => decide (p a b)) = true) :
    ∀ a ∈ l, ∀ b ∈ m, p a b :=
  fun a ha => of_all (List.all_eq_true.mp h a ha)

theorem of_any {α : Type*} {l : List α} {p : α → Prop} [DecidablePred p]
    (h : l.any (fun a => decide (p a)) = true) : ∃ a ∈ l, p a := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  exact ⟨a, ha, of_decide_eq_true hp⟩

theorem of_any₂ {α β : Type*} {l : List α} {m : List β} {p : α → β → Prop}
    [∀ a, DecidablePred (p a)] (h : l.any (fun a => m.any fun b => decide (p a b)) = true) :
    ∃ a ∈ l, ∃ b ∈ m, p a b := by
  obtain ⟨a, ha, hp⟩ := List.any_eq_true.mp h
  exact ⟨a, ha, of_any hp⟩

@[expose] def tsData : List (List (Fin 7 × Fin 7)) :=
  [[], [(4, 5)], [(1, 3)], [(1, 3), (4, 5)], [(0, 1), (2, 3)], [(0, 1), (2, 3), (4, 5)],
    [(0, 3), (0, 2), (0, 1)], [(0, 3), (0, 2), (0, 1), (4, 5)], [(0, 2)], [(0, 2), (4, 5)],
    [(0, 2), (1, 3)], [(0, 2), (1, 3), (4, 5)], [(0, 1), (0, 2), (0, 3)],
    [(0, 1), (0, 2), (0, 3), (4, 5)], [(0, 3), (1, 2)], [(0, 3), (1, 2), (4, 5)]]

@[expose] def tsList : List (Perm (Fin 7)) := tsData.map ofSwaps

@[expose] def taData : List (List (Fin 7 × Fin 7)) :=
  [[], [(1, 3), (4, 5)], [(0, 1), (2, 3)], [(0, 3), (0, 2), (0, 1), (4, 5)], [(0, 2), (4, 5)],
    [(0, 2), (1, 3)], [(0, 1), (0, 2), (0, 3), (4, 5)], [(0, 3), (1, 2)]]

@[expose] def taList : List (Perm (Fin 7)) := taData.map ofSwaps

@[expose] def stabData : List (List (Fin 7 × Fin 7)) :=
  [[], [(4, 6), (4, 5)], [(4, 5), (4, 6)], [(2, 3), (5, 6)], [(2, 3), (4, 5)],
    [(2, 3), (4, 6)], [(1, 2), (5, 6)], [(1, 2), (4, 5)], [(1, 2), (4, 6)], [(1, 3), (1, 2)],
    [(1, 3), (1, 2), (4, 6), (4, 5)], [(1, 3), (1, 2), (4, 5), (4, 6)], [(1, 2), (1, 3)],
    [(1, 2), (1, 3), (4, 6), (4, 5)], [(1, 2), (1, 3), (4, 5), (4, 6)], [(1, 3), (5, 6)],
    [(1, 3), (4, 5)], [(1, 3), (4, 6)], [(0, 1), (5, 6)], [(0, 1), (4, 5)], [(0, 1), (4, 6)],
    [(0, 1), (2, 3)], [(0, 1), (2, 3), (4, 6), (4, 5)], [(0, 1), (2, 3), (4, 5), (4, 6)],
    [(0, 2), (0, 1)], [(0, 2), (0, 1), (4, 6), (4, 5)], [(0, 2), (0, 1), (4, 5), (4, 6)],
    [(0, 3), (0, 2), (0, 1), (5, 6)], [(0, 3), (0, 2), (0, 1), (4, 5)],
    [(0, 3), (0, 2), (0, 1), (4, 6)], [(0, 2), (0, 3), (0, 1), (5, 6)],
    [(0, 2), (0, 3), (0, 1), (4, 5)], [(0, 2), (0, 3), (0, 1), (4, 6)], [(0, 3), (0, 1)],
    [(0, 3), (0, 1), (4, 6), (4, 5)], [(0, 3), (0, 1), (4, 5), (4, 6)], [(0, 1), (0, 2)],
    [(0, 1), (0, 2), (4, 6), (4, 5)], [(0, 1), (0, 2), (4, 5), (4, 6)],
    [(0, 1), (0, 3), (0, 2), (5, 6)], [(0, 1), (0, 3), (0, 2), (4, 5)],
    [(0, 1), (0, 3), (0, 2), (4, 6)], [(0, 2), (5, 6)], [(0, 2), (4, 5)], [(0, 2), (4, 6)],
    [(0, 3), (0, 2)], [(0, 3), (0, 2), (4, 6), (4, 5)], [(0, 3), (0, 2), (4, 5), (4, 6)],
    [(0, 2), (1, 3)], [(0, 2), (1, 3), (4, 6), (4, 5)], [(0, 2), (1, 3), (4, 5), (4, 6)],
    [(0, 3), (0, 1), (0, 2), (5, 6)], [(0, 3), (0, 1), (0, 2), (4, 5)],
    [(0, 3), (0, 1), (0, 2), (4, 6)], [(0, 1), (0, 2), (0, 3), (5, 6)],
    [(0, 1), (0, 2), (0, 3), (4, 5)], [(0, 1), (0, 2), (0, 3), (4, 6)], [(0, 1), (0, 3)],
    [(0, 1), (0, 3), (4, 6), (4, 5)], [(0, 1), (0, 3), (4, 5), (4, 6)], [(0, 2), (0, 3)],
    [(0, 2), (0, 3), (4, 6), (4, 5)], [(0, 2), (0, 3), (4, 5), (4, 6)], [(0, 3), (5, 6)],
    [(0, 3), (4, 5)], [(0, 3), (4, 6)], [(0, 2), (0, 1), (0, 3), (5, 6)],
    [(0, 2), (0, 1), (0, 3), (4, 5)], [(0, 2), (0, 1), (0, 3), (4, 6)], [(0, 3), (1, 2)],
    [(0, 3), (1, 2), (4, 6), (4, 5)], [(0, 3), (1, 2), (4, 5), (4, 6)]]

@[expose] def stabList : List (Perm (Fin 7)) := stabData.map ofSwaps

@[expose] def v4Data : List (List (Fin 7 × Fin 7)) :=
  [[], [(0, 1), (2, 3)], [(0, 2), (1, 3)], [(0, 3), (1, 2)]]

@[expose] def v4List : List (Perm (Fin 7)) := v4Data.map ofSwaps

@[expose] def raSData : List (List (Fin 7 × Fin 7)) :=
  [[], [(4, 5)], [(1, 3)], [(1, 3), (4, 5)], [(1, 4), (3, 5)], [(1, 5), (1, 3), (1, 4)],
    [(1, 4), (1, 3), (1, 5)], [(1, 5), (3, 4)], [(0, 1), (2, 3)], [(0, 1), (2, 3), (4, 5)],
    [(0, 3), (0, 2), (0, 1)], [(0, 3), (0, 2), (0, 1), (4, 5)],
    [(0, 4), (0, 1), (2, 5), (2, 3)], [(0, 5), (0, 3), (0, 2), (0, 4), (0, 1)],
    [(0, 4), (0, 3), (0, 2), (0, 5), (0, 1)], [(0, 5), (0, 1), (2, 4), (2, 3)], [(0, 2)],
    [(0, 2), (4, 5)], [(0, 2), (1, 3)], [(0, 2), (1, 3), (4, 5)], [(0, 2), (1, 4), (3, 5)],
    [(0, 2), (1, 5), (1, 3), (1, 4)], [(0, 2), (1, 4), (1, 3), (1, 5)],
    [(0, 2), (1, 5), (3, 4)], [(0, 1), (0, 2), (0, 3)], [(0, 1), (0, 2), (0, 3), (4, 5)],
    [(0, 3), (1, 2)], [(0, 3), (1, 2), (4, 5)], [(0, 4), (0, 1), (0, 2), (0, 5), (0, 3)],
    [(0, 5), (0, 3), (1, 2), (1, 4)], [(0, 4), (0, 3), (1, 2), (1, 5)],
    [(0, 5), (0, 1), (0, 2), (0, 4), (0, 3)], [(0, 1), (0, 4), (2, 3), (2, 5)],
    [(0, 1), (0, 5), (0, 2), (0, 3), (0, 4)], [(0, 4), (2, 5)], [(0, 5), (0, 2), (0, 4)],
    [(0, 3), (0, 5), (0, 2), (0, 1), (0, 4)], [(0, 3), (0, 4), (1, 5), (1, 2)],
    [(0, 4), (1, 3), (2, 5)], [(0, 5), (0, 2), (0, 4), (1, 3)],
    [(0, 1), (0, 4), (0, 2), (0, 3), (0, 5)], [(0, 1), (0, 5), (2, 3), (2, 4)],
    [(0, 4), (0, 2), (0, 5)], [(0, 5), (2, 4)], [(0, 3), (0, 5), (1, 4), (1, 2)],
    [(0, 3), (0, 4), (0, 2), (0, 1), (0, 5)], [(0, 4), (0, 2), (0, 5), (1, 3)],
    [(0, 5), (1, 3), (2, 4)]]

@[expose] def raSList : List (Perm (Fin 7)) := raSData.map ofSwaps

@[expose] def raAData : List (List (Fin 7 × Fin 7)) :=
  [[], [(1, 3), (4, 5)], [(1, 4), (3, 5)], [(1, 5), (3, 4)], [(0, 1), (2, 3)],
    [(0, 3), (0, 2), (0, 1), (4, 5)], [(0, 4), (0, 1), (2, 5), (2, 3)],
    [(0, 5), (0, 1), (2, 4), (2, 3)], [(0, 2), (4, 5)], [(0, 2), (1, 3)],
    [(0, 2), (1, 5), (1, 3), (1, 4)], [(0, 2), (1, 4), (1, 3), (1, 5)],
    [(0, 1), (0, 2), (0, 3), (4, 5)], [(0, 3), (1, 2)], [(0, 5), (0, 3), (1, 2), (1, 4)],
    [(0, 4), (0, 3), (1, 2), (1, 5)], [(0, 1), (0, 4), (2, 3), (2, 5)], [(0, 4), (2, 5)],
    [(0, 3), (0, 4), (1, 5), (1, 2)], [(0, 5), (0, 2), (0, 4), (1, 3)],
    [(0, 1), (0, 5), (2, 3), (2, 4)], [(0, 5), (2, 4)], [(0, 3), (0, 5), (1, 4), (1, 2)],
    [(0, 4), (0, 2), (0, 5), (1, 3)]]

@[expose] def raAList : List (Perm (Fin 7)) := raAData.map ofSwaps

@[expose] def rbSData : List (List (Fin 7 × Fin 7)) :=
  [[], [(4, 5)], [(2, 3)], [(2, 3), (4, 5)], [(1, 2)], [(1, 2), (4, 5)], [(1, 3), (1, 2)],
    [(1, 3), (1, 2), (4, 5)], [(1, 2), (1, 3)], [(1, 2), (1, 3), (4, 5)], [(1, 3)],
    [(1, 3), (4, 5)], [(0, 1)], [(0, 1), (4, 5)], [(0, 1), (2, 3)], [(0, 1), (2, 3), (4, 5)],
    [(0, 2), (0, 1)], [(0, 2), (0, 1), (4, 5)], [(0, 3), (0, 2), (0, 1)],
    [(0, 3), (0, 2), (0, 1), (4, 5)], [(0, 2), (0, 3), (0, 1)],
    [(0, 2), (0, 3), (0, 1), (4, 5)], [(0, 3), (0, 1)], [(0, 3), (0, 1), (4, 5)],
    [(0, 1), (0, 2)], [(0, 1), (0, 2), (4, 5)], [(0, 1), (0, 3), (0, 2)],
    [(0, 1), (0, 3), (0, 2), (4, 5)], [(0, 2)], [(0, 2), (4, 5)], [(0, 3), (0, 2)],
    [(0, 3), (0, 2), (4, 5)], [(0, 2), (1, 3)], [(0, 2), (1, 3), (4, 5)],
    [(0, 3), (0, 1), (0, 2)], [(0, 3), (0, 1), (0, 2), (4, 5)], [(0, 1), (0, 2), (0, 3)],
    [(0, 1), (0, 2), (0, 3), (4, 5)], [(0, 1), (0, 3)], [(0, 1), (0, 3), (4, 5)],
    [(0, 2), (0, 3)], [(0, 2), (0, 3), (4, 5)], [(0, 3)], [(0, 3), (4, 5)],
    [(0, 2), (0, 1), (0, 3)], [(0, 2), (0, 1), (0, 3), (4, 5)], [(0, 3), (1, 2)],
    [(0, 3), (1, 2), (4, 5)]]

@[expose] def rbSList : List (Perm (Fin 7)) := rbSData.map ofSwaps

@[expose] def rbAData : List (List (Fin 7 × Fin 7)) :=
  [[], [(2, 3), (4, 5)], [(1, 2), (4, 5)], [(1, 3), (1, 2)], [(1, 2), (1, 3)],
    [(1, 3), (4, 5)], [(0, 1), (4, 5)], [(0, 1), (2, 3)], [(0, 2), (0, 1)],
    [(0, 3), (0, 2), (0, 1), (4, 5)], [(0, 2), (0, 3), (0, 1), (4, 5)], [(0, 3), (0, 1)],
    [(0, 1), (0, 2)], [(0, 1), (0, 3), (0, 2), (4, 5)], [(0, 2), (4, 5)], [(0, 3), (0, 2)],
    [(0, 2), (1, 3)], [(0, 3), (0, 1), (0, 2), (4, 5)], [(0, 1), (0, 2), (0, 3), (4, 5)],
    [(0, 1), (0, 3)], [(0, 2), (0, 3)], [(0, 3), (4, 5)], [(0, 2), (0, 1), (0, 3), (4, 5)],
    [(0, 3), (1, 2)]]

@[expose] def rbAList : List (Perm (Fin 7)) := rbAData.map ofSwaps

@[expose] def rcSData : List (List (Fin 7 × Fin 7)) :=
  [[], [(5, 6)], [(4, 5)], [(4, 6), (4, 5)], [(4, 5), (4, 6)], [(4, 6)], [(1, 3)],
    [(1, 3), (5, 6)], [(1, 3), (4, 5)], [(1, 3), (4, 6), (4, 5)], [(1, 3), (4, 5), (4, 6)],
    [(1, 3), (4, 6)], [(0, 1), (2, 3)], [(0, 1), (2, 3), (5, 6)], [(0, 1), (2, 3), (4, 5)],
    [(0, 1), (2, 3), (4, 6), (4, 5)], [(0, 1), (2, 3), (4, 5), (4, 6)],
    [(0, 1), (2, 3), (4, 6)], [(0, 3), (0, 2), (0, 1)], [(0, 3), (0, 2), (0, 1), (5, 6)],
    [(0, 3), (0, 2), (0, 1), (4, 5)], [(0, 3), (0, 2), (0, 1), (4, 6), (4, 5)],
    [(0, 3), (0, 2), (0, 1), (4, 5), (4, 6)], [(0, 3), (0, 2), (0, 1), (4, 6)], [(0, 2)],
    [(0, 2), (5, 6)], [(0, 2), (4, 5)], [(0, 2), (4, 6), (4, 5)], [(0, 2), (4, 5), (4, 6)],
    [(0, 2), (4, 6)], [(0, 2), (1, 3)], [(0, 2), (1, 3), (5, 6)], [(0, 2), (1, 3), (4, 5)],
    [(0, 2), (1, 3), (4, 6), (4, 5)], [(0, 2), (1, 3), (4, 5), (4, 6)],
    [(0, 2), (1, 3), (4, 6)], [(0, 1), (0, 2), (0, 3)], [(0, 1), (0, 2), (0, 3), (5, 6)],
    [(0, 1), (0, 2), (0, 3), (4, 5)], [(0, 1), (0, 2), (0, 3), (4, 6), (4, 5)],
    [(0, 1), (0, 2), (0, 3), (4, 5), (4, 6)], [(0, 1), (0, 2), (0, 3), (4, 6)],
    [(0, 3), (1, 2)], [(0, 3), (1, 2), (5, 6)], [(0, 3), (1, 2), (4, 5)],
    [(0, 3), (1, 2), (4, 6), (4, 5)], [(0, 3), (1, 2), (4, 5), (4, 6)],
    [(0, 3), (1, 2), (4, 6)]]

@[expose] def rcSList : List (Perm (Fin 7)) := rcSData.map ofSwaps

@[expose] def rcAData : List (List (Fin 7 × Fin 7)) :=
  [[], [(4, 6), (4, 5)], [(4, 5), (4, 6)], [(1, 3), (5, 6)], [(1, 3), (4, 5)],
    [(1, 3), (4, 6)], [(0, 1), (2, 3)], [(0, 1), (2, 3), (4, 6), (4, 5)],
    [(0, 1), (2, 3), (4, 5), (4, 6)], [(0, 3), (0, 2), (0, 1), (5, 6)],
    [(0, 3), (0, 2), (0, 1), (4, 5)], [(0, 3), (0, 2), (0, 1), (4, 6)], [(0, 2), (5, 6)],
    [(0, 2), (4, 5)], [(0, 2), (4, 6)], [(0, 2), (1, 3)], [(0, 2), (1, 3), (4, 6), (4, 5)],
    [(0, 2), (1, 3), (4, 5), (4, 6)], [(0, 1), (0, 2), (0, 3), (5, 6)],
    [(0, 1), (0, 2), (0, 3), (4, 5)], [(0, 1), (0, 2), (0, 3), (4, 6)], [(0, 3), (1, 2)],
    [(0, 3), (1, 2), (4, 6), (4, 5)], [(0, 3), (1, 2), (4, 5), (4, 6)]]

@[expose] def rcAList : List (Perm (Fin 7)) := rcAData.map ofSwaps

@[expose] def s4Data : List (List (Fin 7 × Fin 7)) :=
  [[], [(2, 3)], [(1, 2)], [(1, 3), (1, 2)], [(1, 2), (1, 3)], [(1, 3)], [(0, 1)],
    [(0, 1), (2, 3)], [(0, 2), (0, 1)], [(0, 3), (0, 2), (0, 1)], [(0, 2), (0, 3), (0, 1)],
    [(0, 3), (0, 1)], [(0, 1), (0, 2)], [(0, 1), (0, 3), (0, 2)], [(0, 2)], [(0, 3), (0, 2)],
    [(0, 2), (1, 3)], [(0, 3), (0, 1), (0, 2)], [(0, 1), (0, 2), (0, 3)], [(0, 1), (0, 3)],
    [(0, 2), (0, 3)], [(0, 3)], [(0, 2), (0, 1), (0, 3)], [(0, 3), (1, 2)]]

@[expose] def s4List : List (Perm (Fin 7)) := s4Data.map ofSwaps

@[expose] def s3Data : List (List (Fin 7 × Fin 7)) :=
  [[], [(5, 6)], [(4, 5)], [(4, 6), (4, 5)], [(4, 5), (4, 6)], [(4, 6)]]

@[expose] def s3List : List (Perm (Fin 7)) := s3Data.map ofSwaps

theorem ts_closed : (1 : Perm (Fin 7)) ∈ tsList ∧
    (∀ a ∈ tsList, ∀ b ∈ tsList, a * b ∈ tsList) ∧ ∀ a ∈ tsList, a⁻¹ ∈ tsList := by
  exact Alt7Pack.closed_of_K (by norm_num) tsList Alt7Pack.tsCodes Alt7Pack.one7
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem ts_nodup : tsList.Nodup ∧ tsList.length = 16 := by
  decide +kernel

theorem ta_closed : (1 : Perm (Fin 7)) ∈ taList ∧
    (∀ a ∈ taList, ∀ b ∈ taList, a * b ∈ taList) ∧ ∀ a ∈ taList, a⁻¹ ∈ taList := by
  exact Alt7Pack.closed_of_K (by norm_num) taList Alt7Pack.taCodes Alt7Pack.one7
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem ta_nodup : taList.Nodup ∧ taList.length = 8 := by
  decide +kernel

theorem v4_closed : (1 : Perm (Fin 7)) ∈ v4List ∧
    (∀ a ∈ v4List, ∀ b ∈ v4List, a * b ∈ v4List) ∧ ∀ a ∈ v4List, a⁻¹ ∈ v4List := by
  have h : decide ((1 : Perm (Fin 7)) ∈ v4List) = true ∧
      v4List.all (fun a => v4List.all fun b => decide (a * b ∈ v4List)) = true ∧
      v4List.all (fun a => decide (a⁻¹ ∈ v4List)) = true := by
    decide +kernel
  exact ⟨of_decide_eq_true h.1, of_all₂ h.2.1, of_all h.2.2⟩

theorem v4_nodup : v4List.Nodup ∧ v4List.length = 4 := by
  decide +kernel

theorem raS_closed : (1 : Perm (Fin 7)) ∈ raSList ∧
    (∀ a ∈ raSList, ∀ b ∈ raSList, a * b ∈ raSList) ∧ ∀ a ∈ raSList, a⁻¹ ∈ raSList := by
  exact Alt7Pack.closed_of_K (by norm_num) raSList Alt7Pack.raSCodes Alt7Pack.one7
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem raS_nodup : raSList.Nodup ∧ raSList.length = 48 := by
  decide +kernel

theorem raA_closed : (1 : Perm (Fin 7)) ∈ raAList ∧
    (∀ a ∈ raAList, ∀ b ∈ raAList, a * b ∈ raAList) ∧ ∀ a ∈ raAList, a⁻¹ ∈ raAList := by
  exact Alt7Pack.closed_of_K (by norm_num) raAList Alt7Pack.raACodes Alt7Pack.one7
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem raA_nodup : raAList.Nodup ∧ raAList.length = 24 := by
  decide +kernel

theorem rbS_closed : (1 : Perm (Fin 7)) ∈ rbSList ∧
    (∀ a ∈ rbSList, ∀ b ∈ rbSList, a * b ∈ rbSList) ∧ ∀ a ∈ rbSList, a⁻¹ ∈ rbSList := by
  exact Alt7Pack.closed_of_K (by norm_num) rbSList Alt7Pack.rbSCodes Alt7Pack.one7
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rbS_nodup : rbSList.Nodup ∧ rbSList.length = 48 := by
  decide +kernel

theorem rbA_closed : (1 : Perm (Fin 7)) ∈ rbAList ∧
    (∀ a ∈ rbAList, ∀ b ∈ rbAList, a * b ∈ rbAList) ∧ ∀ a ∈ rbAList, a⁻¹ ∈ rbAList := by
  exact Alt7Pack.closed_of_K (by norm_num) rbAList Alt7Pack.rbACodes Alt7Pack.one7
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rbA_nodup : rbAList.Nodup ∧ rbAList.length = 24 := by
  decide +kernel

theorem rcS_closed : (1 : Perm (Fin 7)) ∈ rcSList ∧
    (∀ a ∈ rcSList, ∀ b ∈ rcSList, a * b ∈ rcSList) ∧ ∀ a ∈ rcSList, a⁻¹ ∈ rcSList := by
  exact Alt7Pack.closed_of_K (by norm_num) rcSList Alt7Pack.rcSCodes Alt7Pack.one7
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rcS_nodup : rcSList.Nodup ∧ rcSList.length = 48 := by
  decide +kernel

theorem rcA_closed : (1 : Perm (Fin 7)) ∈ rcAList ∧
    (∀ a ∈ rcAList, ∀ b ∈ rcAList, a * b ∈ rcAList) ∧ ∀ a ∈ rcAList, a⁻¹ ∈ rcAList := by
  exact Alt7Pack.closed_of_K (by norm_num) rcAList Alt7Pack.rcACodes Alt7Pack.one7
    (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem rcA_nodup : rcAList.Nodup ∧ rcAList.length = 24 := by
  decide +kernel

theorem ta_sign : ∀ a ∈ taList, sign a = 1 := by
  have h : taList.all (fun a => decide (sign a = 1)) = true := by
    decide +kernel
  exact of_all h

theorem stab_sign : ∀ a ∈ stabList, sign a = 1 := by
  have h : stabList.all (fun a => decide (sign a = 1)) = true := by
    decide +kernel
  exact of_all h

theorem raA_sign : ∀ a ∈ raAList, sign a = 1 := by
  have h : raAList.all (fun a => decide (sign a = 1)) = true := by
    decide +kernel
  exact of_all h

theorem rbA_sign : ∀ a ∈ rbAList, sign a = 1 := by
  have h : rbAList.all (fun a => decide (sign a = 1)) = true := by
    decide +kernel
  exact of_all h

theorem rcA_sign : ∀ a ∈ rcAList, sign a = 1 := by
  have h : rcAList.all (fun a => decide (sign a = 1)) = true := by
    decide +kernel
  exact of_all h

theorem ts_sub_raS : ∀ a ∈ tsList, a ∈ raSList := by
  have h : tsList.all (fun a => decide (a ∈ raSList)) = true := by
    decide +kernel
  exact of_all h

theorem ts_sub_rbS : ∀ a ∈ tsList, a ∈ rbSList := by
  have h : tsList.all (fun a => decide (a ∈ rbSList)) = true := by
    decide +kernel
  exact of_all h

theorem ts_sub_rcS : ∀ a ∈ tsList, a ∈ rcSList := by
  have h : tsList.all (fun a => decide (a ∈ rcSList)) = true := by
    decide +kernel
  exact of_all h

theorem ta_sub_raA : ∀ a ∈ taList, a ∈ raAList := by
  have h : taList.all (fun a => decide (a ∈ raAList)) = true := by
    decide +kernel
  exact of_all h

theorem ta_sub_rbA : ∀ a ∈ taList, a ∈ rbAList := by
  have h : taList.all (fun a => decide (a ∈ rbAList)) = true := by
    decide +kernel
  exact of_all h

theorem ta_sub_rcA : ∀ a ∈ taList, a ∈ rcAList := by
  have h : taList.all (fun a => decide (a ∈ rcAList)) = true := by
    decide +kernel
  exact of_all h

theorem ta_sub_ts : ∀ a ∈ taList, a ∈ tsList := by
  have h : taList.all (fun a => decide (a ∈ tsList)) = true := by
    decide +kernel
  exact of_all h

theorem raS_not_normal : ∃ r ∈ raSList, ∃ t ∈ tsList, r * t * r⁻¹ ∉ tsList := by
  have h : raSList.any (fun r =>
      tsList.any fun t => decide (r * t * r⁻¹ ∉ tsList)) = true := by
    decide +kernel
  exact of_any₂ h

theorem raA_not_normal : ∃ r ∈ raAList, ∃ t ∈ taList, r * t * r⁻¹ ∉ taList := by
  have h : raAList.any (fun r =>
      taList.any fun t => decide (r * t * r⁻¹ ∉ taList)) = true := by
    decide +kernel
  exact of_any₂ h

theorem rbS_not_normal : ∃ r ∈ rbSList, ∃ t ∈ tsList, r * t * r⁻¹ ∉ tsList := by
  have h : rbSList.any (fun r =>
      tsList.any fun t => decide (r * t * r⁻¹ ∉ tsList)) = true := by
    decide +kernel
  exact of_any₂ h

theorem rbA_not_normal : ∃ r ∈ rbAList, ∃ t ∈ taList, r * t * r⁻¹ ∉ taList := by
  have h : rbAList.any (fun r =>
      taList.any fun t => decide (r * t * r⁻¹ ∉ taList)) = true := by
    decide +kernel
  exact of_any₂ h

theorem rcS_not_normal : ∃ r ∈ rcSList, ∃ t ∈ tsList, r * t * r⁻¹ ∉ tsList := by
  have h : rcSList.any (fun r =>
      tsList.any fun t => decide (r * t * r⁻¹ ∉ tsList)) = true := by
    decide +kernel
  exact of_any₂ h

theorem rcA_not_normal : ∃ r ∈ rcAList, ∃ t ∈ taList, r * t * r⁻¹ ∉ taList := by
  have h : rcAList.any (fun r =>
      taList.any fun t => decide (r * t * r⁻¹ ∉ taList)) = true := by
    decide +kernel
  exact of_any₂ h

@[expose] def d3 : Finset (Fin 7) := {4, 5, 6}

theorem ofSubtype_mem_s3 : ∀ b : Perm {x : Fin 7 // x ∈ d3}, ofSubtype b ∈ s3List := by
  decide +kernel

@[expose] def d3c : Finset (Fin 7) := {0, 1, 2, 3}

theorem mem_d3c : ∀ x : Fin 7, x ∈ d3c ↔ x ∉ d3 := by
  decide +kernel

theorem ofSubtype_mem_s4 : ∀ a : Perm {x : Fin 7 // x ∈ d3c}, ofSubtype a ∈ s4List := by
  decide +kernel

theorem stab_of_mul : ∀ a ∈ s4List, ∀ b ∈ s3List, sign (a * b) = 1 → a * b ∈ stabList := by
  have h : s4List.all (fun a =>
      s3List.all fun b => decide (sign (a * b) = 1 → a * b ∈ stabList)) = true := by
    decide +kernel
  exact of_all₂ h

theorem stab_nodup : stabList.Nodup ∧ stabList.length = 72 := by
  decide +kernel

theorem stab_maps : ∀ g ∈ stabList, ∀ i ∈ d3, g i ∈ d3 := by
  have h : stabList.all (fun g => decide (∀ i ∈ d3, g i ∈ d3)) = true := by
    decide +kernel
  exact of_all h

@[expose] def EvenOn (g : Perm (Fin 7)) : Prop :=
  (g 4 = 4 ∧ g 5 = 5) ∨ (g 4 = 5 ∧ g 5 = 6) ∨ (g 4 = 6 ∧ g 5 = 4)

instance (g : Perm (Fin 7)) : Decidable (EvenOn g) := by
  unfold EvenOn
  infer_instance

theorem d1 : ∀ x ∈ stabList, x ∉ v4List → x ^ 4 = 1 →
    ∃ g ∈ stabList, (x * g * x⁻¹ * g⁻¹) ^ 3 = 1 ∧ x * g * x⁻¹ * g⁻¹ ≠ 1 := by
  have h : stabList.all (fun x => decide (x ∉ v4List → x ^ 4 = 1 →
      ∃ g ∈ stabList, (x * g * x⁻¹ * g⁻¹) ^ 3 = 1 ∧ x * g * x⁻¹ * g⁻¹ ≠ 1)) = true := by
    decide +kernel
  exact of_all h

theorem d2a : ∀ g ∈ stabList, ∀ x ∈ stabList, x ^ 3 = 1 → EvenOn g →
    g * x * g⁻¹ * x⁻¹ ∈ v4List := by
  exact Alt7Pack.commA_of_K (by norm_num) stabList v4List Alt7Pack.stabCodes Alt7Pack.v4Codes
    Alt7Pack.one7 EvenOn Alt7Pack.evenOnK (fun g h => (Alt7Pack.evenOnK_enc g).2 h)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem d2b : ∀ g ∈ stabList, ∀ x ∈ stabList, x ^ 3 = 1 → ¬ EvenOn g →
    g * x * g⁻¹ * x ∈ v4List := by
  exact Alt7Pack.commB_of_K (by norm_num) stabList v4List Alt7Pack.stabCodes Alt7Pack.v4Codes
    Alt7Pack.one7 (fun g => ¬ EvenOn g) (fun c => !Alt7Pack.evenOnK c)
    (fun g h => Alt7Pack.not_evenOnK_enc g h)
    (by decide +kernel) (by decide +kernel) (by decide +kernel) (by decide +kernel)

theorem d3_v4 : ∀ v ∈ v4List, v ^ 3 = 1 → v = 1 := by
  have h : v4List.all (fun v => decide (v ^ 3 = 1 → v = 1)) = true := by
    decide +kernel
  exact of_all h

theorem stab_exp : ∀ x ∈ stabList, x ^ 12 = 1 := by
  exact fun x hx => Alt7Pack.powImp_of_K (by norm_num) stabList Alt7Pack.stabCodes Alt7Pack.one7
    0 12 (by decide +kernel) (by decide +kernel) (by decide +kernel) x hx (pow_zero x)

theorem d3_unique : ∀ Δ : Finset (Fin 7), Δ.card = 3 → (∀ t ∈ taList, ∀ i ∈ Δ, t i ∈ Δ) →
    Δ = d3 := by
  have h : ∀ Δ : Finset (Fin 7), Δ.card = 3 →
      taList.all (fun t => decide (∀ i ∈ Δ, t i ∈ Δ)) = true → Δ = d3 := by
    decide +kernel
  intro Δ hΔ ht
  exact h Δ hΔ (List.all_eq_true.mpr fun t htl => decide_eq_true (ht t htl))

@[expose] def e45 : Fin 7 → ZMod 2 := ![0, 0, 0, 0, 1, 1, 0]

@[expose] def e0123 : Fin 7 → ZMod 2 := ![1, 1, 1, 1, 0, 0, 0]

@[expose] def e012345 : Fin 7 → ZMod 2 := ![1, 1, 1, 1, 1, 1, 0]

theorem fixed_vec : ∀ w : Fin 7 → ZMod 2, ∑ i, w i = 0 →
    (∀ t ∈ taList, ∀ i, w (t⁻¹ i) = w i) → w = 0 ∨ w = e45 ∨ w = e0123 ∨ w = e012345 := by
  have h : ∀ w : Fin 7 → ZMod 2, ∑ i, w i = 0 →
      taList.all (fun t => decide (∀ i, w (t⁻¹ i) = w i)) = true →
      w = 0 ∨ w = e45 ∨ w = e0123 ∨ w = e012345 := by
    decide +kernel
  intro w hw ht
  exact h w hw (List.all_eq_true.mpr fun t htl => decide_eq_true (ht t htl))

@[expose] def y1 : Perm (Fin 7) := ofSwaps [(0, 4), (0, 1), (2, 5), (2, 3)]

@[expose] def c012 : Perm (Fin 7) := ofSwaps [(0, 2), (0, 1)]

@[expose] def c456 : Perm (Fin 7) := ofSwaps [(4, 6), (4, 5)]

theorem three_facts : y1 ∈ raAList ∧ y1 ^ 2 ∈ raAList ∧ y1 ^ 3 = 1 ∧ c012 ∈ rbAList ∧
    c456 ∈ rcAList ∧ c012 ^ 3 = 1 ∧ c456 ^ 3 = 1 ∧ c012 * c456 = c456 * c012 ∧
    ∀ i j : Fin 3, c012 ^ (i : ℕ) * c456 ^ (j : ℕ) = 1 → i = 0 ∧ j = 0 := by
  decide +kernel

theorem e45_rank : ∀ a b c : ZMod 2, (fun i => a * e45 i + b * e45 (y1⁻¹ i) +
    c * e45 ((y1 ^ 2)⁻¹ i)) = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  decide +kernel

theorem e012345_rank : ∀ a b c : ZMod 2, (fun i => a * e012345 i + b * e012345 (c456⁻¹ i) +
    c * e012345 ((c456 ^ 2)⁻¹ i)) = 0 → a = 0 ∧ b = 0 ∧ c = 0 := by
  decide +kernel

theorem c456_facts : c456 ∈ rcSList ∧ c456 ^ 2 ∈ rcAList ∧ c456 ^ 2 ∈ rcSList ∧
    y1 ∈ raSList ∧ y1 ^ 2 ∈ raSList ∧ c012 ∈ rbSList ∧ c456 ∈ rcAList := by
  decide +kernel

theorem e0123_fixed : (∀ r ∈ rbSList, ∀ i, e0123 (r⁻¹ i) = e0123 i) ∧
    ∀ r ∈ rcSList, ∀ i, e0123 (r⁻¹ i) = e0123 i := by
  have h : rbSList.all (fun r => decide (∀ i, e0123 (r⁻¹ i) = e0123 i)) = true ∧
      rcSList.all (fun r => decide (∀ i, e0123 (r⁻¹ i) = e0123 i)) = true := by
    decide +kernel
  exact ⟨of_all h.1, of_all h.2⟩

@[expose] def cycList : List (Perm (Fin 7)) :=
  [[(0, 2), (0, 1)], [(0, 5), (0, 3)], [(1, 3), (1, 2)], [(1, 6), (1, 4)], [(2, 4), (2, 3)],
    [(0, 5), (0, 2)], [(3, 5), (3, 4)], [(1, 6), (1, 3)], [(4, 6), (4, 5)], [(0, 4), (0, 2)],
    [(0, 6), (0, 5)], [(1, 5), (1, 3)], [(0, 6), (0, 1)], [(2, 6), (2, 4)]].map ofSwaps

theorem cyc_sign : ∀ c ∈ cycList, sign c = 1 := by
  have h : cycList.all (fun c => decide (sign c = 1)) = true := by
    decide +kernel
  exact of_all h

theorem exists_cycles : ∀ i : Fin 7, ∃ c₁ ∈ cycList, ∃ c₂ ∈ cycList, c₁ i ≠ i ∧ c₂ i ≠ i ∧
    ∀ x, c₁ x ≠ x → c₂ x ≠ x → x = i := by
  have h : ∀ i : Fin 7, cycList.any (fun c₁ => cycList.any fun c₂ =>
      decide (c₁ i ≠ i ∧ c₂ i ≠ i ∧ ∀ x, c₁ x ≠ x → c₂ x ≠ x → x = i)) = true := by
    decide +kernel
  intro i
  obtain ⟨c₁, h₁, c₂, h₂, hc⟩ := of_any₂ (h i)
  exact ⟨c₁, h₁, c₂, h₂, hc⟩

end CFSG.Quasithin.H13.L32A.C.Alt7
