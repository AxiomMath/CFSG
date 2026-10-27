module

public import CFSG.Monster.B.TwoA.Base.SevenPairA

public section

namespace CFSG.Monster.B.TwoA

open CFSG.Monster.Code CFSG.Sporadic.Mathieu

open scoped Pointwise

@[expose] def R4 : Fin 15 → Finset (Set.powersetCard (Fin 24) 2) := ![
  {duad 2 3 (by decide), duad 4 5 (by decide), duad 6 7 (by decide)},
  {duad 2 3 (by decide), duad 4 6 (by decide), duad 5 7 (by decide)},
  {duad 2 3 (by decide), duad 4 7 (by decide), duad 5 6 (by decide)},
  {duad 2 3 (by decide), duad 8 9 (by decide), duad 10 11 (by decide)},
  {duad 2 3 (by decide), duad 8 10 (by decide), duad 9 11 (by decide)},
  {duad 2 3 (by decide), duad 8 11 (by decide), duad 9 10 (by decide)},
  {duad 2 3 (by decide), duad 12 13 (by decide), duad 14 15 (by decide)},
  {duad 2 3 (by decide), duad 12 14 (by decide), duad 13 15 (by decide)},
  {duad 2 3 (by decide), duad 12 15 (by decide), duad 13 14 (by decide)},
  {duad 2 3 (by decide), duad 16 17 (by decide), duad 18 19 (by decide)},
  {duad 2 3 (by decide), duad 16 18 (by decide), duad 17 19 (by decide)},
  {duad 2 3 (by decide), duad 16 19 (by decide), duad 17 18 (by decide)},
  {duad 2 3 (by decide), duad 20 21 (by decide), duad 22 23 (by decide)},
  {duad 2 3 (by decide), duad 20 22 (by decide), duad 21 23 (by decide)},
  {duad 2 3 (by decide), duad 20 23 (by decide), duad 21 22 (by decide)}]

@[expose] def R5 : Fin 10 → Finset (Set.powersetCard (Fin 24) 2) := ![
  {duad 2 3 (by decide), duad 4 5 (by decide), duad 6 7 (by decide), duad 8 9 (by decide),
    duad 10 11 (by decide), duad 12 13 (by decide), duad 14 15 (by decide)},
  {duad 2 3 (by decide), duad 4 5 (by decide), duad 6 7 (by decide), duad 16 17 (by decide),
    duad 18 19 (by decide), duad 20 21 (by decide), duad 22 23 (by decide)},
  {duad 2 3 (by decide), duad 4 6 (by decide), duad 5 7 (by decide), duad 8 11 (by decide),
    duad 9 10 (by decide), duad 16 19 (by decide), duad 17 18 (by decide)},
  {duad 2 3 (by decide), duad 4 6 (by decide), duad 5 7 (by decide), duad 12 15 (by decide),
    duad 13 14 (by decide), duad 20 23 (by decide), duad 21 22 (by decide)},
  {duad 2 3 (by decide), duad 4 7 (by decide), duad 5 6 (by decide), duad 8 10 (by decide),
    duad 9 11 (by decide), duad 20 22 (by decide), duad 21 23 (by decide)},
  {duad 2 3 (by decide), duad 4 7 (by decide), duad 5 6 (by decide), duad 12 14 (by decide),
    duad 13 15 (by decide), duad 16 18 (by decide), duad 17 19 (by decide)},
  {duad 2 3 (by decide), duad 8 9 (by decide), duad 10 11 (by decide), duad 16 18 (by decide),
    duad 17 19 (by decide), duad 20 23 (by decide), duad 21 22 (by decide)},
  {duad 2 3 (by decide), duad 8 10 (by decide), duad 9 11 (by decide), duad 12 15 (by decide),
    duad 13 14 (by decide), duad 16 17 (by decide), duad 18 19 (by decide)},
  {duad 2 3 (by decide), duad 8 11 (by decide), duad 9 10 (by decide), duad 12 14 (by decide),
    duad 13 15 (by decide), duad 20 21 (by decide), duad 22 23 (by decide)},
  {duad 2 3 (by decide), duad 12 13 (by decide), duad 14 15 (by decide), duad 16 19 (by decide),
    duad 17 18 (by decide), duad 20 22 (by decide), duad 21 23 (by decide)}]

@[expose] def perm4Fun : Fin 15 → Fin 24 → Fin 24 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  ![0, 1, 2, 3, 4, 6, 7, 5, 8, 11, 9, 10, 16, 19, 17, 18, 20, 23, 21, 22, 12, 15, 13, 14],
  ![0, 1, 2, 3, 4, 7, 5, 6, 8, 10, 11, 9, 20, 22, 23, 21, 12, 14, 15, 13, 16, 18, 19, 17],
  ![0, 1, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7, 12, 13, 14, 15, 20, 23, 21, 22, 16, 18, 19, 17],
  ![0, 1, 2, 3, 8, 10, 11, 9, 4, 7, 5, 6, 20, 22, 23, 21, 16, 17, 18, 19, 12, 15, 13, 14],
  ![0, 1, 2, 3, 8, 11, 9, 10, 4, 6, 7, 5, 16, 19, 17, 18, 12, 14, 15, 13, 20, 21, 22, 23],
  ![0, 1, 2, 3, 12, 13, 14, 15, 4, 5, 6, 7, 8, 9, 10, 11, 16, 19, 17, 18, 20, 22, 23, 21],
  ![0, 1, 2, 3, 12, 14, 15, 13, 4, 7, 5, 6, 16, 18, 19, 17, 20, 21, 22, 23, 8, 11, 9, 10],
  ![0, 1, 2, 3, 12, 15, 13, 14, 4, 6, 7, 5, 20, 23, 21, 22, 8, 10, 11, 9, 16, 17, 18, 19],
  ![0, 1, 2, 3, 16, 17, 18, 19, 4, 5, 6, 7, 20, 21, 22, 23, 12, 15, 13, 14, 8, 10, 11, 9],
  ![0, 1, 2, 3, 16, 18, 19, 17, 4, 7, 5, 6, 12, 14, 15, 13, 8, 9, 10, 11, 20, 23, 21, 22],
  ![0, 1, 2, 3, 16, 19, 17, 18, 4, 6, 7, 5, 8, 11, 9, 10, 20, 22, 23, 21, 12, 13, 14, 15],
  ![0, 1, 2, 3, 20, 21, 22, 23, 4, 5, 6, 7, 16, 17, 18, 19, 8, 11, 9, 10, 12, 14, 15, 13],
  ![0, 1, 2, 3, 20, 22, 23, 21, 4, 7, 5, 6, 8, 10, 11, 9, 12, 13, 14, 15, 16, 19, 17, 18],
  ![0, 1, 2, 3, 20, 23, 21, 22, 4, 6, 7, 5, 12, 15, 13, 14, 16, 18, 19, 17, 8, 9, 10, 11]]

@[expose] def perm4Inv : Fin 15 → Fin 24 → Fin 24 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  ![0, 1, 2, 3, 4, 7, 5, 6, 8, 10, 11, 9, 20, 22, 23, 21, 12, 14, 15, 13, 16, 18, 19, 17],
  ![0, 1, 2, 3, 4, 6, 7, 5, 8, 11, 9, 10, 16, 19, 17, 18, 20, 23, 21, 22, 12, 15, 13, 14],
  ![0, 1, 2, 3, 8, 9, 10, 11, 4, 5, 6, 7, 12, 13, 14, 15, 20, 23, 21, 22, 16, 18, 19, 17],
  ![0, 1, 2, 3, 8, 10, 11, 9, 4, 7, 5, 6, 20, 22, 23, 21, 16, 17, 18, 19, 12, 15, 13, 14],
  ![0, 1, 2, 3, 8, 11, 9, 10, 4, 6, 7, 5, 16, 19, 17, 18, 12, 14, 15, 13, 20, 21, 22, 23],
  ![0, 1, 2, 3, 8, 9, 10, 11, 12, 13, 14, 15, 4, 5, 6, 7, 16, 18, 19, 17, 20, 23, 21, 22],
  ![0, 1, 2, 3, 8, 10, 11, 9, 20, 22, 23, 21, 4, 7, 5, 6, 12, 15, 13, 14, 16, 17, 18, 19],
  ![0, 1, 2, 3, 8, 11, 9, 10, 16, 19, 17, 18, 4, 6, 7, 5, 20, 21, 22, 23, 12, 14, 15, 13],
  ![0, 1, 2, 3, 8, 9, 10, 11, 20, 23, 21, 22, 16, 18, 19, 17, 4, 5, 6, 7, 12, 13, 14, 15],
  ![0, 1, 2, 3, 8, 10, 11, 9, 16, 17, 18, 19, 12, 15, 13, 14, 4, 7, 5, 6, 20, 22, 23, 21],
  ![0, 1, 2, 3, 8, 11, 9, 10, 12, 14, 15, 13, 20, 21, 22, 23, 4, 6, 7, 5, 16, 19, 17, 18],
  ![0, 1, 2, 3, 8, 9, 10, 11, 16, 18, 19, 17, 20, 23, 21, 22, 12, 13, 14, 15, 4, 5, 6, 7],
  ![0, 1, 2, 3, 8, 10, 11, 9, 12, 15, 13, 14, 16, 17, 18, 19, 20, 22, 23, 21, 4, 7, 5, 6],
  ![0, 1, 2, 3, 8, 11, 9, 10, 20, 21, 22, 23, 12, 14, 15, 13, 16, 19, 17, 18, 4, 6, 7, 5]]

@[expose] def perm5Fun : Fin 10 → Fin 24 → Fin 24 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 8, 9, 10, 11, 12, 13, 14, 15],
  ![0, 1, 2, 3, 4, 6, 7, 5, 8, 11, 9, 10, 16, 19, 17, 18, 20, 23, 21, 22, 12, 15, 13, 14],
  ![0, 1, 2, 3, 4, 6, 7, 5, 20, 23, 21, 22, 12, 15, 13, 14, 8, 11, 9, 10, 16, 19, 17, 18],
  ![0, 1, 2, 3, 4, 7, 5, 6, 8, 10, 11, 9, 20, 22, 23, 21, 12, 14, 15, 13, 16, 18, 19, 17],
  ![0, 1, 2, 3, 4, 7, 5, 6, 12, 14, 15, 13, 16, 18, 19, 17, 8, 10, 11, 9, 20, 22, 23, 21],
  ![0, 1, 2, 3, 8, 9, 10, 11, 20, 23, 21, 22, 16, 18, 19, 17, 4, 5, 6, 7, 12, 13, 14, 15],
  ![0, 1, 2, 3, 8, 10, 11, 9, 16, 17, 18, 19, 12, 15, 13, 14, 4, 7, 5, 6, 20, 22, 23, 21],
  ![0, 1, 2, 3, 8, 11, 9, 10, 12, 14, 15, 13, 20, 21, 22, 23, 4, 6, 7, 5, 16, 19, 17, 18],
  ![0, 1, 2, 3, 12, 13, 14, 15, 16, 19, 17, 18, 20, 22, 23, 21, 4, 5, 6, 7, 8, 9, 10, 11]]

@[expose] def perm5Inv : Fin 10 → Fin 24 → Fin 24 := ![
  ![0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23],
  ![0, 1, 2, 3, 4, 5, 6, 7, 16, 17, 18, 19, 20, 21, 22, 23, 8, 9, 10, 11, 12, 13, 14, 15],
  ![0, 1, 2, 3, 4, 7, 5, 6, 8, 10, 11, 9, 20, 22, 23, 21, 12, 14, 15, 13, 16, 18, 19, 17],
  ![0, 1, 2, 3, 4, 7, 5, 6, 16, 18, 19, 17, 12, 14, 15, 13, 20, 22, 23, 21, 8, 10, 11, 9],
  ![0, 1, 2, 3, 4, 6, 7, 5, 8, 11, 9, 10, 16, 19, 17, 18, 20, 23, 21, 22, 12, 15, 13, 14],
  ![0, 1, 2, 3, 4, 6, 7, 5, 16, 19, 17, 18, 8, 11, 9, 10, 12, 15, 13, 14, 20, 23, 21, 22],
  ![0, 1, 2, 3, 16, 17, 18, 19, 4, 5, 6, 7, 20, 21, 22, 23, 12, 15, 13, 14, 8, 10, 11, 9],
  ![0, 1, 2, 3, 16, 18, 19, 17, 4, 7, 5, 6, 12, 14, 15, 13, 8, 9, 10, 11, 20, 23, 21, 22],
  ![0, 1, 2, 3, 16, 19, 17, 18, 4, 6, 7, 5, 8, 11, 9, 10, 20, 22, 23, 21, 12, 13, 14, 15],
  ![0, 1, 2, 3, 16, 17, 18, 19, 20, 21, 22, 23, 4, 5, 6, 7, 8, 10, 11, 9, 12, 15, 13, 14]]

@[expose] def perm4 (c : Fin 15) : Equiv.Perm (Fin 24) where
  toFun := perm4Fun c
  invFun := perm4Inv c
  left_inv := (by decide : ∀ c x, perm4Inv c (perm4Fun c x) = x) c
  right_inv := (by decide : ∀ c x, perm4Fun c (perm4Inv c x) = x) c

@[expose] def perm5 (d : Fin 10) : Equiv.Perm (Fin 24) where
  toFun := perm5Fun d
  invFun := perm5Inv d
  left_inv := (by decide : ∀ d x, perm5Inv d (perm5Fun d x) = x) d
  right_inv := (by decide : ∀ d x, perm5Fun d (perm5Inv d x) = x) d

theorem perm4_mem (c : Fin 15) : perm4 c ∈ AutPerm := by
  fin_cases c <;> exact mem_AutPerm_of_basis (by decide +kernel) (by decide +kernel)

theorem perm5_mem (d : Fin 10) : perm5 d ∈ AutPerm := by
  fin_cases d <;> exact mem_AutPerm_of_basis (by decide +kernel) (by decide +kernel)

theorem perm4_fix : ∀ c : Fin 15, ∀ x : Fin 24, x.val < 4 → perm4 c x = x := by decide

theorem perm5_fix : ∀ d : Fin 10, ∀ x : Fin 24, x.val < 4 → perm5 d x = x := by decide

theorem perm4_smul_A2 : ∀ c : Fin 15, perm4 c • A2 = R4 c := by decide +kernel

theorem perm5_smul_A3 : ∀ d : Fin 10, perm5 d • A3 = R5 d := by decide +kernel

theorem R4_injective : Function.Injective R4 := by
  intro c c' h
  revert c c'
  decide +kernel

theorem R5_injective : Function.Injective R5 := by
  intro d d' h
  revert d d'
  decide +kernel

@[expose] def tetLab : Fin 10 → Finset ℕ :=
  ![{4, 5}, {2, 3}, {3, 5}, {2, 4}, {3, 4}, {2, 5}, {1, 3}, {1, 5}, {1, 4}, {1, 2}]

@[expose] def ev4 : Fin 15 → Fin 2 → Fin 10 := ![![0, 1], ![2, 3], ![4, 5], ![0, 6], ![4, 7],
    ![2, 8], ![0, 9], ![5, 8], ![3, 7], ![1, 7], ![5, 6], ![2, 9], ![1, 8], ![4, 9], ![3, 6]]

theorem R4_subset_R5_iff :
    ∀ (c : Fin 15) (d : Fin 10), R4 c ⊆ R5 d ↔ d = ev4 c 0 ∨ d = ev4 c 1 := by
  decide +kernel

theorem mem_tetLab_iff (d : Fin 10) (k : Fin 5) :
    (k : ℕ) + 1 ∈ tetLab d ↔ ∀ D ∈ R5 d, ¬ ((D : Finset (Fin 24)) ⊆ tetrad k) := by
  have h : ∀ (d : Fin 10) (k : Fin 5), (k : ℕ) + 1 ∈ tetLab d ↔
      (R5 d).filter (fun D : Set.powersetCard (Fin 24) 2 =>
        (D : Finset (Fin 24)) ⊆ tetrad k) = ∅ := by
    decide +kernel
  rw [h, Finset.filter_eq_empty_iff]

abbrev twoSubsets : Finset (Finset ℕ) := (Finset.Icc 1 5).powersetCard 2

theorem tetLab_mem : ∀ d, tetLab d ∈ twoSubsets := by decide

theorem tetLab_injective : Function.Injective tetLab := by
  intro d d' h
  revert d d'
  decide

theorem exists_tetLab : ∀ s ∈ twoSubsets, ∃ d, tetLab d = s := by decide

theorem ev4_disjoint :
    ∀ c, ev4 c 0 ≠ ev4 c 1 ∧ Disjoint (tetLab (ev4 c 0)) (tetLab (ev4 c 1)) := by
  decide

theorem ev4_injective : ∀ c c', ({ev4 c 0, ev4 c 1} : Finset (Fin 10)) = {ev4 c' 0, ev4 c' 1} →
    c = c' := by
  decide

theorem exists_ev4 : ∀ d d' : Fin 10, d ≠ d' → Disjoint (tetLab d) (tetLab d') →
    ∃ c, (ev4 c 0 = d ∧ ev4 c 1 = d') ∨ (ev4 c 0 = d' ∧ ev4 c 1 = d) := by
  decide

end CFSG.Monster.B.TwoA
