module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3f4Tc
import CFSG.LocalAnalysis.StandardType.GGLevTwoS3f4CovK

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d
open CFSG.LieType.RootSystem
open scoped Matrix

@[expose] def levTwoS3f4_ws_7_4 : List (List (Fin 5) × List (Fin 5)) :=
  [([], []), ([0], [0]), ([1], [1]), ([2], [2]), ([3], [3]), ([4], [4]), ([0, 1], [0, 1]), ([0, 2], [0, 2]), ([0, 3], [0, 3]), ([0, 4], [0, 4]), ([1, 2], [1, 2]), ([1, 3], [1, 3]), ([1, 4], [1, 4]), ([2, 3], [2, 3]), ([2, 4], [2, 4]), ([3, 4], [3, 4]), ([0, 1, 2], [0, 1]), ([0, 1, 3], [0, 1]), ([0, 1, 4], [0, 1]), ([0, 2, 3], [0, 3]), ([0, 2, 4], [0, 4]), ([0, 3, 4], [0, 3]), ([1, 2, 3], [1, 3]), ([1, 2, 4], [1, 4]), ([1, 3, 4], [1, 3]), ([2, 3, 4], [2, 3]), ([0, 1, 2, 3], [0, 1]), ([0, 1, 2, 4], [0, 1]), ([0, 1, 3, 4], [0, 1]), ([0, 2, 3, 4], [0, 3]), ([1, 2, 3, 4], [1, 3]), ([0, 1, 2, 3, 4], [0, 1])]

@[expose] def levTwoS3f4_ws_14_4 : List (List (Fin 5) × List (Fin 5)) :=
  [([], []), ([0], [0]), ([1], [1]), ([2], [2]), ([3], [3]), ([4], [4]), ([0, 1], [0, 1]), ([0, 2], [0, 2]), ([0, 3], [0, 3]), ([0, 4], [0, 4]), ([1, 2], [1, 2]), ([1, 3], [1, 3]), ([1, 4], [1, 4]), ([2, 3], [2, 3]), ([2, 4], [2, 4]), ([3, 4], [3, 4]), ([0, 1, 2], [1, 2]), ([0, 1, 3], [1, 3]), ([0, 1, 4], [0, 1]), ([0, 2, 3], [2, 3]), ([0, 2, 4], [2, 4]), ([0, 3, 4], [3, 4]), ([1, 2, 3], [1, 2]), ([1, 2, 4], [1, 2]), ([1, 3, 4], [1, 3]), ([2, 3, 4], [2, 3]), ([0, 1, 2, 3], [1, 2]), ([0, 1, 2, 4], [1, 2]), ([0, 1, 3, 4], [1, 3]), ([0, 2, 3, 4], [2, 3]), ([1, 2, 3, 4], [1, 2]), ([0, 1, 2, 3, 4], [1, 2])]

@[expose] def levTwoS3f4_ws_15_4 : List (List (Fin 3) × List (Fin 3)) :=
  [([], []), ([0], [0]), ([1], [1]), ([2], [2]), ([0, 1], [0, 1]), ([0, 2], [0, 2]), ([1, 2], [1, 2]), ([0, 1, 2], [0, 1])]

@[expose] def levTwoS3f4_ws_23_4 : List (List (Fin 5) × List (Fin 5)) :=
  [([], []), ([0], [0]), ([1], [1]), ([2], [2]), ([3], [3]), ([4], [4]), ([0, 1], [0, 1]), ([0, 2], [0, 2]), ([0, 3], [0, 3]), ([0, 4], [0, 4]), ([1, 2], [1, 2]), ([1, 3], [1, 3]), ([1, 4], [1, 4]), ([2, 3], [2, 3]), ([2, 4], [2, 4]), ([3, 4], [3, 4]), ([0, 1, 2], [0, 1]), ([0, 1, 3], [0, 1]), ([0, 1, 4], [0, 1]), ([0, 2, 3], [0, 3]), ([0, 2, 4], [0, 4]), ([0, 3, 4], [0, 3]), ([1, 2, 3], [1, 3]), ([1, 2, 4], [1, 4]), ([1, 3, 4], [1, 3]), ([2, 3, 4], [2, 3]), ([0, 1, 2, 3], [0, 1]), ([0, 1, 2, 4], [0, 1]), ([0, 1, 3, 4], [0, 1]), ([0, 2, 3, 4], [0, 3]), ([1, 2, 3, 4], [1, 3]), ([0, 1, 2, 3, 4], [0, 1])]

@[expose] def levTwoS3f4_ws_28_2 : List (List (Fin 5) × List (Fin 5)) :=
  [([], []), ([0], [0]), ([1], [1]), ([2], [2]), ([3], [3]), ([4], [4]), ([0, 1], [0, 1]), ([0, 2], [0, 2]), ([0, 3], [0, 3]), ([0, 4], [0, 4]), ([1, 2], [1, 2]), ([1, 3], [1, 3]), ([1, 4], [1, 4]), ([2, 3], [2, 3]), ([2, 4], [2, 4]), ([3, 4], [3, 4]), ([0, 1, 2], [0, 1]), ([0, 1, 3], [0, 1]), ([0, 1, 4], [0, 1]), ([0, 2, 3], [0, 2]), ([0, 2, 4], [0, 2]), ([0, 3, 4], [0, 3]), ([1, 2, 3], [1, 2]), ([1, 2, 4], [1, 2]), ([1, 3, 4], [1, 4]), ([2, 3, 4], [2, 4]), ([0, 1, 2, 3], [0, 1]), ([0, 1, 2, 4], [0, 1]), ([0, 1, 3, 4], [0, 1]), ([0, 2, 3, 4], [0, 2]), ([1, 2, 3, 4], [1, 2]), ([0, 1, 2, 3, 4], [0, 1])]

@[expose] def levTwoS3f4_ws_29_2 : List (List (Fin 5) × List (Fin 5)) :=
  [([], []), ([0], [0]), ([1], [1]), ([2], [2]), ([3], [3]), ([4], [4]), ([0, 1], [0, 1]), ([0, 2], [0, 2]), ([0, 3], [0, 3]), ([0, 4], [0, 4]), ([1, 2], [1, 2]), ([1, 3], [1, 3]), ([1, 4], [1, 4]), ([2, 3], [2, 3]), ([2, 4], [2, 4]), ([3, 4], [3, 4]), ([0, 1, 2], [0, 1]), ([0, 1, 3], [0, 1]), ([0, 1, 4], [0, 1]), ([0, 2, 3], [0, 2]), ([0, 2, 4], [0, 2]), ([0, 3, 4], [0, 3]), ([1, 2, 3], [1, 2]), ([1, 2, 4], [1, 2]), ([1, 3, 4], [1, 4]), ([2, 3, 4], [2, 4]), ([0, 1, 2, 3], [0, 1]), ([0, 1, 2, 4], [0, 1]), ([0, 1, 3, 4], [0, 1]), ([0, 2, 3, 4], [0, 2]), ([1, 2, 3, 4], [1, 2]), ([0, 1, 2, 3, 4], [0, 1])]

@[expose] def levTwoS3f4_ws_30_2 : List (List (Fin 3) × List (Fin 3)) :=
  [([], []), ([0], [0]), ([1], [1]), ([2], [2]), ([0, 1], [0, 1]), ([0, 2], [0, 2]), ([1, 2], [1, 2]), ([0, 1, 2], [0, 1])]

@[expose] def levTwoS3f4_ws_30_4 : List (List (Fin 3) × List (Fin 3)) :=
  [([], []), ([0], [0]), ([1], [1]), ([2], [2]), ([0, 1], [0, 1]), ([0, 2], [0, 2]), ([1, 2], [1, 2]), ([0, 1, 2], [0, 1])]


private theorem levTwoS3f4_hall_7_4 :
    ∀ T : Finset (Fin 5), ∃ w ∈ levTwoS3f4_ws_7_4,
      ∀ a : Fin 5, a ∈ w.1 ↔ a ∈ T := by
  decide +kernel

private theorem levTwoS3f4_hpos_7_4 : 0 < (levTwoS3f4_classData_7_4).length := by
  decide +kernel

theorem levTwoS3f4_tcRoot_7_4 :
    TCRoot (isFiniteType_cartan Tag.F4) ↑(levTwoS3f4_patSet 7 4) := by
  have hcl_rep_lt : ∀ a : Fin (levTwoS3f4_classData_7_4).length,
      ((levTwoS3f4_classData_7_4).getD a.val (0, 0)).1 < levTwoS3f4_rootVecs.length := by
    intro a; fin_cases a <;> decide +kernel
  have hrep_notpat : ∀ a : Fin (levTwoS3f4_classData_7_4).length,
      ¬ (levTwoS3f4_patMask 7 4).testBit ((levTwoS3f4_classData_7_4).getD a.val (0, 0)).1 := by
    intro a; fin_cases a <;> decide +kernel
  have hrep_cls : ∀ a : Fin (levTwoS3f4_classData_7_4).length,
      levTwoS3u_clsOf levTwoS3f4_roots levTwoS3f4_classData_7_4 levTwoS3f4_hpos_7_4
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_7_4 a) = a := by
    decide +kernel
  have hcls_orbit : ∀ i : Fin levTwoS3f4_rootVecs.length,
      ¬ (levTwoS3f4_patMask 7 4).testBit i.val →
      ((levTwoS3f4_classData_7_4).getD (levTwoS3u_clsOf levTwoS3f4_roots levTwoS3f4_classData_7_4 levTwoS3f4_hpos_7_4
        (levTwoS3f4_rootVecs.get i)).1 (0, 0)).2.testBit i.val = true := by
    decide +kernel
  have hcl_bfs : ∀ a : Fin (levTwoS3f4_classData_7_4).length,
      levTwoS3b_bfsMask (levTwoS3f4_patPerms 7 4) 300
        [((levTwoS3f4_classData_7_4).getD a.val (0, 0)).1]
        (1 <<< ((levTwoS3f4_classData_7_4).getD a.val (0, 0)).1) =
          ((levTwoS3f4_classData_7_4).getD a.val (0, 0)).2 := by
    intro a
    rw [levTwoS3f4_bfsMask_K]
    fin_cases a <;> decide +kernel
  have hrefl : ∀ a : Fin (levTwoS3f4_classData_7_4).length,
      levTwoS3b_reflectStep (isFiniteType_cartan Tag.F4) levTwoS3f4_rootVecs
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_7_4 a)
        (levTwoS3f4_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_7_4 a)) := by
    intro a
    have hidx48 : (levTwoS3f4_classData_7_4.getD a.val (0, 0)).1 < 48 :=
      Nat.lt_of_lt_of_eq (hcl_rep_lt a) levTwoS3f4_rootVecs_len
    have hidx : (levTwoS3f4_classData_7_4.getD a.val (0, 0)).1 < levTwoS3f4_roots.length := by
      rw [levTwoS3f4_roots_len]; exact hidx48
    rw [levTwoS3f4_reflPerm_repOf a hidx]
    refine levTwoS3f4_reflStep_of_list_check
      (g := levTwoS3f4_roots.getD ((levTwoS3f4_classData_7_4.getD a.val (0, 0)).1) [])
      (by rw [List.getD_eq_getElem _ _ hidx]; exact levTwoS3f4_hlen _ (List.getElem_mem hidx))
      ((levTwoS3f4_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a)) ?_
    exact levTwoS3f4_permOf_step
      (by rw [List.getD_eq_getElem _ _ hidx]; exact levTwoS3f4_hlen _ (List.getElem_mem hidx))
      ((levTwoS3f4_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a))
  refine levTwoS3f4_tcRoot_of_data_ws 7 4 levTwoS3f4_classData_7_4 levTwoS3f4_hpos_7_4 hcl_rep_lt
    hrep_notpat hrep_cls hcls_orbit hcl_bfs hrefl levTwoS3f4_ws_7_4 ?_ ?_
  ·
    exact levTwoS3f4_hws_of_K _ _ _ hcl_rep_lt _ (by decide +kernel)
  ·
    exact levTwoS3f4_hall_7_4

private theorem levTwoS3f4_hall_14_4 :
    ∀ T : Finset (Fin 5), ∃ w ∈ levTwoS3f4_ws_14_4,
      ∀ a : Fin 5, a ∈ w.1 ↔ a ∈ T := by
  decide +kernel

private theorem levTwoS3f4_hpos_14_4 : 0 < (levTwoS3f4_classData_14_4).length := by
  decide +kernel

theorem levTwoS3f4_tcRoot_14_4 :
    TCRoot (isFiniteType_cartan Tag.F4) ↑(levTwoS3f4_patSet 14 4) := by
  have hcl_rep_lt : ∀ a : Fin (levTwoS3f4_classData_14_4).length,
      ((levTwoS3f4_classData_14_4).getD a.val (0, 0)).1 < levTwoS3f4_rootVecs.length := by
    intro a; fin_cases a <;> decide +kernel
  have hrep_notpat : ∀ a : Fin (levTwoS3f4_classData_14_4).length,
      ¬ (levTwoS3f4_patMask 14 4).testBit ((levTwoS3f4_classData_14_4).getD a.val (0, 0)).1 := by
    intro a; fin_cases a <;> decide +kernel
  have hrep_cls : ∀ a : Fin (levTwoS3f4_classData_14_4).length,
      levTwoS3u_clsOf levTwoS3f4_roots levTwoS3f4_classData_14_4 levTwoS3f4_hpos_14_4
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_14_4 a) = a := by
    decide +kernel
  have hcls_orbit : ∀ i : Fin levTwoS3f4_rootVecs.length,
      ¬ (levTwoS3f4_patMask 14 4).testBit i.val →
      ((levTwoS3f4_classData_14_4).getD (levTwoS3u_clsOf levTwoS3f4_roots levTwoS3f4_classData_14_4 levTwoS3f4_hpos_14_4
        (levTwoS3f4_rootVecs.get i)).1 (0, 0)).2.testBit i.val = true := by
    decide +kernel
  have hcl_bfs : ∀ a : Fin (levTwoS3f4_classData_14_4).length,
      levTwoS3b_bfsMask (levTwoS3f4_patPerms 14 4) 300
        [((levTwoS3f4_classData_14_4).getD a.val (0, 0)).1]
        (1 <<< ((levTwoS3f4_classData_14_4).getD a.val (0, 0)).1) =
          ((levTwoS3f4_classData_14_4).getD a.val (0, 0)).2 := by
    intro a
    rw [levTwoS3f4_bfsMask_K]
    fin_cases a <;> decide +kernel
  have hrefl : ∀ a : Fin (levTwoS3f4_classData_14_4).length,
      levTwoS3b_reflectStep (isFiniteType_cartan Tag.F4) levTwoS3f4_rootVecs
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_14_4 a)
        (levTwoS3f4_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_14_4 a)) := by
    intro a
    have hidx48 : (levTwoS3f4_classData_14_4.getD a.val (0, 0)).1 < 48 :=
      Nat.lt_of_lt_of_eq (hcl_rep_lt a) levTwoS3f4_rootVecs_len
    have hidx : (levTwoS3f4_classData_14_4.getD a.val (0, 0)).1 < levTwoS3f4_roots.length := by
      rw [levTwoS3f4_roots_len]; exact hidx48
    rw [levTwoS3f4_reflPerm_repOf a hidx]
    refine levTwoS3f4_reflStep_of_list_check
      (g := levTwoS3f4_roots.getD ((levTwoS3f4_classData_14_4.getD a.val (0, 0)).1) [])
      (by rw [List.getD_eq_getElem _ _ hidx]; exact levTwoS3f4_hlen _ (List.getElem_mem hidx))
      ((levTwoS3f4_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a)) ?_
    exact levTwoS3f4_permOf_step
      (by rw [List.getD_eq_getElem _ _ hidx]; exact levTwoS3f4_hlen _ (List.getElem_mem hidx))
      ((levTwoS3f4_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a))
  refine levTwoS3f4_tcRoot_of_data_ws 14 4 levTwoS3f4_classData_14_4 levTwoS3f4_hpos_14_4 hcl_rep_lt
    hrep_notpat hrep_cls hcls_orbit hcl_bfs hrefl levTwoS3f4_ws_14_4 ?_ ?_
  ·
    exact levTwoS3f4_hws_of_K _ _ _ hcl_rep_lt _ (by decide +kernel)
  ·
    exact levTwoS3f4_hall_14_4


private theorem levTwoS3f4_hall_15_4 :
    ∀ T : Finset (Fin 3), ∃ w ∈ levTwoS3f4_ws_15_4,
      ∀ a : Fin 3, a ∈ w.1 ↔ a ∈ T := by
  decide +kernel

private theorem levTwoS3f4_hpos_15_4 : 0 < (levTwoS3f4_classData_15_4).length := by
  decide +kernel

theorem levTwoS3f4_tcRoot_15_4 :
    TCRoot (isFiniteType_cartan Tag.F4) ↑(levTwoS3f4_patSet 15 4) := by
  have hcl_rep_lt : ∀ a : Fin (levTwoS3f4_classData_15_4).length,
      ((levTwoS3f4_classData_15_4).getD a.val (0, 0)).1 < levTwoS3f4_rootVecs.length := by
    intro a; fin_cases a <;> decide +kernel
  have hrep_notpat : ∀ a : Fin (levTwoS3f4_classData_15_4).length,
      ¬ (levTwoS3f4_patMask 15 4).testBit ((levTwoS3f4_classData_15_4).getD a.val (0, 0)).1 := by
    intro a; fin_cases a <;> decide +kernel
  have hrep_cls : ∀ a : Fin (levTwoS3f4_classData_15_4).length,
      levTwoS3u_clsOf levTwoS3f4_roots levTwoS3f4_classData_15_4 levTwoS3f4_hpos_15_4
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_15_4 a) = a := by
    decide +kernel
  have hcls_orbit : ∀ i : Fin levTwoS3f4_rootVecs.length,
      ¬ (levTwoS3f4_patMask 15 4).testBit i.val →
      ((levTwoS3f4_classData_15_4).getD (levTwoS3u_clsOf levTwoS3f4_roots levTwoS3f4_classData_15_4 levTwoS3f4_hpos_15_4
        (levTwoS3f4_rootVecs.get i)).1 (0, 0)).2.testBit i.val = true := by
    decide +kernel
  have hcl_bfs : ∀ a : Fin (levTwoS3f4_classData_15_4).length,
      levTwoS3b_bfsMask (levTwoS3f4_patPerms 15 4) 300
        [((levTwoS3f4_classData_15_4).getD a.val (0, 0)).1]
        (1 <<< ((levTwoS3f4_classData_15_4).getD a.val (0, 0)).1) =
          ((levTwoS3f4_classData_15_4).getD a.val (0, 0)).2 := by
    intro a
    rw [levTwoS3f4_bfsMask_K]
    fin_cases a <;> decide +kernel
  have hrefl : ∀ a : Fin (levTwoS3f4_classData_15_4).length,
      levTwoS3b_reflectStep (isFiniteType_cartan Tag.F4) levTwoS3f4_rootVecs
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_15_4 a)
        (levTwoS3f4_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_15_4 a)) := by
    intro a
    have hidx48 : (levTwoS3f4_classData_15_4.getD a.val (0, 0)).1 < 48 :=
      Nat.lt_of_lt_of_eq (hcl_rep_lt a) levTwoS3f4_rootVecs_len
    have hidx : (levTwoS3f4_classData_15_4.getD a.val (0, 0)).1 < levTwoS3f4_roots.length := by
      rw [levTwoS3f4_roots_len]; exact hidx48
    rw [levTwoS3f4_reflPerm_repOf a hidx]
    refine levTwoS3f4_reflStep_of_list_check
      (g := levTwoS3f4_roots.getD ((levTwoS3f4_classData_15_4.getD a.val (0, 0)).1) [])
      (by rw [List.getD_eq_getElem _ _ hidx]; exact levTwoS3f4_hlen _ (List.getElem_mem hidx))
      ((levTwoS3f4_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a)) ?_
    exact levTwoS3f4_permOf_step
      (by rw [List.getD_eq_getElem _ _ hidx]; exact levTwoS3f4_hlen _ (List.getElem_mem hidx))
      ((levTwoS3f4_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a))
  refine levTwoS3f4_tcRoot_of_data_ws 15 4 levTwoS3f4_classData_15_4 levTwoS3f4_hpos_15_4 hcl_rep_lt
    hrep_notpat hrep_cls hcls_orbit hcl_bfs hrefl levTwoS3f4_ws_15_4 ?_ ?_
  ·
    exact levTwoS3f4_hws_of_K _ _ _ hcl_rep_lt _ (by decide +kernel)
  ·
    exact levTwoS3f4_hall_15_4


private theorem levTwoS3f4_hall_23_4 :
    ∀ T : Finset (Fin 5), ∃ w ∈ levTwoS3f4_ws_23_4,
      ∀ a : Fin 5, a ∈ w.1 ↔ a ∈ T := by
  decide +kernel

private theorem levTwoS3f4_hpos_23_4 : 0 < (levTwoS3f4_classData_23_4).length := by
  decide +kernel

theorem levTwoS3f4_tcRoot_23_4 :
    TCRoot (isFiniteType_cartan Tag.F4) ↑(levTwoS3f4_patSet 23 4) := by
  have hcl_rep_lt : ∀ a : Fin (levTwoS3f4_classData_23_4).length,
      ((levTwoS3f4_classData_23_4).getD a.val (0, 0)).1 < levTwoS3f4_rootVecs.length := by
    intro a; fin_cases a <;> decide +kernel
  have hrep_notpat : ∀ a : Fin (levTwoS3f4_classData_23_4).length,
      ¬ (levTwoS3f4_patMask 23 4).testBit ((levTwoS3f4_classData_23_4).getD a.val (0, 0)).1 := by
    intro a; fin_cases a <;> decide +kernel
  have hrep_cls : ∀ a : Fin (levTwoS3f4_classData_23_4).length,
      levTwoS3u_clsOf levTwoS3f4_roots levTwoS3f4_classData_23_4 levTwoS3f4_hpos_23_4
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_23_4 a) = a := by
    decide +kernel
  have hcls_orbit : ∀ i : Fin levTwoS3f4_rootVecs.length,
      ¬ (levTwoS3f4_patMask 23 4).testBit i.val →
      ((levTwoS3f4_classData_23_4).getD (levTwoS3u_clsOf levTwoS3f4_roots levTwoS3f4_classData_23_4 levTwoS3f4_hpos_23_4
        (levTwoS3f4_rootVecs.get i)).1 (0, 0)).2.testBit i.val = true := by
    decide +kernel
  have hcl_bfs : ∀ a : Fin (levTwoS3f4_classData_23_4).length,
      levTwoS3b_bfsMask (levTwoS3f4_patPerms 23 4) 300
        [((levTwoS3f4_classData_23_4).getD a.val (0, 0)).1]
        (1 <<< ((levTwoS3f4_classData_23_4).getD a.val (0, 0)).1) =
          ((levTwoS3f4_classData_23_4).getD a.val (0, 0)).2 := by
    intro a
    rw [levTwoS3f4_bfsMask_K]
    fin_cases a <;> decide +kernel
  have hrefl : ∀ a : Fin (levTwoS3f4_classData_23_4).length,
      levTwoS3b_reflectStep (isFiniteType_cartan Tag.F4) levTwoS3f4_rootVecs
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_23_4 a)
        (levTwoS3f4_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_23_4 a)) := by
    intro a
    have hidx48 : (levTwoS3f4_classData_23_4.getD a.val (0, 0)).1 < 48 :=
      Nat.lt_of_lt_of_eq (hcl_rep_lt a) levTwoS3f4_rootVecs_len
    have hidx : (levTwoS3f4_classData_23_4.getD a.val (0, 0)).1 < levTwoS3f4_roots.length := by
      rw [levTwoS3f4_roots_len]; exact hidx48
    rw [levTwoS3f4_reflPerm_repOf a hidx]
    refine levTwoS3f4_reflStep_of_list_check
      (g := levTwoS3f4_roots.getD ((levTwoS3f4_classData_23_4.getD a.val (0, 0)).1) [])
      (by rw [List.getD_eq_getElem _ _ hidx]; exact levTwoS3f4_hlen _ (List.getElem_mem hidx))
      ((levTwoS3f4_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a)) ?_
    exact levTwoS3f4_permOf_step
      (by rw [List.getD_eq_getElem _ _ hidx]; exact levTwoS3f4_hlen _ (List.getElem_mem hidx))
      ((levTwoS3f4_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a))
  refine levTwoS3f4_tcRoot_of_data_ws 23 4 levTwoS3f4_classData_23_4 levTwoS3f4_hpos_23_4 hcl_rep_lt
    hrep_notpat hrep_cls hcls_orbit hcl_bfs hrefl levTwoS3f4_ws_23_4 ?_ ?_
  ·
    exact levTwoS3f4_hws_of_K _ _ _ hcl_rep_lt _ (by decide +kernel)
  ·
    exact levTwoS3f4_hall_23_4


private theorem levTwoS3f4_hall_28_2 :
    ∀ T : Finset (Fin 5), ∃ w ∈ levTwoS3f4_ws_28_2,
      ∀ a : Fin 5, a ∈ w.1 ↔ a ∈ T := by
  decide +kernel

private theorem levTwoS3f4_hpos_28_2 : 0 < (levTwoS3f4_classData_28_2).length := by
  decide +kernel

theorem levTwoS3f4_tcRoot_28_2 :
    TCRoot (isFiniteType_cartan Tag.F4) ↑(levTwoS3f4_patSet 28 2) := by
  have hcl_rep_lt : ∀ a : Fin (levTwoS3f4_classData_28_2).length,
      ((levTwoS3f4_classData_28_2).getD a.val (0, 0)).1 < levTwoS3f4_rootVecs.length := by
    intro a; fin_cases a <;> decide +kernel
  have hrep_notpat : ∀ a : Fin (levTwoS3f4_classData_28_2).length,
      ¬ (levTwoS3f4_patMask 28 2).testBit ((levTwoS3f4_classData_28_2).getD a.val (0, 0)).1 := by
    intro a; fin_cases a <;> decide +kernel
  have hrep_cls : ∀ a : Fin (levTwoS3f4_classData_28_2).length,
      levTwoS3u_clsOf levTwoS3f4_roots levTwoS3f4_classData_28_2 levTwoS3f4_hpos_28_2
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_28_2 a) = a := by
    decide +kernel
  have hcls_orbit : ∀ i : Fin levTwoS3f4_rootVecs.length,
      ¬ (levTwoS3f4_patMask 28 2).testBit i.val →
      ((levTwoS3f4_classData_28_2).getD (levTwoS3u_clsOf levTwoS3f4_roots levTwoS3f4_classData_28_2 levTwoS3f4_hpos_28_2
        (levTwoS3f4_rootVecs.get i)).1 (0, 0)).2.testBit i.val = true := by
    decide +kernel
  have hcl_bfs : ∀ a : Fin (levTwoS3f4_classData_28_2).length,
      levTwoS3b_bfsMask (levTwoS3f4_patPerms 28 2) 300
        [((levTwoS3f4_classData_28_2).getD a.val (0, 0)).1]
        (1 <<< ((levTwoS3f4_classData_28_2).getD a.val (0, 0)).1) =
          ((levTwoS3f4_classData_28_2).getD a.val (0, 0)).2 := by
    intro a
    rw [levTwoS3f4_bfsMask_K]
    fin_cases a <;> decide +kernel
  have hrefl : ∀ a : Fin (levTwoS3f4_classData_28_2).length,
      levTwoS3b_reflectStep (isFiniteType_cartan Tag.F4) levTwoS3f4_rootVecs
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_28_2 a)
        (levTwoS3f4_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_28_2 a)) := by
    intro a
    have hidx48 : (levTwoS3f4_classData_28_2.getD a.val (0, 0)).1 < 48 :=
      Nat.lt_of_lt_of_eq (hcl_rep_lt a) levTwoS3f4_rootVecs_len
    have hidx : (levTwoS3f4_classData_28_2.getD a.val (0, 0)).1 < levTwoS3f4_roots.length := by
      rw [levTwoS3f4_roots_len]; exact hidx48
    rw [levTwoS3f4_reflPerm_repOf a hidx]
    refine levTwoS3f4_reflStep_of_list_check
      (g := levTwoS3f4_roots.getD ((levTwoS3f4_classData_28_2.getD a.val (0, 0)).1) [])
      (by rw [List.getD_eq_getElem _ _ hidx]; exact levTwoS3f4_hlen _ (List.getElem_mem hidx))
      ((levTwoS3f4_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a)) ?_
    exact levTwoS3f4_permOf_step
      (by rw [List.getD_eq_getElem _ _ hidx]; exact levTwoS3f4_hlen _ (List.getElem_mem hidx))
      ((levTwoS3f4_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a))
  refine levTwoS3f4_tcRoot_of_data_ws 28 2 levTwoS3f4_classData_28_2 levTwoS3f4_hpos_28_2 hcl_rep_lt
    hrep_notpat hrep_cls hcls_orbit hcl_bfs hrefl levTwoS3f4_ws_28_2 ?_ ?_
  ·
    exact levTwoS3f4_hws_of_K _ _ _ hcl_rep_lt _ (by decide +kernel)
  ·
    exact levTwoS3f4_hall_28_2


private theorem levTwoS3f4_hall_29_2 :
    ∀ T : Finset (Fin 5), ∃ w ∈ levTwoS3f4_ws_29_2,
      ∀ a : Fin 5, a ∈ w.1 ↔ a ∈ T := by
  decide +kernel

private theorem levTwoS3f4_hpos_29_2 : 0 < (levTwoS3f4_classData_29_2).length := by
  decide +kernel

theorem levTwoS3f4_tcRoot_29_2 :
    TCRoot (isFiniteType_cartan Tag.F4) ↑(levTwoS3f4_patSet 29 2) := by
  have hcl_rep_lt : ∀ a : Fin (levTwoS3f4_classData_29_2).length,
      ((levTwoS3f4_classData_29_2).getD a.val (0, 0)).1 < levTwoS3f4_rootVecs.length := by
    intro a; fin_cases a <;> decide +kernel
  have hrep_notpat : ∀ a : Fin (levTwoS3f4_classData_29_2).length,
      ¬ (levTwoS3f4_patMask 29 2).testBit ((levTwoS3f4_classData_29_2).getD a.val (0, 0)).1 := by
    intro a; fin_cases a <;> decide +kernel
  have hrep_cls : ∀ a : Fin (levTwoS3f4_classData_29_2).length,
      levTwoS3u_clsOf levTwoS3f4_roots levTwoS3f4_classData_29_2 levTwoS3f4_hpos_29_2
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_29_2 a) = a := by
    decide +kernel
  have hcls_orbit : ∀ i : Fin levTwoS3f4_rootVecs.length,
      ¬ (levTwoS3f4_patMask 29 2).testBit i.val →
      ((levTwoS3f4_classData_29_2).getD (levTwoS3u_clsOf levTwoS3f4_roots levTwoS3f4_classData_29_2 levTwoS3f4_hpos_29_2
        (levTwoS3f4_rootVecs.get i)).1 (0, 0)).2.testBit i.val = true := by
    decide +kernel
  have hcl_bfs : ∀ a : Fin (levTwoS3f4_classData_29_2).length,
      levTwoS3b_bfsMask (levTwoS3f4_patPerms 29 2) 300
        [((levTwoS3f4_classData_29_2).getD a.val (0, 0)).1]
        (1 <<< ((levTwoS3f4_classData_29_2).getD a.val (0, 0)).1) =
          ((levTwoS3f4_classData_29_2).getD a.val (0, 0)).2 := by
    intro a
    rw [levTwoS3f4_bfsMask_K]
    fin_cases a <;> decide +kernel
  have hrefl : ∀ a : Fin (levTwoS3f4_classData_29_2).length,
      levTwoS3b_reflectStep (isFiniteType_cartan Tag.F4) levTwoS3f4_rootVecs
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_29_2 a)
        (levTwoS3f4_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_29_2 a)) := by
    intro a
    have hidx48 : (levTwoS3f4_classData_29_2.getD a.val (0, 0)).1 < 48 :=
      Nat.lt_of_lt_of_eq (hcl_rep_lt a) levTwoS3f4_rootVecs_len
    have hidx : (levTwoS3f4_classData_29_2.getD a.val (0, 0)).1 < levTwoS3f4_roots.length := by
      rw [levTwoS3f4_roots_len]; exact hidx48
    rw [levTwoS3f4_reflPerm_repOf a hidx]
    refine levTwoS3f4_reflStep_of_list_check
      (g := levTwoS3f4_roots.getD ((levTwoS3f4_classData_29_2.getD a.val (0, 0)).1) [])
      (by rw [List.getD_eq_getElem _ _ hidx]; exact levTwoS3f4_hlen _ (List.getElem_mem hidx))
      ((levTwoS3f4_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a)) ?_
    exact levTwoS3f4_permOf_step
      (by rw [List.getD_eq_getElem _ _ hidx]; exact levTwoS3f4_hlen _ (List.getElem_mem hidx))
      ((levTwoS3f4_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a))
  refine levTwoS3f4_tcRoot_of_data_ws 29 2 levTwoS3f4_classData_29_2 levTwoS3f4_hpos_29_2 hcl_rep_lt
    hrep_notpat hrep_cls hcls_orbit hcl_bfs hrefl levTwoS3f4_ws_29_2 ?_ ?_
  ·
    exact levTwoS3f4_hws_of_K _ _ _ hcl_rep_lt _ (by decide +kernel)
  ·
    exact levTwoS3f4_hall_29_2


private theorem levTwoS3f4_hall_30_2 :
    ∀ T : Finset (Fin 3), ∃ w ∈ levTwoS3f4_ws_30_2,
      ∀ a : Fin 3, a ∈ w.1 ↔ a ∈ T := by
  decide +kernel

private theorem levTwoS3f4_hpos_30_2 : 0 < (levTwoS3f4_classData_30_2).length := by
  decide +kernel

theorem levTwoS3f4_tcRoot_30_2 :
    TCRoot (isFiniteType_cartan Tag.F4) ↑(levTwoS3f4_patSet 30 2) := by
  have hcl_rep_lt : ∀ a : Fin (levTwoS3f4_classData_30_2).length,
      ((levTwoS3f4_classData_30_2).getD a.val (0, 0)).1 < levTwoS3f4_rootVecs.length := by
    intro a; fin_cases a <;> decide +kernel
  have hrep_notpat : ∀ a : Fin (levTwoS3f4_classData_30_2).length,
      ¬ (levTwoS3f4_patMask 30 2).testBit ((levTwoS3f4_classData_30_2).getD a.val (0, 0)).1 := by
    intro a; fin_cases a <;> decide +kernel
  have hrep_cls : ∀ a : Fin (levTwoS3f4_classData_30_2).length,
      levTwoS3u_clsOf levTwoS3f4_roots levTwoS3f4_classData_30_2 levTwoS3f4_hpos_30_2
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_30_2 a) = a := by
    decide +kernel
  have hcls_orbit : ∀ i : Fin levTwoS3f4_rootVecs.length,
      ¬ (levTwoS3f4_patMask 30 2).testBit i.val →
      ((levTwoS3f4_classData_30_2).getD (levTwoS3u_clsOf levTwoS3f4_roots levTwoS3f4_classData_30_2 levTwoS3f4_hpos_30_2
        (levTwoS3f4_rootVecs.get i)).1 (0, 0)).2.testBit i.val = true := by
    decide +kernel
  have hcl_bfs : ∀ a : Fin (levTwoS3f4_classData_30_2).length,
      levTwoS3b_bfsMask (levTwoS3f4_patPerms 30 2) 300
        [((levTwoS3f4_classData_30_2).getD a.val (0, 0)).1]
        (1 <<< ((levTwoS3f4_classData_30_2).getD a.val (0, 0)).1) =
          ((levTwoS3f4_classData_30_2).getD a.val (0, 0)).2 := by
    intro a
    rw [levTwoS3f4_bfsMask_K]
    fin_cases a <;> decide +kernel
  have hrefl : ∀ a : Fin (levTwoS3f4_classData_30_2).length,
      levTwoS3b_reflectStep (isFiniteType_cartan Tag.F4) levTwoS3f4_rootVecs
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_30_2 a)
        (levTwoS3f4_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_30_2 a)) := by
    intro a
    have hidx48 : (levTwoS3f4_classData_30_2.getD a.val (0, 0)).1 < 48 :=
      Nat.lt_of_lt_of_eq (hcl_rep_lt a) levTwoS3f4_rootVecs_len
    have hidx : (levTwoS3f4_classData_30_2.getD a.val (0, 0)).1 < levTwoS3f4_roots.length := by
      rw [levTwoS3f4_roots_len]; exact hidx48
    rw [levTwoS3f4_reflPerm_repOf a hidx]
    refine levTwoS3f4_reflStep_of_list_check
      (g := levTwoS3f4_roots.getD ((levTwoS3f4_classData_30_2.getD a.val (0, 0)).1) [])
      (by rw [List.getD_eq_getElem _ _ hidx]; exact levTwoS3f4_hlen _ (List.getElem_mem hidx))
      ((levTwoS3f4_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a)) ?_
    exact levTwoS3f4_permOf_step
      (by rw [List.getD_eq_getElem _ _ hidx]; exact levTwoS3f4_hlen _ (List.getElem_mem hidx))
      ((levTwoS3f4_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a))
  refine levTwoS3f4_tcRoot_of_data_ws 30 2 levTwoS3f4_classData_30_2 levTwoS3f4_hpos_30_2 hcl_rep_lt
    hrep_notpat hrep_cls hcls_orbit hcl_bfs hrefl levTwoS3f4_ws_30_2 ?_ ?_
  ·
    exact levTwoS3f4_hws_of_K _ _ _ hcl_rep_lt _ (by decide +kernel)
  ·
    exact levTwoS3f4_hall_30_2


private theorem levTwoS3f4_hall_30_4 :
    ∀ T : Finset (Fin 3), ∃ w ∈ levTwoS3f4_ws_30_4,
      ∀ a : Fin 3, a ∈ w.1 ↔ a ∈ T := by
  decide +kernel

private theorem levTwoS3f4_hpos_30_4 : 0 < (levTwoS3f4_classData_30_4).length := by
  decide +kernel

theorem levTwoS3f4_tcRoot_30_4 :
    TCRoot (isFiniteType_cartan Tag.F4) ↑(levTwoS3f4_patSet 30 4) := by
  have hcl_rep_lt : ∀ a : Fin (levTwoS3f4_classData_30_4).length,
      ((levTwoS3f4_classData_30_4).getD a.val (0, 0)).1 < levTwoS3f4_rootVecs.length := by
    intro a; fin_cases a <;> decide +kernel
  have hrep_notpat : ∀ a : Fin (levTwoS3f4_classData_30_4).length,
      ¬ (levTwoS3f4_patMask 30 4).testBit ((levTwoS3f4_classData_30_4).getD a.val (0, 0)).1 := by
    intro a; fin_cases a <;> decide +kernel
  have hrep_cls : ∀ a : Fin (levTwoS3f4_classData_30_4).length,
      levTwoS3u_clsOf levTwoS3f4_roots levTwoS3f4_classData_30_4 levTwoS3f4_hpos_30_4
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_30_4 a) = a := by
    decide +kernel
  have hcls_orbit : ∀ i : Fin levTwoS3f4_rootVecs.length,
      ¬ (levTwoS3f4_patMask 30 4).testBit i.val →
      ((levTwoS3f4_classData_30_4).getD (levTwoS3u_clsOf levTwoS3f4_roots levTwoS3f4_classData_30_4 levTwoS3f4_hpos_30_4
        (levTwoS3f4_rootVecs.get i)).1 (0, 0)).2.testBit i.val = true := by
    decide +kernel
  have hcl_bfs : ∀ a : Fin (levTwoS3f4_classData_30_4).length,
      levTwoS3b_bfsMask (levTwoS3f4_patPerms 30 4) 300
        [((levTwoS3f4_classData_30_4).getD a.val (0, 0)).1]
        (1 <<< ((levTwoS3f4_classData_30_4).getD a.val (0, 0)).1) =
          ((levTwoS3f4_classData_30_4).getD a.val (0, 0)).2 := by
    intro a
    rw [levTwoS3f4_bfsMask_K]
    fin_cases a <;> decide +kernel
  have hrefl : ∀ a : Fin (levTwoS3f4_classData_30_4).length,
      levTwoS3b_reflectStep (isFiniteType_cartan Tag.F4) levTwoS3f4_rootVecs
        (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_30_4 a)
        (levTwoS3f4_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.F4) levTwoS3f4_roots levTwoS3f4_classData_30_4 a)) := by
    intro a
    have hidx48 : (levTwoS3f4_classData_30_4.getD a.val (0, 0)).1 < 48 :=
      Nat.lt_of_lt_of_eq (hcl_rep_lt a) levTwoS3f4_rootVecs_len
    have hidx : (levTwoS3f4_classData_30_4.getD a.val (0, 0)).1 < levTwoS3f4_roots.length := by
      rw [levTwoS3f4_roots_len]; exact hidx48
    rw [levTwoS3f4_reflPerm_repOf a hidx]
    refine levTwoS3f4_reflStep_of_list_check
      (g := levTwoS3f4_roots.getD ((levTwoS3f4_classData_30_4.getD a.val (0, 0)).1) [])
      (by rw [List.getD_eq_getElem _ _ hidx]; exact levTwoS3f4_hlen _ (List.getElem_mem hidx))
      ((levTwoS3f4_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a)) ?_
    exact levTwoS3f4_permOf_step
      (by rw [List.getD_eq_getElem _ _ hidx]; exact levTwoS3f4_hlen _ (List.getElem_mem hidx))
      ((levTwoS3f4_hRl _).mpr (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a))
  refine levTwoS3f4_tcRoot_of_data_ws 30 4 levTwoS3f4_classData_30_4 levTwoS3f4_hpos_30_4 hcl_rep_lt
    hrep_notpat hrep_cls hcls_orbit hcl_bfs hrefl levTwoS3f4_ws_30_4 ?_ ?_
  ·
    exact levTwoS3f4_hws_of_K _ _ _ hcl_rep_lt _ (by decide +kernel)
  ·
    exact levTwoS3f4_hall_30_4


end CFSG.StandardType.LevTwo
