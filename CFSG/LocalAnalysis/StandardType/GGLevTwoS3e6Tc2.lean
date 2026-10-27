module

public import CFSG.LocalAnalysis.StandardType.GGLevTwoS3e6Tc

public section

namespace CFSG.StandardType.LevTwo

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open CFSG.LocalAnalysis.GLTheoremB.MovingAround.InputsL33d
open CFSG.LieType.RootSystem
open scoped Matrix

@[expose] def levTwoS3e6_e6Ws_29 : List (List (Fin 4) × List (Fin 4)) :=
  [([], []), ([0], [0]), ([1], [1]), ([2], [2]), ([3], [3]), ([0, 1], [0, 1]), ([0, 2], [0, 2]), ([0, 3], [0, 3]), ([1, 2], [1, 2]), ([1, 3], [1, 3]), ([2, 3], [2, 3]), ([0, 1, 2], [0, 1]), ([0, 1, 3], [0, 1]), ([0, 2, 3], [0, 2]), ([1, 2, 3], [1, 2]), ([0, 1, 2, 3], [0, 1])]

@[expose] def levTwoS3e6_e6Ws_30 : List (List (Fin 4) × List (Fin 4)) :=
  [([], []), ([0], [0]), ([1], [1]), ([2], [2]), ([3], [3]), ([0, 1], [0, 1]), ([0, 2], [0, 2]), ([0, 3], [0, 3]), ([1, 2], [1, 2]), ([1, 3], [1, 3]), ([2, 3], [2, 3]), ([0, 1, 2], [0, 1]), ([0, 1, 3], [0, 1]), ([0, 2, 3], [0, 2]), ([1, 2, 3], [1, 2]), ([0, 1, 2, 3], [0, 1])]

@[expose] def levTwoS3e6_e6Ws_53 : List (List (Fin 4) × List (Fin 4)) :=
  [([], []), ([0], [0]), ([1], [1]), ([2], [2]), ([3], [3]), ([0, 1], [0, 1]), ([0, 2], [0, 2]), ([0, 3], [0, 3]), ([1, 2], [1, 2]), ([1, 3], [1, 3]), ([2, 3], [2, 3]), ([0, 1, 2], [0, 1]), ([0, 1, 3], [0, 1]), ([0, 2, 3], [0, 2]), ([1, 2, 3], [1, 2]), ([0, 1, 2, 3], [0, 1])]

@[expose] def levTwoS3e6_e6Ws_58 : List (List (Fin 4) × List (Fin 4)) :=
  [([], []), ([0], [0]), ([1], [1]), ([2], [2]), ([3], [3]), ([0, 1], [0, 1]), ([0, 2], [0, 2]), ([0, 3], [0, 3]), ([1, 2], [1, 2]), ([1, 3], [1, 3]), ([2, 3], [2, 3]), ([0, 1, 2], [0, 1]), ([0, 1, 3], [0, 1]), ([0, 2, 3], [0, 2]), ([1, 2, 3], [1, 2]), ([0, 1, 2, 3], [0, 1])]

@[expose] def levTwoS3e6_e6Ws_60 : List (List (Fin 3) × List (Fin 3)) :=
  [([], []), ([0], [0]), ([1], [1]), ([2], [2]), ([0, 1], [0, 1]), ([0, 2], [0, 2]), ([1, 2], [1, 2]), ([0, 1, 2], [0, 1])]

@[expose] def levTwoS3e6_e6Ws_116 : List (List (Fin 4) × List (Fin 4)) :=
  [([], []), ([0], [0]), ([1], [1]), ([2], [2]), ([3], [3]), ([0, 1], [0, 1]), ([0, 2], [0, 2]), ([0, 3], [0, 3]), ([1, 2], [1, 2]), ([1, 3], [1, 3]), ([2, 3], [2, 3]), ([0, 1, 2], [0, 1]), ([0, 1, 3], [0, 1]), ([0, 2, 3], [0, 3]), ([1, 2, 3], [1, 2]), ([0, 1, 2, 3], [0, 1])]

@[expose] def levTwoS3e6_e6Ws_120 : List (List (Fin 4) × List (Fin 4)) :=
  [([], []), ([0], [0]), ([1], [1]), ([2], [2]), ([3], [3]), ([0, 1], [0, 1]), ([0, 2], [0, 2]), ([0, 3], [0, 3]), ([1, 2], [1, 2]), ([1, 3], [1, 3]), ([2, 3], [2, 3]), ([0, 1, 2], [0, 1]), ([0, 1, 3], [0, 1]), ([0, 2, 3], [0, 3]), ([1, 2, 3], [1, 2]), ([0, 1, 2, 3], [0, 1])]

private theorem levTwoS3e6_reflCheck_29 :
    (List.finRange (levTwoS3e6_e6ClassData_29).length).all (fun a =>
      (List.range 72).all (fun i => decide (
        levTwoS3e6_roots.getD ((levTwoS3e6_permOf (levTwoS3e6_roots.getD
          ((levTwoS3e6_e6ClassData_29.getD a.val (0, 0)).1) [])).getD i 0) [] =
        levTwoS3e6_reflv (levTwoS3e6_roots.getD
          ((levTwoS3e6_e6ClassData_29.getD a.val (0, 0)).1) []) (levTwoS3e6_roots.getD i [])))) = true := by
  decide +kernel

private theorem levTwoS3e6_reflCheck_30 :
    (List.finRange (levTwoS3e6_e6ClassData_30).length).all (fun a =>
      (List.range 72).all (fun i => decide (
        levTwoS3e6_roots.getD ((levTwoS3e6_permOf (levTwoS3e6_roots.getD
          ((levTwoS3e6_e6ClassData_30.getD a.val (0, 0)).1) [])).getD i 0) [] =
        levTwoS3e6_reflv (levTwoS3e6_roots.getD
          ((levTwoS3e6_e6ClassData_30.getD a.val (0, 0)).1) []) (levTwoS3e6_roots.getD i [])))) = true := by
  decide +kernel

private theorem levTwoS3e6_reflCheck_53 :
    (List.finRange (levTwoS3e6_e6ClassData_53).length).all (fun a =>
      (List.range 72).all (fun i => decide (
        levTwoS3e6_roots.getD ((levTwoS3e6_permOf (levTwoS3e6_roots.getD
          ((levTwoS3e6_e6ClassData_53.getD a.val (0, 0)).1) [])).getD i 0) [] =
        levTwoS3e6_reflv (levTwoS3e6_roots.getD
          ((levTwoS3e6_e6ClassData_53.getD a.val (0, 0)).1) []) (levTwoS3e6_roots.getD i [])))) = true := by
  decide +kernel

private theorem levTwoS3e6_reflCheck_58 :
    (List.finRange (levTwoS3e6_e6ClassData_58).length).all (fun a =>
      (List.range 72).all (fun i => decide (
        levTwoS3e6_roots.getD ((levTwoS3e6_permOf (levTwoS3e6_roots.getD
          ((levTwoS3e6_e6ClassData_58.getD a.val (0, 0)).1) [])).getD i 0) [] =
        levTwoS3e6_reflv (levTwoS3e6_roots.getD
          ((levTwoS3e6_e6ClassData_58.getD a.val (0, 0)).1) []) (levTwoS3e6_roots.getD i [])))) = true := by
  decide +kernel

private theorem levTwoS3e6_reflCheck_60 :
    (List.finRange (levTwoS3e6_e6ClassData_60).length).all (fun a =>
      (List.range 72).all (fun i => decide (
        levTwoS3e6_roots.getD ((levTwoS3e6_permOf (levTwoS3e6_roots.getD
          ((levTwoS3e6_e6ClassData_60.getD a.val (0, 0)).1) [])).getD i 0) [] =
        levTwoS3e6_reflv (levTwoS3e6_roots.getD
          ((levTwoS3e6_e6ClassData_60.getD a.val (0, 0)).1) []) (levTwoS3e6_roots.getD i [])))) = true := by
  decide +kernel

private theorem levTwoS3e6_reflCheck_116 :
    (List.finRange (levTwoS3e6_e6ClassData_116).length).all (fun a =>
      (List.range 72).all (fun i => decide (
        levTwoS3e6_roots.getD ((levTwoS3e6_permOf (levTwoS3e6_roots.getD
          ((levTwoS3e6_e6ClassData_116.getD a.val (0, 0)).1) [])).getD i 0) [] =
        levTwoS3e6_reflv (levTwoS3e6_roots.getD
          ((levTwoS3e6_e6ClassData_116.getD a.val (0, 0)).1) []) (levTwoS3e6_roots.getD i [])))) = true := by
  decide +kernel

private theorem levTwoS3e6_reflCheck_120 :
    (List.finRange (levTwoS3e6_e6ClassData_120).length).all (fun a =>
      (List.range 72).all (fun i => decide (
        levTwoS3e6_roots.getD ((levTwoS3e6_permOf (levTwoS3e6_roots.getD
          ((levTwoS3e6_e6ClassData_120.getD a.val (0, 0)).1) [])).getD i 0) [] =
        levTwoS3e6_reflv (levTwoS3e6_roots.getD
          ((levTwoS3e6_e6ClassData_120.getD a.val (0, 0)).1) []) (levTwoS3e6_roots.getD i [])))) = true := by
  decide +kernel

private theorem levTwoS3e6_e6Hws_29 :
    (levTwoS3e6_e6Ws_29).all (fun w => decide (w.2.length ≤ 2) &&
      w.2.all (fun a => decide (a ∈ w.1)) &&
      levTwoS3t_coversWith levTwoS3e6_reflPerm levTwoS3e6_e6ClassData_29
        (levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots levTwoS3e6_e6ClassData_29)
        (levTwoS3e6_e6BasePermsLit 29) [] w.1 w.2) = true := by
  decide +kernel

private theorem levTwoS3e6_e6Hws_30 :
    (levTwoS3e6_e6Ws_30).all (fun w => decide (w.2.length ≤ 2) &&
      w.2.all (fun a => decide (a ∈ w.1)) &&
      levTwoS3t_coversWith levTwoS3e6_reflPerm levTwoS3e6_e6ClassData_30
        (levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots levTwoS3e6_e6ClassData_30)
        (levTwoS3e6_e6BasePermsLit 30) [] w.1 w.2) = true := by
  decide +kernel

private theorem levTwoS3e6_e6Hws_53 :
    (levTwoS3e6_e6Ws_53).all (fun w => decide (w.2.length ≤ 2) &&
      w.2.all (fun a => decide (a ∈ w.1)) &&
      levTwoS3t_coversWith levTwoS3e6_reflPerm levTwoS3e6_e6ClassData_53
        (levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots levTwoS3e6_e6ClassData_53)
        (levTwoS3e6_e6BasePermsLit 53) [] w.1 w.2) = true := by
  decide +kernel

private theorem levTwoS3e6_e6Hws_58 :
    (levTwoS3e6_e6Ws_58).all (fun w => decide (w.2.length ≤ 2) &&
      w.2.all (fun a => decide (a ∈ w.1)) &&
      levTwoS3t_coversWith levTwoS3e6_reflPerm levTwoS3e6_e6ClassData_58
        (levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots levTwoS3e6_e6ClassData_58)
        (levTwoS3e6_e6BasePermsLit 58) [] w.1 w.2) = true := by
  decide +kernel

private theorem levTwoS3e6_e6Hws_60 :
    (levTwoS3e6_e6Ws_60).all (fun w => decide (w.2.length ≤ 2) &&
      w.2.all (fun a => decide (a ∈ w.1)) &&
      levTwoS3t_coversWith levTwoS3e6_reflPerm levTwoS3e6_e6ClassData_60
        (levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots levTwoS3e6_e6ClassData_60)
        (levTwoS3e6_e6BasePermsLit 60) [] w.1 w.2) = true := by
  decide +kernel

private theorem levTwoS3e6_e6Hws_116 :
    (levTwoS3e6_e6Ws_116).all (fun w => decide (w.2.length ≤ 2) &&
      w.2.all (fun a => decide (a ∈ w.1)) &&
      levTwoS3t_coversWith levTwoS3e6_reflPerm levTwoS3e6_e6ClassData_116
        (levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots levTwoS3e6_e6ClassData_116)
        (levTwoS3e6_e6BasePermsLit 116) [] w.1 w.2) = true := by
  decide +kernel

private theorem levTwoS3e6_e6Hws_120 :
    (levTwoS3e6_e6Ws_120).all (fun w => decide (w.2.length ≤ 2) &&
      w.2.all (fun a => decide (a ∈ w.1)) &&
      levTwoS3t_coversWith levTwoS3e6_reflPerm levTwoS3e6_e6ClassData_120
        (levTwoS3u_repOf (n := Tag.rank Tag.E6) levTwoS3e6_roots levTwoS3e6_e6ClassData_120)
        (levTwoS3e6_e6BasePermsLit 120) [] w.1 w.2) = true := by
  decide +kernel

private theorem levTwoS3e6_e6Hall_29 :
    ∀ T : Finset (Fin 4), ∃ w ∈ levTwoS3e6_e6Ws_29,
      ∀ a : Fin 4, a ∈ w.1 ↔ a ∈ T := by
  decide +kernel

private theorem levTwoS3e6_e6Hall_30 :
    ∀ T : Finset (Fin 4), ∃ w ∈ levTwoS3e6_e6Ws_30,
      ∀ a : Fin 4, a ∈ w.1 ↔ a ∈ T := by
  decide +kernel

private theorem levTwoS3e6_e6Hall_53 :
    ∀ T : Finset (Fin 4), ∃ w ∈ levTwoS3e6_e6Ws_53,
      ∀ a : Fin 4, a ∈ w.1 ↔ a ∈ T := by
  decide +kernel

private theorem levTwoS3e6_e6Hall_58 :
    ∀ T : Finset (Fin 4), ∃ w ∈ levTwoS3e6_e6Ws_58,
      ∀ a : Fin 4, a ∈ w.1 ↔ a ∈ T := by
  decide +kernel

private theorem levTwoS3e6_e6Hall_60 :
    ∀ T : Finset (Fin 3), ∃ w ∈ levTwoS3e6_e6Ws_60,
      ∀ a : Fin 3, a ∈ w.1 ↔ a ∈ T := by
  decide +kernel

private theorem levTwoS3e6_e6Hall_116 :
    ∀ T : Finset (Fin 4), ∃ w ∈ levTwoS3e6_e6Ws_116,
      ∀ a : Fin 4, a ∈ w.1 ↔ a ∈ T := by
  decide +kernel

private theorem levTwoS3e6_e6Hall_120 :
    ∀ T : Finset (Fin 4), ∃ w ∈ levTwoS3e6_e6Ws_120,
      ∀ a : Fin 4, a ∈ w.1 ↔ a ∈ T := by
  decide +kernel

theorem levTwoS3e6_tcRoot_29 :
    TCRoot (isFiniteType_cartan Tag.E6) (levTwoS3e6_patSet 29) := by
  have hcl_rep_lt : ∀ a : Fin (levTwoS3e6_e6ClassData_29).length,
      (levTwoS3e6_e6ClassData_29.getD a.val (0, 0)).1 < levTwoS3e6_rootVecs.length := by
    decide +kernel
  refine levTwoS3e6_tcRoot_of_data_ws 29 (by decide +kernel) levTwoS3e6_e6ClassData_29
    (by decide +kernel) hcl_rep_lt (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ levTwoS3e6_e6Ws_29
    levTwoS3e6_e6Hws_29 levTwoS3e6_e6Hall_29
  intro a
  have hidx72 : (levTwoS3e6_e6ClassData_29.getD a.val (0, 0)).1 < 72 :=
    Nat.lt_of_lt_of_eq (hcl_rep_lt a) levTwoS3e6_rootVecs_len
  have hcheckAll := List.all_eq_true.mp levTwoS3e6_reflCheck_29 a
    (by simp)
  have hp : levTwoS3e6_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.E6)
      levTwoS3e6_roots levTwoS3e6_e6ClassData_29 a) =
      levTwoS3e6_permOf (levTwoS3e6_roots.getD
        ((levTwoS3e6_e6ClassData_29.getD a.val (0, 0)).1) []) := by
    simp only [levTwoS3e6_reflPerm, levTwoS3u_repOf]
    rw [levTwoS3u_ofFn_vec (Tag.rank Tag.E6)
      (levTwoS3e6_roots_length hidx72)]
  rw [hp]
  refine levTwoS3e6_reflStep_of_list_check (g := levTwoS3e6_roots.getD
      ((levTwoS3e6_e6ClassData_29.getD a.val (0, 0)).1) [])
    (levTwoS3e6_roots_length hidx72)
    ((levTwoS3e6_rootVecs_isRoot_iff _).mpr
      (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a)) ?_
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp hcheckAll i.val
    (List.mem_range.mpr i.isLt))

theorem levTwoS3e6_tcRoot_30 :
    TCRoot (isFiniteType_cartan Tag.E6) (levTwoS3e6_patSet 30) := by
  have hcl_rep_lt : ∀ a : Fin (levTwoS3e6_e6ClassData_30).length,
      (levTwoS3e6_e6ClassData_30.getD a.val (0, 0)).1 < levTwoS3e6_rootVecs.length := by
    decide +kernel
  refine levTwoS3e6_tcRoot_of_data_ws 30 (by decide +kernel) levTwoS3e6_e6ClassData_30
    (by decide +kernel) hcl_rep_lt (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ levTwoS3e6_e6Ws_30
    levTwoS3e6_e6Hws_30 levTwoS3e6_e6Hall_30
  intro a
  have hidx72 : (levTwoS3e6_e6ClassData_30.getD a.val (0, 0)).1 < 72 :=
    Nat.lt_of_lt_of_eq (hcl_rep_lt a) levTwoS3e6_rootVecs_len
  have hcheckAll := List.all_eq_true.mp levTwoS3e6_reflCheck_30 a
    (by simp)
  have hp : levTwoS3e6_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.E6)
      levTwoS3e6_roots levTwoS3e6_e6ClassData_30 a) =
      levTwoS3e6_permOf (levTwoS3e6_roots.getD
        ((levTwoS3e6_e6ClassData_30.getD a.val (0, 0)).1) []) := by
    simp only [levTwoS3e6_reflPerm, levTwoS3u_repOf]
    rw [levTwoS3u_ofFn_vec (Tag.rank Tag.E6)
      (levTwoS3e6_roots_length hidx72)]
  rw [hp]
  refine levTwoS3e6_reflStep_of_list_check (g := levTwoS3e6_roots.getD
      ((levTwoS3e6_e6ClassData_30.getD a.val (0, 0)).1) [])
    (levTwoS3e6_roots_length hidx72)
    ((levTwoS3e6_rootVecs_isRoot_iff _).mpr
      (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a)) ?_
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp hcheckAll i.val
    (List.mem_range.mpr i.isLt))

theorem levTwoS3e6_tcRoot_53 :
    TCRoot (isFiniteType_cartan Tag.E6) (levTwoS3e6_patSet 53) := by
  have hcl_rep_lt : ∀ a : Fin (levTwoS3e6_e6ClassData_53).length,
      (levTwoS3e6_e6ClassData_53.getD a.val (0, 0)).1 < levTwoS3e6_rootVecs.length := by
    decide +kernel
  refine levTwoS3e6_tcRoot_of_data_ws 53 (by decide +kernel) levTwoS3e6_e6ClassData_53
    (by decide +kernel) hcl_rep_lt (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ levTwoS3e6_e6Ws_53
    levTwoS3e6_e6Hws_53 levTwoS3e6_e6Hall_53
  intro a
  have hidx72 : (levTwoS3e6_e6ClassData_53.getD a.val (0, 0)).1 < 72 :=
    Nat.lt_of_lt_of_eq (hcl_rep_lt a) levTwoS3e6_rootVecs_len
  have hcheckAll := List.all_eq_true.mp levTwoS3e6_reflCheck_53 a
    (by simp)
  have hp : levTwoS3e6_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.E6)
      levTwoS3e6_roots levTwoS3e6_e6ClassData_53 a) =
      levTwoS3e6_permOf (levTwoS3e6_roots.getD
        ((levTwoS3e6_e6ClassData_53.getD a.val (0, 0)).1) []) := by
    simp only [levTwoS3e6_reflPerm, levTwoS3u_repOf]
    rw [levTwoS3u_ofFn_vec (Tag.rank Tag.E6)
      (levTwoS3e6_roots_length hidx72)]
  rw [hp]
  refine levTwoS3e6_reflStep_of_list_check (g := levTwoS3e6_roots.getD
      ((levTwoS3e6_e6ClassData_53.getD a.val (0, 0)).1) [])
    (levTwoS3e6_roots_length hidx72)
    ((levTwoS3e6_rootVecs_isRoot_iff _).mpr
      (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a)) ?_
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp hcheckAll i.val
    (List.mem_range.mpr i.isLt))

theorem levTwoS3e6_tcRoot_58 :
    TCRoot (isFiniteType_cartan Tag.E6) (levTwoS3e6_patSet 58) := by
  have hcl_rep_lt : ∀ a : Fin (levTwoS3e6_e6ClassData_58).length,
      (levTwoS3e6_e6ClassData_58.getD a.val (0, 0)).1 < levTwoS3e6_rootVecs.length := by
    decide +kernel
  refine levTwoS3e6_tcRoot_of_data_ws 58 (by decide +kernel) levTwoS3e6_e6ClassData_58
    (by decide +kernel) hcl_rep_lt (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ levTwoS3e6_e6Ws_58
    levTwoS3e6_e6Hws_58 levTwoS3e6_e6Hall_58
  intro a
  have hidx72 : (levTwoS3e6_e6ClassData_58.getD a.val (0, 0)).1 < 72 :=
    Nat.lt_of_lt_of_eq (hcl_rep_lt a) levTwoS3e6_rootVecs_len
  have hcheckAll := List.all_eq_true.mp levTwoS3e6_reflCheck_58 a
    (by simp)
  have hp : levTwoS3e6_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.E6)
      levTwoS3e6_roots levTwoS3e6_e6ClassData_58 a) =
      levTwoS3e6_permOf (levTwoS3e6_roots.getD
        ((levTwoS3e6_e6ClassData_58.getD a.val (0, 0)).1) []) := by
    simp only [levTwoS3e6_reflPerm, levTwoS3u_repOf]
    rw [levTwoS3u_ofFn_vec (Tag.rank Tag.E6)
      (levTwoS3e6_roots_length hidx72)]
  rw [hp]
  refine levTwoS3e6_reflStep_of_list_check (g := levTwoS3e6_roots.getD
      ((levTwoS3e6_e6ClassData_58.getD a.val (0, 0)).1) [])
    (levTwoS3e6_roots_length hidx72)
    ((levTwoS3e6_rootVecs_isRoot_iff _).mpr
      (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a)) ?_
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp hcheckAll i.val
    (List.mem_range.mpr i.isLt))

theorem levTwoS3e6_tcRoot_60 :
    TCRoot (isFiniteType_cartan Tag.E6) (levTwoS3e6_patSet 60) := by
  have hcl_rep_lt : ∀ a : Fin (levTwoS3e6_e6ClassData_60).length,
      (levTwoS3e6_e6ClassData_60.getD a.val (0, 0)).1 < levTwoS3e6_rootVecs.length := by
    decide +kernel
  refine levTwoS3e6_tcRoot_of_data_ws 60 (by decide +kernel) levTwoS3e6_e6ClassData_60
    (by decide +kernel) hcl_rep_lt (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ levTwoS3e6_e6Ws_60
    levTwoS3e6_e6Hws_60 levTwoS3e6_e6Hall_60
  intro a
  have hidx72 : (levTwoS3e6_e6ClassData_60.getD a.val (0, 0)).1 < 72 :=
    Nat.lt_of_lt_of_eq (hcl_rep_lt a) levTwoS3e6_rootVecs_len
  have hcheckAll := List.all_eq_true.mp levTwoS3e6_reflCheck_60 a
    (by simp)
  have hp : levTwoS3e6_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.E6)
      levTwoS3e6_roots levTwoS3e6_e6ClassData_60 a) =
      levTwoS3e6_permOf (levTwoS3e6_roots.getD
        ((levTwoS3e6_e6ClassData_60.getD a.val (0, 0)).1) []) := by
    simp only [levTwoS3e6_reflPerm, levTwoS3u_repOf]
    rw [levTwoS3u_ofFn_vec (Tag.rank Tag.E6)
      (levTwoS3e6_roots_length hidx72)]
  rw [hp]
  refine levTwoS3e6_reflStep_of_list_check (g := levTwoS3e6_roots.getD
      ((levTwoS3e6_e6ClassData_60.getD a.val (0, 0)).1) [])
    (levTwoS3e6_roots_length hidx72)
    ((levTwoS3e6_rootVecs_isRoot_iff _).mpr
      (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a)) ?_
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp hcheckAll i.val
    (List.mem_range.mpr i.isLt))

theorem levTwoS3e6_tcRoot_116 :
    TCRoot (isFiniteType_cartan Tag.E6) (levTwoS3e6_patSet 116) := by
  have hcl_rep_lt : ∀ a : Fin (levTwoS3e6_e6ClassData_116).length,
      (levTwoS3e6_e6ClassData_116.getD a.val (0, 0)).1 < levTwoS3e6_rootVecs.length := by
    decide +kernel
  refine levTwoS3e6_tcRoot_of_data_ws 116 (by decide +kernel) levTwoS3e6_e6ClassData_116
    (by decide +kernel) hcl_rep_lt (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ levTwoS3e6_e6Ws_116
    levTwoS3e6_e6Hws_116 levTwoS3e6_e6Hall_116
  intro a
  have hidx72 : (levTwoS3e6_e6ClassData_116.getD a.val (0, 0)).1 < 72 :=
    Nat.lt_of_lt_of_eq (hcl_rep_lt a) levTwoS3e6_rootVecs_len
  have hcheckAll := List.all_eq_true.mp levTwoS3e6_reflCheck_116 a
    (by simp)
  have hp : levTwoS3e6_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.E6)
      levTwoS3e6_roots levTwoS3e6_e6ClassData_116 a) =
      levTwoS3e6_permOf (levTwoS3e6_roots.getD
        ((levTwoS3e6_e6ClassData_116.getD a.val (0, 0)).1) []) := by
    simp only [levTwoS3e6_reflPerm, levTwoS3u_repOf]
    rw [levTwoS3u_ofFn_vec (Tag.rank Tag.E6)
      (levTwoS3e6_roots_length hidx72)]
  rw [hp]
  refine levTwoS3e6_reflStep_of_list_check (g := levTwoS3e6_roots.getD
      ((levTwoS3e6_e6ClassData_116.getD a.val (0, 0)).1) [])
    (levTwoS3e6_roots_length hidx72)
    ((levTwoS3e6_rootVecs_isRoot_iff _).mpr
      (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a)) ?_
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp hcheckAll i.val
    (List.mem_range.mpr i.isLt))

theorem levTwoS3e6_tcRoot_120 :
    TCRoot (isFiniteType_cartan Tag.E6) (levTwoS3e6_patSet 120) := by
  have hcl_rep_lt : ∀ a : Fin (levTwoS3e6_e6ClassData_120).length,
      (levTwoS3e6_e6ClassData_120.getD a.val (0, 0)).1 < levTwoS3e6_rootVecs.length := by
    decide +kernel
  refine levTwoS3e6_tcRoot_of_data_ws 120 (by decide +kernel) levTwoS3e6_e6ClassData_120
    (by decide +kernel) hcl_rep_lt (by decide +kernel) (by decide +kernel)
    (by decide +kernel) (by decide +kernel) ?_ levTwoS3e6_e6Ws_120
    levTwoS3e6_e6Hws_120 levTwoS3e6_e6Hall_120
  intro a
  have hidx72 : (levTwoS3e6_e6ClassData_120.getD a.val (0, 0)).1 < 72 :=
    Nat.lt_of_lt_of_eq (hcl_rep_lt a) levTwoS3e6_rootVecs_len
  have hcheckAll := List.all_eq_true.mp levTwoS3e6_reflCheck_120 a
    (by simp)
  have hp : levTwoS3e6_reflPerm (levTwoS3u_repOf (n := Tag.rank Tag.E6)
      levTwoS3e6_roots levTwoS3e6_e6ClassData_120 a) =
      levTwoS3e6_permOf (levTwoS3e6_roots.getD
        ((levTwoS3e6_e6ClassData_120.getD a.val (0, 0)).1) []) := by
    simp only [levTwoS3e6_reflPerm, levTwoS3u_repOf]
    rw [levTwoS3u_ofFn_vec (Tag.rank Tag.E6)
      (levTwoS3e6_roots_length hidx72)]
  rw [hp]
  refine levTwoS3e6_reflStep_of_list_check (g := levTwoS3e6_roots.getD
      ((levTwoS3e6_e6ClassData_120.getD a.val (0, 0)).1) [])
    (levTwoS3e6_roots_length hidx72)
    ((levTwoS3e6_rootVecs_isRoot_iff _).mpr
      (levTwoS3u_rep_mem (fun a => hcl_rep_lt a) a)) ?_
  intro i
  exact of_decide_eq_true (List.all_eq_true.mp hcheckAll i.val
    (List.mem_range.mpr i.isLt))

end CFSG.StandardType.LevTwo
