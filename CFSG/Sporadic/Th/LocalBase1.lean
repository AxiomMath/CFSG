
module

public import CFSG.Sporadic.Th.LocalBase

public import CFSG.Sporadic.Th.ChainBase1

@[expose] public section

namespace CFSG.Sporadic.Th

open Native Pointwise

theorem z_mem_L (s : ℕ) : lettersG z0J z1J s ∈ L :=
  lettersG_mem L (Subgroup.subset_closure (Set.mem_insert _ _))
    (Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)) s

theorem xy_mem_H
    (s : ℕ) : lettersG xJ yJ s ∈ H := lettersG_mem H xJ_mem_H yJ_mem_H s

section Local

variable {c : ℕ} (hC : CertFacts c)
include hC

theorem treeData_q0 :
    TreeData nX xJ yJ q0Size 1 (ap q0T.1) (ap q0T.2.2) q0T.2.1 :=
  TreeData.of_treeOK (rep_x hC) (rep_y hC) hC.tables.q0tree

theorem treeData_q1 :
    TreeData nX z0J z1J q1Size 2 (ap q1T.1) (findPt q1T.1) q1T.2 :=
  TreeData.of_treeOK (rep_z0 hC) (rep_z1 hC) hC.tables.q1tree

theorem L_fix_one : ∀ l ∈ L, idx nX l 1 = 1 := by
  intro l hl
  have hz0 : idx nX z0J 1 = 1 := by rw [← rep_z0 hC 1 (one_lt_nX hC)]; exact hC.tables.z01
  have hz1 : idx nX z1J 1 = 1 := by rw [← rep_z1 hC 1 (one_lt_nX hC)]; exact hC.tables.z11
  induction hl using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with rfl | rfl
    · exact hz0
    · exact hz1
  | one => exact idx_one 1
  | mul x y _ _ hx hy => rw [idx_mul, hy, hx]
  | inv x _ hx => rw [← hx, idx_inv_idx, hx]

end Local

end CFSG.Sporadic.Th
