
module

public import CFSG.Sporadic.Th.LocalBase1

public import CFSG.Sporadic.Th.Chain

public section

namespace CFSG.Sporadic.Th

open Native Pointwise

section Local

variable {c : ℕ} (hC : CertFacts c)
include hC

theorem L_fix_two_eq_one :
    ∀ l ∈ L, idx nX l 2 = 2 → l = 1 :=
  levelTwo_stab_eq_one (nX_ge hC) (treeData_q1 hC) (allIn_eq_true.1 hC.tables.levelTwo)
    (rep_z_letters hC) (rep_chain_inv1 hC) chainT_pl1 chainT_pts1 (fun h => eq_of_residue hC h)

theorem H_fix_one_mem_L :
    ∀ h ∈ H, idx nX h 1 = 1 → h ∈ L :=
  levelOne_stab_le L (nX_ge hC) (treeData_q0 hC) (x_sq hC) (y_cube hC) (rep_x hC) (rep_y hC)
    (parAll_eq_true hC.tables.levelOne) (rep_xy_letters hC) (rep_chain_inv0 hC)
    (rep_chain_inv1 hC) chainT_pl0 chainT_pos0 (fun t k => treeElt_mem L t z_mem_L k)
    (fun h => eq_of_residue hC h)

theorem card_H :
    Nat.card H = 634023936 := by
  have hT0 := treeData_q0 hC
  have hT1 := treeData_q1 hC
  let p1 : Fin nX := ⟨1, one_lt_nX hC⟩
  let p2 : Fin nX := ⟨2, two_lt_nX hC⟩
  have h := card_eq_of_stabilizer_chain H L p1 p2 (L_le_H)
    (fun l hl => smul_eq_of_idx l p1 p1 (L_fix_one hC l hl))
    (fun h hh hfix => H_fix_one_mem_L hC h hh (by
      have := idx_val h p1; rw [hfix] at this; exact this))
    (fun l hl hfix => L_fix_two_eq_one hC l hl (by
      have := idx_val l p2; rw [hfix] at this; exact this))
  have h0 : Nat.card (MulAction.orbit H p1) = q0Size := hT0.card_orbit
  have h1 : Nat.card (MulAction.orbit L p2) = q1Size := hT1.card_orbit
  rw [h, h0, h1]
  rfl

end Local

end CFSG.Sporadic.Th
