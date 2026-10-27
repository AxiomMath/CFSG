
module

import all CFSG.Fischer.F4
public import CFSG.Monster.B.TwoA.Unitary.Form

public section

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Fischer Matrix CFSG.Monster.B.Classical.UnitarySix CFSG.LieType.Universal.Unitary

@[expose] def sw35 : Equiv.Perm (Fin 6) := Equiv.swap 3 5

@[expose] def swV (s : V6) : V6 := fun i => s (sw35 i)

theorem sw35_sw35 : ∀ j : Fin 6, sw35 (sw35 j) = j := by decide

theorem sw_rev_sw : ∀ j : Fin 6, sw35 (Fin.rev (sw35 j)) = partner j := by decide

theorem swV_swV (s : V6) : swV (swV s) = s := funext fun j => by
  simp only [swV, sw35_sw35]

theorem herm_swV (s t : V6) : herm (swV s) (swV t) = hU s t := by
  rw [herm, hU_eq_sum, ← Equiv.sum_comp sw35]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [swV, sw35_sw35, sw_rev_sw]

theorem hU_swV (s t : V6) : hU (swV s) (swV t) = herm s t := by
  rw [← herm_swV, swV_swV, swV_swV]

@[expose] def swLin : V6 ≃ₗ[F4] V6 where
  toFun := swV
  invFun := swV
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv := swV_swV
  right_inv := swV_swV

theorem planeRow_zero : ∀ a : Fin 3, planeRow 0 a = Pi.single (lo a) 1 := by decide +kernel

theorem swV_single_lo : ∀ a : Fin 3, swV (Pi.single (lo a) 1) = Pi.single (lo a) 1 := by
  decide +kernel

@[expose] def rowConj (G : Matrix (Fin 6) (Fin 6) F4) : Matrix (Fin 6) (Fin 6) F4 :=
  (Matrix.reindex sw35 sw35 G)ᵀ

theorem vecMul_rowConj (G : Matrix (Fin 6) (Fin 6) F4) (s : V6) :
    s ᵥ* rowConj G = swV (G *ᵥ swV s) := by
  funext j
  simp only [rowConj, vecMul, dotProduct, transpose_apply, reindex_apply, submatrix_apply, swV,
    mulVec]
  rw [← Equiv.sum_comp sw35]
  refine Finset.sum_congr rfl fun m _ => ?_
  have e : sw35.symm = sw35 := Equiv.symm_swap 3 5
  rw [e, sw35_sw35, mul_comm]

theorem det_rowConj (G : Matrix (Fin 6) (Fin 6) F4) : (rowConj G).det = G.det := by
  rw [rowConj, det_transpose, det_reindex_self]

end CFSG.Monster.B.TwoA.Unitary
