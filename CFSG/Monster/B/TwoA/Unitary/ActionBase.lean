
module

public import CFSG.Monster.B.TwoA.Unitary.Bridge

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Unitary

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Lifts CFSG.Monster.Visible
  CFSG.Monster.VisQuot CFSG.Monster.VisCert CFSG.Monster.ScalarKernel CFSG.Monster.SpinLattice
  CFSG.Monster.B.Short CFSG.Monster.B.Co2 CFSG.Monster.B.TwoA CFSG.Monster.B.TwoA.Census

theorem decW_one_shiftLeft (t : Fin 22) : decW (1 <<< (t : ℕ)) = qbW t := by
  rw [decW, Finset.sum_eq_single t]
  · rw [bvec_apply, testBit_one_shiftLeft, decide_eq_true rfl]
    simp
  · intro i _ hit
    rw [bvec_apply, testBit_one_shiftLeft, decide_eq_false (fun h => hit (Fin.ext h))]
    simp
  · simp

theorem end_decW
    {f : Module.End (ZMod 2) (Wv v0)} {rows : Array ℕ}
    (h : ∀ t : Fin 22, f (qbW t) = decW rows[(t : ℕ)]!) (c : ℕ) :
    f (decW c) = decW (Native.actD 22 rows c) := by
  rw [Native.actD, xorHom_actGo decW decW_xor, decW_zero, zero_add, decW, map_sum]
  simp only [map_smul, h]
  rw [Finset.sum_range (fun s => if c.testBit s then decW rows[s]! else 0)]
  refine Finset.sum_congr rfl fun t _ => ?_
  rw [bvec_apply]
  split_ifs <;> simp

theorem ainv_n6PermArr_apply (k : Fin 6) (i : Fin 24) :
    (((n6Aut k : Equiv.Perm (Fin 24))⁻¹ i : Fin 24) : ℕ) =
      (ainv n6PermArr[(k : ℕ)]!)[(i : ℕ)]! := by
  have h1 := decode_ainv (n6PermArr_perm k)
  have h2 := decode_apply (PermArr_ainv (n6PermArr_perm k)) i
  rw [h1] at h2
  exact h2

def genRows (k : Fin 17) : Array ℕ := n6RowArr[(k : ℕ)]!

end CFSG.Monster.B.TwoA.Unitary
