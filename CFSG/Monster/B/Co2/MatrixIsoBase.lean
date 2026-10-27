
module

public import CFSG.Monster.B.Co2.MatrixWBase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.Co2

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.SpinLattice CFSG.Monster.ScalarKernel
  CFSG.Monster.Visible CFSG.Monster.VisCert CFSG.Monster.VisQuot CFSG.Certificates
  CFSG.Monster.B.Short

attribute [local irreducible] Native.chainStrong Native.strongInv Native.chainLevels
  Native.chainWords Native.pairPerms Native.chainOrbits Native.permutations Native.vectors
  Native.genRecords Native.vecPos Native.permInv

theorem wAct_inv_wvec_of {k : Kstab v0} {p : Equiv.Perm Ω} (h : ∀ j, wAct v0 k (wvec j) = wvec (p j))
    (j : Ω) : wAct v0 k⁻¹ (wvec j) = wvec (p⁻¹ j) := by
  have h1 := h (p⁻¹ j)
  rw [← Equiv.Perm.mul_apply, mul_inv_cancel, Equiv.Perm.one_apply] at h1
  rw [← h1, wAct_inv_apply]

@[expose] def A0' : Agrp := ⟨A0, Subgroup.subset_closure (Set.mem_insert _ _)⟩

@[expose] def A1' : Agrp := ⟨A1, Subgroup.subset_closure (Set.mem_insert_of_mem _ rfl)⟩

end CFSG.Monster.B.Co2
