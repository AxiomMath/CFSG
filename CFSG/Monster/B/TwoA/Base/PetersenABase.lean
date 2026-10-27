
module

public import CFSG.Monster.B.TwoA.Base.ConjSub
public import CFSG.Monster.B.TwoA.Base.Par45ABase

@[expose] public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.B CFSG.Monster.VisQuot CFSG.Monster.ScalarKernel CFSG.Monster.B.Co2
  CFSG.Monster.Lifts CFSG.Monster.VisCert

open scoped IsMulCommutative

@[expose] def X4 : Set (Subgroup Dfull) := {F | (∃ g ∈ Shat, F = conjSub g E4) ∧ E3 ≤ F}

@[expose] def X5 : Set (Subgroup Dfull) := {F | (∃ g ∈ Shat, F = conjSub g E5) ∧ E3 ≤ F}

theorem subgroupOf_K3_eq (H : Subgroup Dfull) : H.subgroupOf K3 = (K3 ⊓ H).subgroupOf K3 := by
  ext k
  rw [Subgroup.mem_subgroupOf, Subgroup.mem_subgroupOf, Subgroup.mem_inf]
  exact ⟨fun h => ⟨k.2, h⟩, fun h => h.2⟩

theorem subOf_mono
    {E F F' : Subgroup Dfull} [CFSG.IsElementaryAbelian 2 E] (h : F ≤ F') :
    subOf E F ≤ subOf E F' := fun _ hx => h hx

end CFSG.Monster.B.TwoA
