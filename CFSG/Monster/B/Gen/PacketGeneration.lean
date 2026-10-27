
module

public import CFSG.Monster.B.Gen.PacketGenerationBase

public import CFSG.Monster.B.Gen.HRecords
public import CFSG.Monster.B.Gen.Generation

public section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B

open CFSG.Monster CFSG.Monster.Code CFSG.Monster.Spin CFSG.Monster.SpinLattice
  CFSG.Monster.Griess CFSG.Monster.Visible CFSG.Monster.Generated CFSG.Monster.B.Short
  CFSG.Monster.VisQuot CFSG.Monster.B.Rep4371

theorem closure_selGen :
    Subgroup.closure (Set.range selGen) = ⊤ :=
  closure_eq_top_of_generators ⟨25, selGen_last⟩
    (fun i => ⟨⟨kappa ⟨hElt i, hElt_mem_Cgen i⟩, kappa_mem_Jbar (hElt_mem_Jstar i)⟩,
      Subgroup.subset_closure ⟨⟨i + 1, by omega⟩, selGen_succ i⟩,
      jbarToKv_kappa_hElt i (hElt_mem_Cgen i) (hElt_mem_Jstar i)⟩)
    ⟨⟨_, kappa_rho_mem_Ebar (qElt_mem_centralizer 1)⟩,
      Subgroup.subset_closure ⟨0, selGen_zero⟩, psiBar_qElt_one_ne_one⟩

end CFSG.Monster.B
