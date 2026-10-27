module

public import CFSG.YGroups.Y443.Tri.AssemblyLit
public import CFSG.Monster.Tri.OddTypeOrdersGmat

public section

universe u v w

namespace CFSG.Open

open CFSG.Open in
theorem _root_.CFSG.Milestones.fam_m_simplicity :
    IsSimpleGroup MonsterY443Derived :=
  CFSG.YGroups.Y443.fam_m_simplicity_of_th CFSG.Monster.Existence.thInvolutionCentralizersGenerate

end CFSG.Open
