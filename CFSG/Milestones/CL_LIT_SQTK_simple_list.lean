
module

public import CFSG.Milestones.CL_LIT_SQTK_simple_listBase

public import CFSG.LocalAnalysis.SectionRank.SectionAssembly

public section

namespace CFSG.Milestones

open CFSG.Blueprint CFSG.Assembly.LowTwoRank CFSG.SectionRank

theorem cl_lit_sqtk_simple_list_section
    (X : Type) [Group X] [Finite X] (hSQTK : IsSQTKCat X)
    (H : Subgroup X) (N : Subgroup H) [N.Normal] [IsSimpleGroup (H ⧸ N)]
    (hnonab : ∃ a b : H ⧸ N, a * b ≠ b * a) : SQTKSimpleList (H ⧸ N) := by
  obtain ⟨hSQT, hcat⟩ :=
    SectionRank.sqt_catalog_of_simple_section_of_sqtk hSQTK H N hnonab
  exact cl_lit_sqtk_simple_list (H ⧸ N) hnonab hSQT hcat

end CFSG.Milestones
