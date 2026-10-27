module

public import CFSG.Quasithin.Background.A3StructureFacts
public import CFSG.Milestones.CL_LIT_SQTK_simple_list

public section

namespace CFSG.Quasithin

theorem SQTKGroup.isSQTKCat {X : Type} [Group X] [Finite X] (h : SQTKGroup X) :
    CFSG.SectionRank.IsSQTKCat X :=
  ⟨CFSG.SectionRank.isStronglyQuasithin_iff.mpr h.1, h.2⟩

theorem a23SQTKListFact
    : A23SQTKListFact := by
  intro X _ _ hX H N _ hsimple hnonab
  exact CFSG.Milestones.cl_lit_sqtk_simple_list_section X hX.isSQTKCat H N hnonab

theorem catalogStepFact
    : CatalogStepFact := by
  intro L _ _ hq hS hodd
  exact (CFSG.SectionRank.catalogStepHyp L hq hS.isSQTKCat hodd).1

end CFSG.Quasithin
