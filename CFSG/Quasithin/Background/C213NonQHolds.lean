module

public import CFSG.Quasithin.Background.C213NonQ
public import CFSG.Quasithin.H13.VolIA36
public import CFSG.Quasithin.H13.L32NA3SQTK

public section

namespace CFSG.Quasithin.C213NonQ

theorem asc213StepNonQ_holds :
    ∀ (G : Type) [Group G] [Finite G], ASC213StepNonQ G := fun _ _ _ =>
  asc213StepNonQ_of_a3 H13.VolI.a36ForSQTK_holds H13.a3ForSQTK_holds.1 H13.a3ForSQTK_holds.2.2

theorem asc213Step_holds :
    ∀ (G : Type) [Group G] [Finite G], ASC213Step G := fun G _ _ =>
  asc213Step_of_nonQ (asc213StepNonQ_holds G)

end CFSG.Quasithin.C213NonQ
