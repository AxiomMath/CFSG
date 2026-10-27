module

public import CFSG.Quasithin.Background.F6CatRecogInputs2
public import CFSG.Milestones.CL_LIT_Walter_abelian_Sylow_two_simple

public section

namespace CFSG.Quasithin

namespace F6

theorem walterModelsStatement
    : WalterModelsStatement :=
  fun G _ _ _ hnonab P hP =>
    CFSG.Milestones.cl_lit_walter_abelian_sylow_two_simple_models G hnonab P hP

end F6

end CFSG.Quasithin
