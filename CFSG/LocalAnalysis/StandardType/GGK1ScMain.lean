module

public import CFSG.LocalAnalysis.StandardType.GGK1ScFinal
public import CFSG.LocalAnalysis.StandardType.GGK1Final

public section

namespace CFSG.StandardType

theorem ggK0MainBS_cl :
    GGK0MainBS GGKacGenericCl GGMultValidCl :=
  ggK0MainBS_cl_of_schur ggK0Schur_cl

theorem ggK0Main_cl :
    GGK0Main GGKacGenericCl GGMultValidCl :=
  ggK0Main_cl_of_schur ggK0Schur_cl

end CFSG.StandardType

end
