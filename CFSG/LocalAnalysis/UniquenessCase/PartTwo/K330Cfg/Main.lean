module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Dispatch
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.ExclAll

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup

theorem K330Cfg.exclAll_of_k33 (hK33 : CFSG.LocalAnalysis.UniquenessCase.UCK.K33) :
    K330Cfg.ExclAll :=
  fun _ _ _ hs => K330Cfg.excl_of_k33 hK33 hs

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
