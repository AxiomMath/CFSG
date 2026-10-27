module

public import CFSG.Quasithin.H13.A7Nat1238Inputs
public import CFSG.Quasithin.H13.A7Nat1238NQ

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin

theorem insp1238NonQ_of
    (h3214 : Stmt3_2_14) : Insp1238NonQ := by
  intro G _ _ T L V hyp ψ e _ hKe K₀ hKeK₀ hK₀ hTK₀ hq hJ hZ
  exact nonQ_core h3214 hyp.simple hyp.nonabelian hyp.qtke hyp.sylow hK₀ hTK₀ hKe hKeK₀ hq hJ hZ

end CFSG.Quasithin.H13.A7
