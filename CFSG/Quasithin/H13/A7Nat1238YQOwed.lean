module

public import CFSG.Quasithin.H13.A7Nat1238Y
public import CFSG.Quasithin.H13.A7Nat1238Q

public section

namespace CFSG.Quasithin.H13.A7

open CFSG.Open CFSG.Quasithin

theorem insp1238Y_of (h56 : AsB56) :
    Insp1238Y := by
  intro G _ _ T L V hyp ψ e hS h he y hyZ hy4 hTK hKn hKJ
  exact centralizerSection_le_of_b56 h56 hyp h he hS.mem hyZ hy4 hTK hKn hKJ

theorem insp1238Q_of (hTab : Insp1238QTab) (h1222 : Stmt12_2_2) (h331 : Stmt3_3_1)
    (h1233 : Stmt12_3_3) : Insp1238Q := by
  intro G _ _ T L V hyp ψ e hS h he y hyZ hy4 K K₀ hK hKeK hKK₀ hK₀max hK₀f hq hK₀J hV₀
  exact insp1238Q_core hTab h1222 h331 h1233 hyp h he hS hyZ hy4 hK hKeK hKK₀ hK₀max hK₀f hq
    hK₀J hV₀

end CFSG.Quasithin.H13.A7
