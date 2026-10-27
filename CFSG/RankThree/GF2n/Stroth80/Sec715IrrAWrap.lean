module

public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrASteps
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrABridge
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAShape
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrANbr

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank


theorem sec715HasLine_of (hTri : Omega8TrialityStatement) (h310chi : Stroth310ChiStatement)
    (h52a : Stroth52aStatement) (hMp : Sec7CentreMpStatement) (hCRW : Sec7CRWStatement)
    (hZcard : Sec7ZCardStatement) : Sec715HasLineStatement := by
  intro G _ _ M Q Z B _ hc n t r hs hr hp _ Z0 hZ0 _ K _ _ γ M₀ ρ b hS φ₈ hφr hφk e he hTI L₃ L₄
    _ _ _ _ ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ hD
  exact hasLineProp_of h310chi h52a hMp hCRW hZcard hs hr hp hD
    (trialityFacts_of hTri h310chi h52a hS hs hr φ₈ hφr hφk e he hD) hZ0 hTI

theorem sec715NonOrthNbrs_of (h77 : Stroth77Statement) (hAdj : Sec715AdjStatement)
    (hCent : Sec715CentStatement) (h34 : Stroth34Statement) (h311a : Stroth311aStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZV : Sec7ZVStatement)
    (hMp : Sec7CentreMpStatement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement) (hCRW : Sec7CRWStatement)
    (hCommN : Sec7CommNStatement) : Sec715NonOrthNbrsStatement := by
  intro G _ _ M Q Z B _ hc n t r hs hr hp hn Z0 hZ0 hZN K _ _ γ M₀ ρ b hS _ _ _ _ _ hTI
  intros
  exact nonOrthNbrs_of h77 hAdj hCent h34 h311a hZt hZcard hZV hMp hRoot h310chi h51 h52a h52b
    hNO hCRW hCommN hS hs hp hn hZ0 hZN hTI hr

end CFSG.RankThree.GF2n.Stroth80.S715L
