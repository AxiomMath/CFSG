module

public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAMatActProp
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrARoot
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrASameLine
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrAFixV
public import CFSG.Quasithin.H13.L32NSp4Over
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrABridge
public import CFSG.RankThree.GF2n.Stroth80.Sec715IrrASteps

public section

namespace CFSG.RankThree.GF2n.Stroth80.S715L

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank

theorem sec715RootElt_of (hTri : Omega8TrialityStatement) (hEnd : Omega8EndScalarStatement)
    (h34 : Stroth34Statement) (hRoot : Stroth310RootStatement)
    (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement) (h52a : Stroth52aStatement)
    (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement) (hA : Sec7AExistsStatement)
    (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement) (hZV : Sec7ZVStatement)
    (hCommN : Sec7CommNStatement) (hY : Sec713YStatement) (hCent : Sec715CentStatement)
    (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement) : Sec715RootEltStatement := by
  intro G _ _ M Q Z B _ hc n t r hs hr hp _ Z0 hZ0 hZN K _ _ γ M₀ ρ b hS φ₈ hφr hφk e he hTI L₃
    L₄ _ _ _ _ ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ hD
  have hSΔ : ∀ F ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      F = S714.delta hS t g (S714.mem_bar_H0_of_CN hg) := fun F hF =>
    (mem_deltaSub_iff h34 hRoot h310chi h51 h52a h52b hNO hZcard hCRW hMp hS hs hr).mp hF
  exact hD.rootEltProp_of h34 h310chi h51 h52a hA hZt hZcard hMp hZV hCommN hY hCent hCRW hMp hs
    hr hp (trialityFacts_of hTri h310chi h52a hS hs hr φ₈ hφr hφk e he hD) hZ0 hZN hTI hSΔ
    (matActProp_of h310chi h52a hZt hZcard hS hs hr hZ0 hSΔ hD
      (endScalar4_of hEnd h310chi h52a hS hs hr φ₈ hφr hφk hD))
    (fun _ hzH hzV => mem_NormH0_of_fixes h310chi h52a hMp hS hs hr hZ0 hzH hzV)

theorem sec715SameLineOrth_of (hTri : Omega8TrialityStatement)
    (hEnd : Omega8EndScalarStatement) (h34 : Stroth34Statement)
    (hRoot : Stroth310RootStatement) (h310chi : Stroth310ChiStatement) (h51 : Stroth51Statement)
    (h52a : Stroth52aStatement) (h52b : Stroth52bStatement) (hNO : Sec7NOrderStatement)
    (hA : Sec7AExistsStatement) (hZt : Sec7ZtStatement) (hZcard : Sec7ZCardStatement)
    (hZV : Sec7ZVStatement) (hCommN : Sec7CommNStatement) (hY : Sec713YStatement)
    (hCent : Sec715CentStatement) (hCRW : Sec7CRWStatement) (hMp : Sec7CentreMpStatement) :
    Sec715SameLineOrthStatement := by
  intro G _ _ M Q Z B _ hc n t r hs hr hp _ Z0 hZ0 hZN K _ _ γ M₀ ρ b hS φ₈ hφr hφk e he hTI L₃
    L₄ _ _ _ _ ρ₃ ρ₄ eM eN μ q₃ q₄ φ ψ κ hD
  have hSΔ : ∀ F ∈ deltaSub hS t, ∃ (g : Mbar M Q) (hg : g ∈ bar M Q (hc.CN t)),
      F = S714.delta hS t g (S714.mem_bar_H0_of_CN hg) := fun F hF =>
    (mem_deltaSub_iff h34 hRoot h310chi h51 h52a h52b hNO hZcard hCRW hMp hS hs hr).mp hF
  have T := trialityFacts_of hTri h310chi h52a hS hs hr φ₈ hφr hφk e he hD
  exact sameLineOrthProp_of h310chi h52a hMp hCRW hZcard hs hr hp hD T hZ0 hTI
    (hD.isotropic_of_symNbr h34 h310chi h51 h52a hA hZt hZcard hMp hZV hCommN hY hCent hCRW hMp
      hs hr hp T hZ0 hZN hTI hSΔ
      (matActProp_of h310chi h52a hZt hZcard hS hs hr hZ0 hSΔ hD
        (endScalar4_of hEnd h310chi h52a hS hs hr φ₈ hφr hφk hD))
      (fun _ hzH hzV => mem_NormH0_of_fixes h310chi h52a hMp hS hs hr hZ0 hzH hzV))

end CFSG.RankThree.GF2n.Stroth80.S715L
