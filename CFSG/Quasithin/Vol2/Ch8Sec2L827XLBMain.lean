module

public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBModule
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XLBCaseBGlue
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XAssembly
public import CFSG.Quasithin.Vol2.Ch8Sec2L827XVCard

public section

namespace CFSG.Quasithin.H13.L827X

open CFSG.Quasithin.H13.L827X.LBDefs

theorem xiChiefLowerBound_holds : XiChiefLowerBound := by
  intro G _ _ T X K U V X₁ W₀ W₁ v hT hX hCT hK hXK hNKX hKs hXC hTU hUV hVT hTV hVe hX₁lt
    hX₁X hTX₁ hvV hvX₁ hUW₀ hW₀W₁ hW₁R hΛW₀ hΛW₁ hchief hWX
  have h : XiHyp T X K U V X₁ W₀ W₁ v :=
    ⟨hT, hX, hCT, hK, hXK, hNKX, hKs, hXC, hTU, hUV, hVT, hTV, hVe, hX₁lt, hX₁X, hTX₁,
      hvV, hvX₁, hUW₀, hW₀W₁, hW₁R, hΛW₀, hΛW₁, hchief, hWX⟩
  obtain ⟨W, _, _, _, τ, π, hR⟩ := LBModule.chief_rep_exists h
  have hvΛ : v ∈ CFSG.Quasithin.conjClosure K T ⊔ T :=
    (le_sup_right : T ≤ CFSG.Quasithin.conjClosure K T ⊔ T) (hVT hvV)
  rw [LBModule.mQuot_eq_finrank_range h hR hvΛ]
  by_cases hB : ⁅W₁, XiY X⁆ ≤ W₀
  · exact LBCaseBGlue.caseB_glue h hR hvΛ hB
  · exact LBCaseAG.caseA_glue h hR hvΛ hB

theorem step827Xi_holds
    (hmod : StmtFSUModule) (h711n : Stmt7_1_1_normal) (h825 : Stmt8_2_5) : Step827Xi :=
  step827Xi_of hmod h711n h825 stmt827VCard_holds xiChiefLowerBound_holds

end CFSG.Quasithin.H13.L827X

end
