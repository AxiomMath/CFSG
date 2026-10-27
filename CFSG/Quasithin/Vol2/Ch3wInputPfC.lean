module

public import CFSG.Quasithin.EmptyFaithful.E23JShape
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6S66Main
public import CFSG.Quasithin.Vol2.Ch8Sec2L822CovV
public import CFSG.Quasithin.Vol2.Ch3Sec1L319PlusC
public import CFSG.Quasithin.Vol2.Ch3Sec1L319G6Good

public section

namespace CFSG.Quasithin.H13.L319

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.H13
  CFSG.Quasithin.Ch3z

theorem lemma319SixShapeD_of_goodC (hB69 : B69Struct) (hB1 : B69One) (hD125 : D125NonsolvableSQTK)
    (hgood : Lemma319SixGood) : Lemma319SixShapeD := by
  intro G _ _ T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hconcl h6i h6iii L N hstep hnc
  have h : Hyp319 T M M₀ H V := ⟨hbase, hII, hq, hMu, hVH, fun hd => hdual ⟨_, hd⟩⟩
  have hD := h.d11Hyp hT
  have hnff : ¬ IsFFInt M₀ V h.reduced.2.2.1 := fun hff =>
    h.not_qInt_le_one ((isFFInt_iff_qInt_le_one _ _ _).mp hff)
  have hmp : MinParabolic H T (H ⊓ M) := hD.minParabolic hnff
  have hsq : IsSQTKSub H := isSQTKSub_of_inH hK hs hnab h.inH_H
  have hUe := hconcl.elemAbelian
  have hUT : conjClosure V H ≤ T := conjClosure_le_T hD h.le_pCore
  have hRT := h.pCoreOf_le hT
  have hq2 : (2 : WithTop ℚ) ≤ qInt M₀ V h.reduced.2.2.1 := h.q_eq.ge
  have hD125' : D15Proof.D125 H T (conjClosure V H) :=
    d125_of_input hD125 hD hsq h.not_qInt_le_one h.le_pCore hUe
  obtain ⟨A, hA⟩ := hconcl.exists_A
  have hset : Setting H T (H ⊓ M) (conjClosure V H) A :=
    ⟨hmp, hsq, hUT, hUe, hA.1, hA.not_le hRT,
      fun L' N' hs' hnc' => hconcl.count_four A hA L' N' hs' hnc'⟩
  have hrepl : ∀ A' : Subgroup G, IsMaxElemAbelian T A' → ¬ A' ≤ pCoreOf 2 H →
      ∃ D : Subgroup G, Setting H T (H ⊓ M) (conjClosure V H) D ∧ D ≤ A' ⊔ conjClosure V H := by
    intro A' hA' hA'R
    have hA'n : ¬ IsMaxElemAbelian (pCoreOf 2 H) A' := fun hmax => hA'R hmax.1
    obtain ⟨D, hDT, hDn, hDq, hDA⟩ := E23J.exists_quadratic_below hD hnff h.le_pCore hq2 hA' hA'n
    exact ⟨D, E23J.setting_of_quadratic h hT hsq hD125' hconcl.chief hDT hDn hDq, hDA⟩
  obtain ⟨L₀, N₀, hstep₀, hnc₀, χ₀, hχC, a, haA, haH, hχa⟩ :=
    hgood G T hs hnab hK hT M M₀ H V hM hbase hII hq hMu hVH hdual hconcl h6i h6iii A hA
  exact E23J.chiefFactorShape_of_setting' hB69 hB1 hset hrepl hstep₀ hnc₀ hχC haA haH hχa hstep hnc

end CFSG.Quasithin.H13.L319

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.Quasithin.E3 CFSG.Quasithin.H CFSG.Quasithin.ASInputs CFSG.Quasithin
  CFSG.Quasithin.H13.L319

theorem step822M22_of_goodE (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5) (h331 : Stmt3_3_1) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h711n : Stmt7_1_1_normal) (hD15 : D15AsPrintedSQTK)
    (hS316 : AS316SylowNonsolvable) (hD125 : D125NonsolvableSQTK) (hB69 : B69Struct) (hB1 : B69One)
    (hgood : Lemma319SixGood) (hM22 : M22Facts822)
    (h3cov : Res822ThreeCover) (hcJ3 : Res822CoverJ3) (hcov : Res822CoverV)
    (hKz : Res822Kz) : Step822M22 :=
  step822M22_ofV h37 h38 h39 h3228 h325 h331 hC58 h317 h711n hD15 hS316 hD125
    (lemma319SixPlusD_of_shapeC (lemma319SixShapeD_of_goodC hB69 hB1 hD125 hgood))
    (lemma319KerNoThree_of_common (lemma319Common_of_inputs hB69))
    (lemma319NoS5_of_good hB69 hB1 hgood) hM22 h3cov hcJ3 hcov hKz

theorem step822M22_of_residualE (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5) (h331 : Stmt3_3_1) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h711n : Stmt7_1_1_normal) (hD15 : D15AsPrintedSQTK)
    (hS316 : AS316SylowNonsolvable) (hD125 : D125NonsolvableSQTK) (hB69 : B69Struct) (hB1 : B69One)
    (hres : Six6TwoIndex) (hM22 : M22Facts822)
    (h3cov : Res822ThreeCover) (hcJ3 : Res822CoverJ3) (hcov : Res822CoverV)
    (hKz : Res822Kz) : Step822M22 :=
  step822M22_of_goodE h37 h38 h39 h3228 h325 h331 hC58 h317 h711n hD15 hS316 hD125
    hB69 hB1 (lemma319SixGood_of_residual hC58 h317 hB69 hB1 hres) hM22 h3cov hcJ3 hcov hKz

theorem step822M22_of_b69E (h37 : A37ForSQTK) (h38 : A38ForSQTK) (h39 : A39ForSQTK)
    (h3228 : Stmt3_2_2_eight) (h325 : Stmt3_2_5) (h331 : Stmt3_3_1) (hC58 : TheoremC58)
    (h317 : AS317Sylow) (h711n : Stmt7_1_1_normal) (hD15 : D15AsPrintedSQTK)
    (hS316 : AS316SylowNonsolvable) (hD125 : D125NonsolvableSQTK) (hB69 : B69Struct) (hB1 : B69One)
    (hM22 : M22Facts822) (h3cov : Res822ThreeCover) (hcJ3 : Res822CoverJ3) (hcov : Res822CoverV)
    (hKz : Res822Kz) : Step822M22 :=
  step822M22_of_residualE h37 h38 h39 h3228 h325 h331 hC58 h317 h711n hD15 hS316 hD125
    hB69 hB1 (six6TwoIndex_of hB69 hB1) hM22 h3cov hcJ3 hcov hKz

end CFSG.Quasithin.H13
