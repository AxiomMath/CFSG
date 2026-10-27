module

public import CFSG.LocalAnalysis.StandardType.GGRemTableBLExc6
public import CFSG.LocalAnalysis.StandardType.GGTableBThreeTBTwE6Q8

public section

namespace CFSG.Yardstones.M3f9567aba59d

open CFSG CFSG.Assembly CFSG.StandardType CFSG.StandardType.TableBExcTwoTB

theorem exc5r_of_exc4 (p : ℕ) (lab : LargeEvenLabel) (hp : p.Prime)
    (hlab : LargeEvenInLambda2 lab)
    (h : GGRemTableBLExc4Label p lab ∧ ¬ GGTableBTwE6ThreeQ8Label p lab) :
    GGRemTableBLExc5Label p lab ∨ GGTableBTwE6TwoThreeLabel p lab := by
  obtain ⟨h1 | h1, h2⟩ := h
  · have h3 := twE6Three_of_exc4 hp hlab h1
    have hn : lab.n < 3 := by
      by_contra hn
      exact h2 ⟨h3, by omega⟩
    have hn1 : 1 ≤ lab.n := hlab.1
    obtain ⟨ht, rfl, hd⟩ := h3
    refine Or.inr ⟨ht, ?_, rfl⟩
    rcases (show lab.n = 1 ∨ lab.n = 2 by omega) with h1' | h1'
    · exact h1'
    · rw [h1'] at hd
      norm_num at hd
  · exact Or.inl h1

theorem ggRemainderTableBL_of_exc5r
    (hCx : GGTableBCxInputOn GGRemTableBLExc5Label)
    (hMod : GGTableBModuleInputOn GGRemTableBLExc5Label)
    (hAct : GGTableBActionInputOn fun p lab =>
      GGRemTableBLExc5Label p lab ∨ GGTableBTwE6TwoThreeLabel p lab)
    (hTv : GGLTransvectionCenterInputOn GGRemTableBLExc5TvLabel)
    (hLineN : GGLNoInvariantLineInputOn GGRemTableBLExc5Label)
    (hX : GGTwE6InnerDiagBound2LInput) (hY : GGE6InnerDiagBoundThreeInput)
    (hM : GGTwE6TorusModelInput) (hT : GGTwE6NoTransvectionInput)
    (hKT : GGE6DivTorusNbrInput) (hKM : GGE6DivModuleInput) (hKA : GGE6DivActionInput)
    (hKV : GGE6DivTvInput) (hE7 : TableBExcTwoTB.GGE7TwoSCToralInput)
    (hE8 : TableBExcTwoTB.GGE8TwoSCToralInput) (hB : GGTwE6ThreeBstarRankInput)
    (hTN : GGTwE6ThreeTorusNbrInput) (hTM : GGTwE6ThreeModuleInput)
    (hTA : GGTwE6ThreeActionInputQ8) (hTT : GGTwE6ThreeTvInput) :
    GGRemainderTableBL :=
  ggRemainderTableBL_of_exc4
    (ggTableBCxInputOn_of_not_twE6Three hX hB hTN
      (ggTableBCxInputOn_restrict hCx fun p lab hp hlab _ h => exc5_of_exc4 p lab hp hlab h))
    (ggTableBModuleInputOn_of_not_twE6Three hX hB hTM
      (ggTableBModuleInputOn_restrict hMod fun p lab hp hlab _ h => exc5_of_exc4 p lab hp hlab h))
    (ggTableBActionInputOn_of_not_twE6ThreeQ8 hX hB hTA
      (ggTableBActionInputOn_restrict hAct fun p lab hp hlab _ h =>
        exc5r_of_exc4 p lab hp hlab h))
    hX hY hM hT
    (ggLTransvectionCenterInputOn_of_not_twE6Three hB hTT
      (ggLTransvectionCenterInputOn_restrict hTv fun p lab hp hlab _ h =>
        exc5Tv_of_exc4Tv p lab hp hlab h))
    (ggLNoInvariantLineInputOn_of_not_twE6Three hB hTM
      (ggLNoInvariantLineInputOn_restrict hLineN fun p lab hp hlab _ h =>
        exc5_of_exc4 p lab hp hlab h))
    hKT hKM hKA hKV hE7 hE8

theorem ggRemainderTableBL_of_exc6r
    (hCx : GGTableBCxInputOn GGRemTableBLExc5Label)
    (hMod : GGTableBModuleInputOn GGRemTableBLExc5Label)
    (hAct : GGTableBActionInputOn fun p lab =>
      GGRemTableBLExc5Label p lab ∨ GGTableBTwE6TwoThreeLabel p lab)
    (hTv : GGLTransvectionCenterInputOn GGRemTableBLExc5Label)
    (hLineN : GGLNoInvariantLineInputOn GGRemTableBLExc5Label)
    (hX : GGTwE6InnerDiagBound2LInput) (hY : GGE6InnerDiagBoundThreeInput)
    (hM : GGTwE6TorusModelInput) (hT : GGTwE6NoTransvectionInput)
    (hKT : GGE6DivTorusNbrInput) (hKM : GGE6DivModuleInput) (hKA : GGE6DivActionInput)
    (hKV : GGE6DivTvInput) (hE7 : GGE7TwoSCToralInput) (hE8 : GGE8TwoSCToralInput)
    (hN7 : GGE7TwoNormIsometryInput) (hN8 : GGE8TwoNormIsometryInput)
    (hB : GGTwE6ThreeBstarRankInput) (hTN : GGTwE6ThreeTorusNbrInput)
    (hTM : GGTwE6ThreeModuleInput) (hTA : GGTwE6ThreeActionInputQ8) (hTT : GGTwE6ThreeTvInput) :
    GGRemainderTableBL :=
  ggRemainderTableBL_of_exc5r hCx hMod hAct
    (ggLTransvectionCenterInputOn_of_not_e7e8TwoThree_tv hE7 hN7 hE8 hN8
      (CorFourTwoVacMore.lTransvectionCenterInputOn_mono
        (fun p lab h => exc5_of_exc5Tv p lab h) hTv))
    hLineN hX hY hM hT hKT hKM hKA hKV hE7 hE8 hB hTN hTM hTA hTT

end CFSG.Yardstones.M3f9567aba59d
