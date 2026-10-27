module

public import CFSG.Quasithin.Vol2.Ch4Sec4Prime443Defs
public import CFSG.Quasithin.Vol2.Ch4Sec4L448
public import CFSG.Quasithin.Vol2.Ch1A3Cat
public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.Vol2NativeLocalNormal
public import CFSG.Quasithin.Vol2.Ch4Sec4L446Orth
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge

public section

namespace CFSG.Quasithin.H13.Ch4

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.H13

theorem stmt4_4_3Orbit'_of_steps (h446 : Lemma446One) (h448 : Lemma448) (hEnd : Lemma443End') :
    Stmt4_4_3Orbit' := by
  rw [stmt4_4_3Orbit_iff']
  intro G _ _ T M L B Tp VB hH
  by_contra hc
  have s' : Setting443' G T M L B Tp VB := ⟨hH, hc⟩
  have s : Setting443 G T M L B Tp VB := setting443_of_prime s'
  have hU := h446 G T M L B Tp VB s
  exact hEnd G T M L B Tp VB s' hU (h448 G T M L B Tp VB s hU)

theorem stmt4_4_3Orbit'_of_inputs
    (h4213 : Stmt4_2_13FF) (h128 : CFSG.Quasithin.ASInputs.AS_A_1_28) (hEnd : Lemma443End') :
    Stmt4_4_3Orbit' :=
  stmt4_4_3Orbit'_of_steps (lemma446One_of h4213 lemma446Mod_holds lemma446ModOrth_holds
    (a37ForSQTK_of_cat CFSG.QuasithinUnique.Vol2Native.a37ForSQTKCat_proved)
    (a39ForSQTK_of_cat CFSG.QuasithinUnique.Vol2Native.a39ForSQTKCat_proved))
    (lemma448_holds h128) hEnd

end CFSG.Quasithin.H13.Ch4
