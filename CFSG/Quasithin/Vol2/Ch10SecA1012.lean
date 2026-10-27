module

public import CFSG.Quasithin.Vol2.Ch10SecA1012P5
public import CFSG.Quasithin.Vol2.Ch10SecA1012Three
public import CFSG.Quasithin.Vol2.Ch10SecA1012SixBaum

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecA

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.QuasithinUnique
open scoped IsMulCommutative

theorem stmt10_1_2_of
    (hF : Facts10_1) (hFT : FactsTorus) (h37 : Vol2Native.A37ForSQTKCat)
    (h38 : Vol2Native.A38ForSQTKCat) (h322 : TmpL6_3_2_2_two) (h3228 : TmpL6_3_2_2_eight)
    (hshape : Stmt7_0_1_shape) (h42 : AsB42) (h51 : AsB51) (h154 : AsB15Part4)
    (h116 : ASInputs.AS_I_1_6_one) (h3210 : TmpL6_3_2_10_nine) (h331 : Stmt3_3_1)
    (he23 : E2.E23Statement) : Stmt10_1_2 := by
  intro G _ _ T L I hyp
  refine ⟨fun hnot => ?_, thompsonJ_le_T1 h37 h38 h322 h154 hyp,
    inf_centralizer_eq_pCoreOf_of_not_six h37 h38 h3228 hyp,
    fun _ => le_normalizer_inf_centralizer h37 h38 hyp,
    (isUniqueM_normalizer_inf_centralizer h331 h37 h38 hyp).1,
    (isUniqueM_normalizer_inf_centralizer h331 h37 h38 hyp).2,
    fsuCVM_eq_bot hF h37 h38 h322 hshape h42 h51 h154 h116 h3210 hyp,
    part_five hF hFT h37 h38 h322 hshape h42 h51 h154 h116 h3210 hyp,
    fun h12 => ⟨minParabolic_L0T h37 h38 hyp (exists_SL_two_of_cases12 hshape hyp h12),
      baum_le_T1 he23 h37 h38 h322 h154 hshape h3228 hyp h12⟩⟩
  have hnFF : ∀ _ : IsMulCommutative ↥(fsuVM T L I),
      ¬ IsFFModule (V := ↥(fsuVM T L I)) (autOn (fsuL0 T L ⊔ T) (fsuVM T L I)) :=
    fun _ => not_isFFModule_of_not_cases123 hF h37 h38 h322 hshape h42 h51 h154 h116 hyp hnot
  exact ⟨hnFF, thompsonJ_le_centralizer_of_not_isFFModule hyp hnFF⟩

end CFSG.Quasithin.Vol2.Ch10.SecA
