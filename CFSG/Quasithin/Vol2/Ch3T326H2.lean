module

public import CFSG.Quasithin.Vol2.Ch7Stmt326Lt
public import CFSG.Quasithin.Vol2.Ch10T326CBridge

public section

namespace CFSG.Quasithin.H13

open scoped IsMulCommutative

theorem concl326ThreeIv_iff {G : Type} [Group G] (T L I : Subgroup G)
    [IsMulCommutative ↥(fsuVM T L I)] : Concl326ThreeIv T L I ↔ Case3_2_6_iv T L I :=
  Iff.rfl

theorem concl326ThreeC_iff_ch10 {G : Type} [Group G] [Finite G] (T L I : Subgroup G) :
    Concl326ThreeC T L I ↔ Vol2.Ch10.Concl326ThreeC T L I :=
  Iff.rfl

theorem stmt3_2_6Lt_of_C (h326 : Stmt3_2_6C) : Stmt3_2_6Lt :=
  fun G _ _ T L I hfsu hlt => (Vol2.Ch10.tmpL6_3_2_6C_of_stmt3_2_6C h326 G T L I hfsu hlt).2.2

end CFSG.Quasithin.H13
