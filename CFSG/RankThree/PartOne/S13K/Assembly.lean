module

public import CFSG.RankThree.PartOne.U5LIFT.Rows
public import CFSG.RankThree.PartOne.S13K.Row1
public import CFSG.RankThree.PartOne.S13K.Row1Pair
public import CFSG.RankThree.PartOne.S13K.Sp6Comm

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.Assembly CFSG.RankThree.PartOne
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

theorem kfLiftAll_holds (hGA : CFSG.Open.GriessAllModelsStatement) :
    KFLiftAll :=
  kfLiftAll_of_rows (kfLiftRowOne_holds hGA) (kfLiftRow9_holds hGA) (kfLiftRow10_holds hGA)
    (U5LIFT.kfLiftRow11 hGA) (U5LIFT.kfLiftRow12 hGA)

theorem kfCommSame_of_core (hGA : CFSG.Open.GriessAllModelsStatement)
    (hRow1 : KF123Row 1) (h107 : InSec10Seven) (h109 : InSec10Nine) (h122 : Node122) :
    KFCommSame :=
  kfCommSame_of_rows hRow1 h107 h109 h122 (kfCommRow9_holds hGA) (kfCommRow10 hGA)
    (U5LIFT.kfCommRow11 hGA) (U5LIFT.kfCommRow12 hGA)

theorem kfCommAll_of_core (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (h133 : KF133Two)
    (hDist : KFCommDistinct) (hRow1 : KF123Row 1) (h107 : InSec10Seven) (h109 : InSec10Nine)
    (h122 : Node122) : KFCommAll :=
  kfCommAll_of_inputs hS hRe (kfLiftAll_holds hGA) h133 hDist (kf141a_holds hGA)
    (kfCommSame_of_core hGA hRow1 h107 h109 h122)

theorem kf134Pair_of_core (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (h133 : KF133Two) : KF134Pair :=
  kf134Pair_of_inputs hS hRe (kfLiftAll_holds hGA) h133

theorem kf141c_of_core (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (h133 : KF133Two)
    (hDist : KFCommDistinct) (hRow1 : KF123Row 1) (h107 : InSec10Seven) (h109 : InSec10Nine)
    (h122 : Node122) : KF141c :=
  kf141c_of_commAll (kfCommAll_of_core hGA hS hRe h133 hDist hRow1 h107 h109 h122)

theorem kf141_of_core (hGA : CFSG.Open.GriessAllModelsStatement)
    (hS : SchreierFor InCatalog) (hRe : Sec13Reinst) (h133 : KF133Two)
    (hDist : KFCommDistinct) (hRow1 : KF123Row 1) (h107 : InSec10Seven) (h109 : InSec10Nine)
    (h122 : Node122) : KF141 :=
  kf141_of_parts (kf141a_holds hGA) (kf141b_holds hGA)
    (kf141c_of_core hGA hS hRe h133 hDist hRow1 h107 h109 h122)

theorem kf132At_row11 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF132At 11 := by
  intro G _ _ p A c L E h hF _ _ _ hrow _ hE4 t ht htL
  have hp5 : p = 5 := hrow.1
  subst hp5
  obtain ⟨f, hRM, hall⟩ := U5LIFT.kfAt_row11 hGA h hF (ne_of_card_E h (hE4 (by norm_num))) hrow
  exact ⟨f, f, hRM, rfl, hall t ht htL⟩

theorem kf132At_row12 (hGA : CFSG.Open.GriessAllModelsStatement) :
    KF132At 12 := by
  intro G _ _ p A c L E h hF _ _ _ hrow _ hE4 t ht htL
  have hp5 : p = 5 := hrow.1
  subst hp5
  obtain ⟨f, hRM, hall⟩ := U5LIFT.kfAt_row12 hGA h hF (ne_of_card_E h (hE4 (by norm_num))) hrow
  exact ⟨f, f, hRM, rfl, hall t ht htL⟩

end CFSG.RankThree.PartOne.S13K
