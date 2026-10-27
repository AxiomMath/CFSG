module

import CFSG.Quasithin.Vol2.Ch3T326GA
public import CFSG.Quasithin.Background.F918K8
public import CFSG.Quasithin.Background.SmithD321SQ
public import CFSG.Quasithin.Background.SmithD321Type
public import CFSG.Quasithin.Background.SmithD39TwoSzHolds
public import CFSG.Quasithin.Vol2.Ch5Sec1L34DiscList

public section

namespace CFSG.Quasithin.RonanD321

open CFSG.Quasithin CFSG.Quasithin.SmithD321 CFSG.Quasithin.SmithD391 CFSG.Open
  CFSG.Assembly.LowTwoRank CFSG.QuasithinUnique

variable {W : Type} [CommGroup W] [Finite W]


set_option linter.unusedVariables false in
theorem qhatStar_le_normalizer
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    (hB : D321Base M Mp T L V t) (hqM : qhatOf M ≤ ((2 : ℚ) : WithTop ℚ))
    (htop : orbSup T V ≠ ⊤) (h3L : 3 ∣ Nat.card ↥L) :
    ∀ A ∈ QhatStar M, A ≤ Subgroup.normalizer (L : Set (MulAut W)) := fun _ hA =>
  H13.T326.qhatStar_le_normalizer_of_d321 asA21SQTKSection asB42_holds
    (a38B42_of Vol2.Ch10.SecA.facts10_1_holds insp5aNonShape_holds) SmithD39Two.d36c_holds
    d37_holds asB56_holds SmithD39Two.d38Top_holds a23SQTKListFact
    H13.simpleThreePrimeSuzukiFact hB htop h3L hA

theorem qhatStar_le_stabSub
    {M Mp T L : Subgroup (MulAut W)} {V : Subgroup W} {t : MulAut W}
    (hB : D321Base M Mp T L V t) (hqM : qhatOf M ≤ ((2 : ℚ) : WithTop ℚ))
    (htop : orbSup T V ≠ ⊤) (h3L : 3 ∣ Nat.card ↥L) :
    ∀ A ∈ QhatStar M, A ≤ stabSub (commV L) := fun A hA _ ha =>
  have hN := qhatStar_le_normalizer hB hqM htop h3L A hA
  mem_stabSub_of_inv (B15P4.map_commV_mem (hN ha)) (B15P4.map_commV_mem (hN (A.inv_mem ha)))

end CFSG.Quasithin.RonanD321
