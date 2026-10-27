module

public import CFSG.RankThree.PartTwo.Sec17.Item1730Conj
public import CFSG.RankThree.PartTwo.KFacts.KS17J2AutOuter
public import CFSG.RankThree.PartTwo.KFacts.KS14Orders
public import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
public import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
public import CFSG.LocalAnalysis.ComponentClassification.J2CoverAut
public import CFSG.Sporadic.J2

public section

namespace CFSG.RankThree.PartTwo

theorem KFacts.ks17J2AutThree :
    KFacts.KS17J2AutThree :=
  KFacts.ks17J2AutThree_of_outer
    CFSG.ComponentClassification.J2Cover.ctuc_j2_full_automorphism_permutation_model.2.2.2.2.2

namespace Sec17

open Sec13

theorem ks17HJConjugacy_of_items
    (h131 : Item131)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) : KFacts.KS17HJConjugacy :=
  ks17HJConjugacy_of h131 Sec13.sporadicModels131 Sec13.slTwoCenter h134 h48 h415
    CFSG.Sporadic.J2.isSimpleGroup_J2 KFacts.KS14.ks17J2NotList KFacts.ks17J2AutThree

theorem step1730Chosen_of_items
    (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h415 : Sec4.Item4_15) : Step1730Chosen :=
  step1730Chosen_of h131 Sec13.sporadicModels131 Sec13.slTwoCenter h134 h48 h415
    CFSG.Sporadic.J2.isSimpleGroup_J2 KFacts.KS14.ks17J2NotList

theorem rank3II_17_30_of_items
    (h1728 : Item1728)
    (h131 : Item131) (h134 : Item134) (h48 : Sec4.Item4_8) (h415 : Sec4.Item4_15) : Item1730 :=
  rank3II_17_30_of_item1728 h1728 h131 Sec13.sporadicModels131 Sec13.slTwoCenter h134 h48 h415
    CFSG.Sporadic.J2.isSimpleGroup_J2 KFacts.KS14.ks17J2NotList KFacts.ks17J2AutThree

end Sec17

end CFSG.RankThree.PartTwo
