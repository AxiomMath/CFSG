module

public import CFSG.Quasithin.Vol2.Ch3Sec3FrontierA

public section

namespace CFSG.Quasithin.H13

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.Blueprint
open CFSG.Quasithin.H13.Ch3Sec3
open CFSG.QuasithinUnique.Vol2Native (A38ForSQTKCat A39ForSQTKCat)

namespace Frontier331

theorem step3_3_20_of_frontier
    (hF : F6.TheoremF618Cat) (hList : Vol2Native.A312ListFactsCat) : Step3_3_20 :=
  step3_3_20_of hF F6.inspF618Rest_holds S3320.inspWalter3320_holds asA21SQTKSection
    Vol2Native.a36ForSQTKCat_proved Vol2Native.a37ForSQTKCat_proved a38Cat
    Vol2Native.a39ForSQTKCat_proved CFSG.Quasithin.ASInputs.AS_A_1_31_holds (a312Cat hList)
    inspA312F618_holds (fun Q _ _ h => (KGAutSyl.factAutSylowA6_holds Q h).autOddNormCent)
    (fun Q _ _ h => (KGAutSyl.factAutSylowA7_holds Q h).autOddNormCent)
    (fun Q _ _ h => (KGAutSyl.factAutSylowM12_holds Q h).autOddNormCent)
    (fun p hp hp3 Q _ _ h => (KGAutSyl.factAutSylowL2Sq_holds p hp hp3 Q h).autOddNormCent)
    KGAutSyl.factAutOddL2pPlus_holds factAutL3Eps_holds KGAutSyl.factAutL2pOuter_holds
    KGAutSyl.factL2pSylowFour_holds factL2pSylowNorm_holds

theorem stmt3_3_20_of_frontier
    (h311 : Theorem311Stmt) (hF : F6.TheoremF618Cat)
    (hList : Vol2Native.A312ListFactsCat) : Stmt3_3_20 :=
  stmt3_3_20_of (stmt3_3_10_of_frontier h311) (step3_3_20_of_frontier hF hList)

end Frontier331

end CFSG.Quasithin.H13
