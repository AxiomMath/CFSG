module

public import CFSG.RankThree.PartTwo.Sec13.Item137ProofInvert
public import CFSG.RankThree.PartTwo.Sec13.Item137Proof
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item414Local
import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
import CFSG.RankThree.PartTwo.KFacts.KS18M12Proof

public section

namespace CFSG.RankThree.PartTwo.Sec13

theorem item137Move_of
    (h131 : Item131) (h133 : Item133) (h134 : Item134) (h48 : Sec4.Item4_8)
    (h13S : Sec17.Item13Setup) (hPGL : Item137InvertPGL) : Item137Move :=
  item137Move_of_core_inputs h131 sporadicModels131 Sec4.Sporadic.rank3II_4_14_local
    (item137Core_of h131 h133 h13S sporadicModels131 Sec4.Sporadic.rank3II_4_14_local
      (item137Invert_of h131 h134 h48 sporadicModels131 Sec4.Sporadic.rank3II_4_14_local
        Sec4.Sporadic.rank3II_4_15 KFacts.ks18M12 hPGL))

theorem item137_of_items
    (h131 : Item131) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) (h133 : Item133)
    (h134 : Item134) (h48 : Sec4.Item4_8) (h13S : Sec17.Item13Setup)
    (hPGL : Item137InvertPGL) : Item137 :=
  item137_of h131 h422 h45 h13S (item137Move_of h131 h133 h134 h48 h13S hPGL)

end CFSG.RankThree.PartTwo.Sec13
