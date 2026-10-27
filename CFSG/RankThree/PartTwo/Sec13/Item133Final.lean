module

public import CFSG.RankThree.PartTwo.Sec13.Item133
import CFSG.RankThree.PartTwo.Sec13.Item13Final
import CFSG.RankThree.PartTwo.Sec13.Item13NotSLTwo
import CFSG.RankThree.PartTwo.Sec13.Item13SetupAt
import CFSG.RankThree.PartTwo.Sec13.Item13SLTwo
import CFSG.RankThree.PartTwo.Sec13.Item13Sporadic
public import Certificates.Certificate8171
public import Certificates.Certificate8172
public import Certificates.Certificate3029
public import Certificates.Certificate3086
public import Certificates.Certificate3139
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField

public section

namespace CFSG.RankThree.PartTwo.Sec13

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

theorem rank3II_13_3_of (h131 : Item131) (h422 : Sec4.Item4_22) (h45 : Sec4.Item4_5) :
    Item133 :=
  rank3II_13_3_of_inputs h131 (rank3II_13_2_of h131 h422 h45) sporadicModels131 slTwoCenter
    (item13SetupAt_of h422 h45) (notSLTwoOfHypT_of h131 sporadicModels131)

end CFSG.RankThree.PartTwo.Sec13
