module

public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4M
public import CFSG.Quasithin.Vol2.Ch4Sec4G443J4GE
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge

public section

namespace CFSG.Quasithin.H13.Ch4.G443J4

open CFSG.Open CFSG.Quasithin CFSG.QuasithinUnique

section Gap

theorem gap443J4_of' (h39 : A39ForSQTK) (hA21 : AsA21SQTKSection) (hLoc : KG443J4Loc)
    (hGenL : KG443J4GenL52) : E443.Gap443J4 :=
  gap443J4_of h39 hA21 hLoc kg443J4GenM24_holds hGenL

end Gap

end CFSG.Quasithin.H13.Ch4.G443J4
