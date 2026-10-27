module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K462
public import CFSG.LocalAnalysis.UniquenessCase.UC1K46Quasi
public import CFSG.LocalAnalysis.UniquenessCase.UC1K46InspEven
public import CFSG.LocalAnalysis.UniquenessCase.UC1K46InspJ1Two
public import CFSG.LocalAnalysis.UniquenessCase.UC1K46InspU3
public import CFSG.LocalAnalysis.UniquenessCase.UC1K46Cover

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UCK


theorem k462_of_open
    (h45 : K45Odd) : K462 :=
  k462_of_named h45 quasisimpleOfCentral_holds k46Quasisimple_holds insp2L2_holds insp2L3_holds
    insp2J1_holds

theorem k46semireg_of_open
    (h45 : K45Odd) (hZ : ZassenhausPerfect) : K46Semireg :=
  k46semireg_of_named h45 quasisimpleOfCentral_holds k46Quasisimple_holds insp2L2_holds
    insp2L3_holds insp2J1_holds hZ

end CFSG.LocalAnalysis.UniquenessCase.UCK
