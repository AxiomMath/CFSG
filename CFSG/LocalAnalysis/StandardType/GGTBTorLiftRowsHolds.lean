module

public import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsCls
public import CFSG.LocalAnalysis.StandardType.GGTBTorLiftRowsExc

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTBTorLiftRows_holds :
    GGTBTorLiftRows := by
  intro p lab r m N C M hp hp2 hlab hrow
  cases hrow with
  | aDep h1 h2 h3 h4 _ => exact ggTBTorLift_aDep hp hp2 hlab h1 h2 h3 h4
  | e6Three h1 h2 h3 => subst h2; exact ggTBTorLift_e6Three h1 h3
  | e8Three h1 h2 => subst h2; exact ggTBTorLiftE8 lab hlab h1
  | aInd h1 h2 h3 => exact ggTBTorLift_aInd hp hp2 hlab h1 h2 h3
  | c h1 h2 => exact ggTBTorLift_c hp hp2 hlab h1 h2
  | d h1 => exact ggTBTorLift_d hp hp2 hlab h1
  | e6Ind h1 h2 h3 => exact ggTBTorLift_e6Ind hp hp2 h1 hlab h2 h3
  | e7 h1 h2 => exact ggTBTorLift_e7 hp hp2 h1 h2
  | e8Ind _ h2 h3 => exact ggTBTorLift_e8 hp hp2 h2 h3
  | f4 h1 h2 _ => exact ggTBTorLift_f4 hp hp2 h1 h2
  | g2 h1 h2 => exact ggTBTorLift_g2 hp hp2 h1 h2
  | relD h1 => exact ggTBTorLift_relD hp hp2 hlab h1
  | relE6 h1 h2 => exact ggTBTorLift_relE6 hp hp2 h1 hlab h2
  | relA5 h1 h2 => exact ggTBTorLift_relA5 hp hp2 hlab h1 h2

end CFSG.StandardType

end
