module

public import CFSG.RankThree.PartTwo.Sec4.StatementsComponents
import CFSG.Sporadic.Bridge.M11
import CFSG.Sporadic.Bridge.M12
import CFSG.Sporadic.Bridge.M22
import CFSG.Sporadic.Bridge.M23Surj
import CFSG.Sporadic.Bridge.M24Surj
import CFSG.Sporadic.Bridge.J1
import CFSG.Sporadic.Bridge.J2
import CFSG.Sporadic.Bridge.J3Surj
import CFSG.Sporadic.Bridge.HSSurj
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.McL
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.He
import CFSG.LocalAnalysis.QuasithinUnique.SQTK.Seed.Ru
import CFSG.RankThree.PartTwo.Census.Sporadic.J4Bridge

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open TauCeti CFSG.Blueprint CFSG.RankThree.PartTwo.Sec4

theorem nonempty_carrier_mulEquiv_of_mem46 {s : SporadicName} (hs : s ∈ sporadics46)
    [IsSimpleGroup s.Group] : Nonempty (NativeSporadic.Carrier s ≃* s.Group) := by
  cases s
  case M11 => exact CFSG.Sporadic.Bridge.M11.nonempty_mulEquiv
  case M12 => exact CFSG.Sporadic.Bridge.M12.nonempty_mulEquiv
  case M22 => exact CFSG.Sporadic.Bridge.M22.nonempty_mulEquiv
  case M23 => exact CFSG.Sporadic.Bridge.M23.nonempty_mulEquiv
  case M24 => exact CFSG.Sporadic.Bridge.M24.nonempty_mulEquiv
  case J1 => exact CFSG.Sporadic.Bridge.J1.nonempty_mulEquiv
  case J2 => exact CFSG.Sporadic.Bridge.J2.nonempty_mulEquiv
  case J3 => exact CFSG.Sporadic.Bridge.J3.nonempty_mulEquiv
  case J4 => exact CFSG.RankThree.PartTwo.Census.nonempty_mulEquiv_carrier_J4.map MulEquiv.symm
  case McL => exact CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_McL.map MulEquiv.symm
  case HS => exact CFSG.Sporadic.Bridge.HS.nonempty_mulEquiv
  case He => exact CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_He.map MulEquiv.symm
  case Ru => exact CFSG.QuasithinUnique.SQTK.nonempty_mulEquiv_carrier_Ru.map MulEquiv.symm
  all_goals simp [sporadics46] at hs

end CFSG.RankThree.PartTwo.Sec4.Census
