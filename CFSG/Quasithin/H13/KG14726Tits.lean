module

public import CFSG.Quasithin.H13.KG14726Local
public import CFSG.Sporadic.Schreier.TitsPair
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Assembly.ComponentTypeDefs

public section

namespace CFSG.Quasithin.H13.KG14726

open Subgroup CFSG.Sporadic.Schreier.Tits

theorem twoCentralConstrained_titsD :
    TwoCentralConstrained ↥titsD := by
  obtain ⟨hSyl, hH, -, -, hJp, -, hJn, -, -, -, hCJ, -⟩ := AT_Tits_intrinsic_local_pair
  exact twoCentralConstrained_of_localPair titsS_le_titsD hSyl
    (AT_Tits_local_center_and_centralizer_checks).2.1 hH hJp titsJ_le_titsH hJn hCJ

end CFSG.Quasithin.H13.KG14726

end
