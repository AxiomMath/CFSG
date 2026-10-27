module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.LocalAnalysis.StandardType.GGTypeANbrTableBWeyl

import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeSplitAAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggNbrTableBWeylTypeSplitOn_typeA :
    GGNbrTableBWeylTypeSplitOn fun _ lab => lab.tag = .A := by
  rintro p hp - ⟨tag, n, f⟩ hlab htag - hsp Q hQ
  dsimp only at htag
  subst htag
  have hl1 : 1 ≤ n := hlab.2.1
  exact ggWTSA_recipeLinear_weylTypeW (d := n + 1) (N := 2 ^ f) hp hsp.2.2 ⟨f, rfl⟩ (by omega) hQ

end CFSG.StandardType

end
