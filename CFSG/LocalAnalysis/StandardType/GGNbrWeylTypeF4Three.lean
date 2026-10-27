module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs

import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeF4ThreeAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

theorem ggF4ThreeNbrWeylTypeInput_holds :
    GGF4ThreeNbrWeylTypeInput := by
  intro lab _ h
  obtain ⟨t, l, n⟩ := lab
  obtain ⟨htag, -, -⟩ := h
  dsimp only at htag
  subst htag
  intro Q hQ
  obtain ⟨K, _, _, hK, hQ⟩ := hQ
  have : CharP K 2 := charP_two_of_card hK
  exact ⟨K, inferInstance, inferInstance, hK, hQ, ggWTF4_weylTypeW_F4_three⟩

end CFSG.StandardType

end
