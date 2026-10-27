module

public import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeDefs
public import CFSG.LocalAnalysis.StandardType.GGNbrReflGenNonSplitFamilies
public import Certificates.Certificate1953
public import Certificates.Certificate1954

import CFSG.LocalAnalysis.StandardType.GGNbrWeylTypeE6TwoAux

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly TableB

theorem ggNbrTableBWeylTypeNonSplitOn_e6Two :
    GGNbrTableBWeylTypeNonSplitOn GGNbrNonSplitE6TwoLabel := by
  intro p _ _ lab _ hS _
  obtain ⟨htag, hn1, rfl⟩ := hS
  have hW : LargeEvenLabelAll lab fun R _ I _ => GGTorusWeylTypeW 3 4 R I := by
    obtain ⟨t, l, n⟩ := lab
    dsimp only at htag hn1
    subst htag
    subst hn1
    intro Q hQ
    obtain ⟨K, _, _, hK, hQ'⟩ := hQ
    exact ⟨K, inferInstance, inferInstance, hK, hQ',
      ggWTEx1_weylTypeW_E6Two_three (by rw [hK]; rfl)⟩
  exact (largeEvenLabelAll_and (largeEvenLabelAll_torusLift_E6_two ⟨htag, hn1⟩) hW).mono
    fun _ _ _ _ ⟨hl, hw⟩ _ _ => ⟨4, hl, hw⟩

end CFSG.StandardType

end
