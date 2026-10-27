module

public import CFSG.Quasithin.Background.B5NonInputs
public import CFSG.Quasithin.Background.A3StructureListNative
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.LayerSQTK

public section

namespace CFSG.Quasithin

theorem asA21SQTKSection
    : AsA21SQTKSection := by
  intro X _ _ hX H G _ _ π hπ L _ hL h2
  have key := CFSG.QuasithinUnique.Setup.Layer.sqtk_two_power_index
    CFSG.SectionRank.oddKernelCentralization CFSG.SectionRank.catalogStepHyp hX.isSQTKCat H π hπ L
    hL h2
  exact ⟨CFSG.SectionRank.isStronglyQuasithin_iff.1 key.1.1, key.1.2⟩

end CFSG.Quasithin
