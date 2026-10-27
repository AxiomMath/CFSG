module

public import CFSG.LocalAnalysis.StandardType.GGSporKRestDefs
import Certificates.Kernel.SporCovF2.RuGlue
public import Certificates.Data.CFSGNative.Ru.Data

public section

namespace Certificates

theorem certificate1023102 : 
    CFSG.StandardType.SporadicShape.SporKRestCover 3 CFSG.Blueprint.NativeSporadic.Ru ∧
      CFSG.StandardType.SporadicShape.SporKRestCover 5 CFSG.Blueprint.NativeSporadic.Ru := by
  intros
  exact ⟨@CFSG.StandardType.SporadicShape.SporKRestCover.of_mulEquiv
      ↥(CFSG.Sporadic.SmallF2.J CFSG.Sporadic.Ru.Native.ruData) CFSG.Blueprint.NativeSporadic.Ru
      inferInstance inferInstance CFSG.Sporadic.Bridge.Ru.nativeEquiv.symm 3
      CFSG.KD.SporCovF2.Ru.sporKRestCover_three_J,
    @CFSG.StandardType.SporadicShape.SporKRestCover.of_mulEquiv
      ↥(CFSG.Sporadic.SmallF2.J CFSG.Sporadic.Ru.Native.ruData) CFSG.Blueprint.NativeSporadic.Ru
      inferInstance inferInstance CFSG.Sporadic.Bridge.Ru.nativeEquiv.symm 5
      CFSG.KD.SporCovF2.Ru.sporKRestCover_five_J⟩

end Certificates
