module

public import CFSG.LocalAnalysis.StandardType.GGFinModelPkg
public import CFSG.LieType.Steinberg.Isogeny.E6
public import CFSG.LieType.Steinberg.CentralExt.FieldFourMultiplier
public import CFSG.LieType.Steinberg.CentralExt.F4E8Multiplier
public import CFSG.LocalAnalysis.ComponentInitial.CentralCoverAbelian

public section

namespace CFSG.StandardType.GGFinModel

open CFSG.Open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Universal

section BridgeE6

@[expose] noncomputable def ggKbEquivE6 (n f : ℕ) :
    GGKb .E6 n f ≃* adjointGroup .E6 (GaloisField 2 f) :=
  (QuotientGroup.quotientMulEquivOfEq
      (CFSG.LieType.Steinberg.CentralExt.FieldFour.e6Isogeny_ker_eq_center
        (K := GaloisField 2 f))).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective
      (φ := CFSG.LieType.Steinberg.Isogeny.e6Isogeny (GaloisField 2 f))
      (CFSG.LieType.Steinberg.Isogeny.e6Isogeny_surjective (GaloisField 2 f)))

end BridgeE6

end CFSG.StandardType.GGFinModel
