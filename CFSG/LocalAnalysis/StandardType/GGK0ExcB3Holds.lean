module

public import CFSG.LocalAnalysis.StandardType.GGK0ExcB3OfProducers
public import CFSG.LocalAnalysis.StandardType.GGK0RationalProducerHolds
public import CFSG.LocalAnalysis.StandardType.GGK0ExcTrivialHolds
public import CFSG.LocalAnalysis.StandardType.GGK0ExcCentreU
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

public section

namespace CFSG.StandardType.GGK0ExcB3Prod

open CFSG.Assembly CFSG.StandardType
open CFSG.StandardType.GGK0MarkedKacIface1587

theorem ggK0ExcB3_holds :
    GGK0ExcB3 := by
  let Omega := AlgebraicClosure (ZMod 2)
  exact ggK0ExcB3_of_producers Omega f4Producer_holds e6Producer_holds twE6Producer_holds
    e7Producer_holds e8Producer_holds ggK0ExcTrivial_holds
    (GGK0ExcCentreU.ggK0ExcRealizedCentre_all Omega)

end CFSG.StandardType.GGK0ExcB3Prod
