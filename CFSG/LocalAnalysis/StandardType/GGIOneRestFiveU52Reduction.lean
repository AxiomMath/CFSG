module

public import CFSG.LocalAnalysis.StandardType.GGIOneRestFiveUnitaryDvd
public import CFSG.LocalAnalysis.StandardType.GGStdSubSmallRestUnitaryCenter
public import CFSG.LocalAnalysis.StandardType.GGBstarDeltaUnitaryOutdiag

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.LocalAnalysis.ComponentInitial

namespace IOneU52

theorem ggOutdiagPrime_five {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) :
    GGOutdiagPrime 3 (UnitaryR K 1 5) (UnitaryI K 1 5) :=
  InndiagSU.ggOutdiagPrime_unitary (d := 5) (n := 1) hK le_rfl (by norm_num) (by decide)
    Nat.prime_three (by norm_num) (by norm_num)

section Certs

theorem ggCenterPrime_five {K : Type} [Field K] [Finite K] (hK : Nat.card K = (2 ^ 1) ^ 2) :
    GGCenterPrime 3 (UnitaryR K 1 5) :=
  StdSubRestU.ggCenterPrime_unitary (d := 5) (n := 1) (p := 3) hK le_rfl (by norm_num)
    (by decide) Nat.prime_three (by norm_num) (by norm_num)

theorem ggEndNodeIOne_five_of_root {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ 1) ^ 2) (hR : GGEndNodeRoot 3 3 (UnitaryR K 1 5) (UnitaryI K 1 5)) :
    GGEndNodeIOne 3 3 (UnitaryR K 1 5) (UnitaryI K 1 5) :=
  ggEndNodeIOne_of_root_prime hR (ggOutdiagPrime_five hK) (ggCenterPrime_five hK)

end Certs

end IOneU52

@[expose] def GGIOneUnitaryFiveRootInput : Prop :=
  ∀ (K : Type) [Field K] [Finite K], Nat.card K = (2 ^ 1) ^ 2 →
    GGEndNodeRoot 3 3 (UnitaryR K 1 5) (UnitaryI K 1 5)

section Certs

theorem ggIOneUnitaryFiveTwoInput_of_rootInput (hR : GGIOneUnitaryFiveRootInput) :
    GGIOneUnitaryFiveTwoInput :=
  fun K _ _ hK => IOneU52.ggEndNodeIOne_five_of_root hK (hR K hK)

end Certs

end CFSG.StandardType
