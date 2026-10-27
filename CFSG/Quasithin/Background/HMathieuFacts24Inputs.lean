
module

public import CFSG.Quasithin.Background.HMathieuFacts22Base
public import CFSG.Quasithin.Background.HMathieuSyl24GreedyBase
public import CFSG.Quasithin.Background.HMathieuSyl24Odd
public meta import CFSG.Quasithin.Background.HMathieuSyl24

public section

namespace CFSG.Quasithin.H.Mathieu

open CFSG.Monster.Code CFSG.QuasithinUnique.Setup.X1

variable {V : Type*} [CommGroup V]

variable {L M : Subgroup (MulAut V)}

@[expose] def inv24Arr : Array ℕ :=
  #[5, 22, 16, 3, 19, 0, 6, 21, 14, 9, 10, 11, 15, 13, 8, 12, 2, 17, 23, 4, 20, 7, 1, 18]

end CFSG.Quasithin.H.Mathieu
