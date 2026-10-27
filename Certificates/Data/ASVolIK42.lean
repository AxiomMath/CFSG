
module

public import Certificates.Data.SmithB45MatQ
public import CFSG.Quasithin.Background.HMathieuSyl24

public section

namespace CFSG.Quasithin.B45Mat

@[expose] def noQuadRank3 {P : Type*} (n : ℕ) (act : P → ℕ → ℕ) (l : List P) : Bool :=
  decide (l.length < 3) || !quadBasisOK n act l

end CFSG.Quasithin.B45Mat
