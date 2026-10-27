module

public import CFSG.Certificates.Kernel.Enum.Defs
public import Certificates.Data.Kernel.Spor.Chain

public section

namespace CFSG.KC.TitsPi

open CFSG.KC.Enum CFSG.KS

@[expose] noncomputable def cmpL (n w P : Nat) : Nat → List Nat → Bool
  | k, a :: t => a == pg w (mask w) P k && cmpL n w P (k + 1) t
  | k, [] => k == n

end CFSG.KC.TitsPi

end
