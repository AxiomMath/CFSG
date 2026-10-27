module

public import CFSG.Quasithin.H13.A5M22HatInputs

public section

namespace CFSG.KC.HMathieu

open CFSG.Quasithin.H.Mathieu CFSG.Quasithin.H13.A5.M22Hat

@[expose] def witE (e : Array ℕ) (p : ℕ) : Bool :=
  decide (wit22I[p]! < pool22.length) && decide (wit22J[p]! < pool22.length) &&
    decide (wit22K[p]! < pool22.length) &&
    order11OK (prod4 e pool22[wit22I[p]!]! pool22[wit22J[p]!]! pool22[wit22K[p]!]!)

@[expose] def inv24 (e : Array ℕ) : Bool := (List.range 24).all fun i => e[e[i]!]! == i

end CFSG.KC.HMathieu

end
