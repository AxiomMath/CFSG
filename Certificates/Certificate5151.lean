module

public import CFSG.GH74.GLS.C3.Prop121.Card7H1Inputs
public import CFSG.GH74.GLS.C3.Prop121.Card7SylInputs
meta import CFSG.GH74.GLS.C3.Prop121.Card7H1Inputs
meta import CFSG.GH74.GLS.C3.Prop121.Card7SylInputs

public section

open CFSG.GH74.GLS.C3.Prop121.Card7.Syl CFSG.GH74.GLS.C3.Prop121.Card7.HC

namespace Certificates

set_option maxRecDepth 100000 in
open CFSG.GH74.GLS.C3.Prop121.Card7.Syl CFSG.GH74.GLS.C3.Prop121.Card7.HC in
theorem certificate5151 : (decide (Y11 ∈ SL) = true)
    ∧ (decide (PS 0 2 ∈ SL) = true)
    ∧ ((SL.all fun t => decide (t * Y11 = Y11 * t)) = true)
    ∧ ((SL.all fun s => (!(SL.all fun t => decide (s * t = t * s))) || decide (s = 1 ∨ s = Y11)) = true) :=
  by decide +kernel

end Certificates
