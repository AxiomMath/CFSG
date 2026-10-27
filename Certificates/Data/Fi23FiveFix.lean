module

public import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveInputs
public meta import CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23FiveInputs

public section

namespace CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native

open CFSG.Sporadic.Fi23.Native CFSG.Sporadic.Th.Native

set_option compiler.extract_closed false

@[expose] def fi23FiveFixOK (O : WOrbit) : Bool :=
  let T₀ := eTab O
  let T₁ := starWordTab O (dTable O) (genTables O (-2)) (fivePathOf O)
  (List.range 5).all fun a => (List.range 5).all fun b =>
    a + b == 0 || (fixList (fiveTab T₀ T₁ a b)).length == 21

end CFSG.HardMathSupport.Timmesfeld.SporadicBalance.Fi23Native
