module

public import CFSG.Sporadic.Schreier.RuCheckChains
public import CFSG.Sporadic.Schreier.RuWitArrays
public meta import CFSG.Sporadic.Schreier.RuCheckChains
public meta import CFSG.Sporadic.Schreier.RuWitArrays
public import CFSG.Sporadic.Schreier.RuCheckLInputs
public import Certificates.Certificate2252

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem ruL_check :
    ruChainOK 4060 (ruField4060 5) 3 6 ruLChainBase ruLChainDerivations = true ∧
    rawOrbitSizes 4060 (ruField4060 5) (ruBaseArr 4060 ruLChainBase) = [1820, 64] ∧
    (∀ i < 3, eqA 4060 (ruField4060 5)[i]! ruLGensA[i]! = true) ∧
    (∀ i < 3, eqA 4060 (compA 4060 ruLGensA[i]! ruA0A) (compA 4060 ruA0A ruLGensA[i]!) = true) ∧
    (∀ p ∈ [5, 7, 13], eqA 4060 (powA 4060 (ruYpA p) p) (idA 4060) = true ∧
      eqA 4060 (ruYpA p) (idA 4060) = false) ∧
    (∀ p ∈ [5, 7, 13], eqA 4060 (ruVpA p) (idA 4060) = false ∧
      eqA 4060 (powA 4060 (ruVpA p) 256) (idA 4060) = true) :=
  Certificates.certificate2252

end CFSG.Sporadic.RuSchreier
