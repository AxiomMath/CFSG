module

public import CFSG.Sporadic.Schreier.RuArrays
public import CFSG.Certificates.NativeSetOrbit
public meta import CFSG.Sporadic.Schreier.RuArrays
public meta import CFSG.Certificates.NativeSetOrbit
public import CFSG.Sporadic.Schreier.RuCheckTreeInputs
public import Certificates.Certificate2259

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem ruTree_check :
    ruFixZ.length = 92 ∧ ruTreeSets.size = 593775 ∧
    (∀ j, 1 ≤ j → j < 593775 → ruTreeParent j < j ∧ ruTreeGen j < 2) ∧
    translatesOK ruTreeGens ruFixZ ruTreeSets ruTreePar ruTreeLab = true ∧
    ruSortedStrict ruTreeSets = true :=
  Certificates.certificate2259

end CFSG.Sporadic.RuSchreier
