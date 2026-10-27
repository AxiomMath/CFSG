
module

public import CFSG.Sporadic.Schreier.RuCheckOrbitsBase

public import CFSG.Sporadic.Schreier.RuArrays
public meta import CFSG.Sporadic.Schreier.RuArrays
public import Certificates.Certificate2256

public section

namespace CFSG.Sporadic.RuSchreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native

theorem ruOrbits_check :
    ptPosOK 4060 ruF ruFPos = true ∧ ptPosOK 4060 ruY ruYPos = true ∧
    ruF = ruCOrbit 0 ∧ ruY = ruCOrbit 2 ∧
    (∀ k < 4, ptPosOK 4060 (ruCOrbit k) (ruCOrbitPos.getD k #[]) = true) ∧
    (∀ k < 3, ptPosOK 4060 (ruNOrbit k) (ruNOrbitPos.getD k #[]) = true) ∧
    labListsOK 4060 ruCOrbits ruCLab ruCOrbitPos = true ∧
    labListsOK 4060 ruNOrbits ruNLab ruNOrbitPos = true ∧
    orbitPartOK 4060 #[ruC0A, ruC1A] ruCLab ruCRoots ruCForest.1 ruCForest.2.1
      ruCForest.2.2 = true ∧
    orbitPartOK 4060 #[ruNs0A, ruNs1A] ruNLab ruNRoots ruNForest.1 ruNForest.2.1
      ruNForest.2.2 = true :=
  Certificates.certificate2256

end CFSG.Sporadic.RuSchreier
