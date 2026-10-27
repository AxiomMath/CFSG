module

public import CFSG.Sporadic.HeldB.CertPChainData
public import CFSG.Sporadic.HeldB.CertPFieldsData
public meta import CFSG.Sporadic.HeldB.CertPChainData
public meta import CFSG.Sporadic.HeldB.CertPFieldsData
public import Certificates.Certificate2110

public section

namespace CFSG.Sporadic.HeldB

theorem heStab_check :
    (∀ j ∈ heStabIdx, (heStrong j)[0]! = 0) ∧
    (∀ y < 8330, y = 0 ∨ ∃ j ∈ heStabIdx, (heStrong j)[y]! ≠ y) :=
  Certificates.certificate2110

end CFSG.Sporadic.HeldB
