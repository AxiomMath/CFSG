module

public import CFSG.Sporadic.Schreier.ONCheckSmallAux
public meta import CFSG.Sporadic.Schreier.ONCheckSmallAux
public import CFSG.Sporadic.ONOddCore.SylowEightCheckInputs
public import Certificates.Certificate2129

public section

namespace CFSG.Sporadic.ONOddCore

open CFSG.ONSchreier CFSG.PSL3Four.Native

theorem sylow_eight_cert :
    enumOK 32 sqTabs sqEnum = true ∧ sqEnum.tabs.size = 64 ∧
      enumOK 32 omegaTabs omegaEnum = true ∧ omegaEnum.tabs.size = 8 ∧
      omegaEnum.tabs.all (fun a => omegaEnum.tabs.all fun b => comp 32 a b == comp 32 b a) =
        true ∧
      omegaEnum.tabs.all (fun a => comp 32 a a == idTab 32) = true :=
  Certificates.certificate2129

end CFSG.Sporadic.ONOddCore
