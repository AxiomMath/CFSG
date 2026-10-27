module

public import CFSG.Sporadic.Schreier.TitsQTCheckInputs
import Certificates.Kernel.SporSch.Tits.QT4155

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.TitsQT in
open CFSG.Sporadic.Schreier.Tits CFSG.Certificates.Native CFSG.Monster.B.Co2.Native in
theorem certificate4155 : (siftA 1755 titsSLevels (baseArr 1755 titsSBase) 0 conjXArr = true ∧
          siftA 1755 titsSLevels (baseArr 1755 titsSBase) 0 conjYArr = true ∧
          (compA 1755 conjXArr conjYArr)[12]! = 115 ∧
          (compA 1755 conjYArr conjXArr)[12]! = 117) := KernelSporSch.TitsQT.facts

end Certificates
