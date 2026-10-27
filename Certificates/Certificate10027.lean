module

public import Certificates.Data.CFSGNative.MonsterAxis.CoPair
public import CFSG.Certificates.Kernel.AxisPlane.Orbit
import Certificates.Kernel.CoPair.W1
import Certificates.Kernel.CoPair.W2
import Certificates.Kernel.CoPair.S64Ok
import CFSG.Certificates.Kernel.CoPairOrbitOf
public import Mathlib.Data.Set.Card

public section

namespace Certificates

open CertificateChecks

open CFSG.Monster.Existence.CoPair.Native CFSG.KC.AxisPlane in
theorem certificate10027 :
    (orbitOf 2 genXY 1 ⊆ Set.Iio (2 ^ 24) ∧ (orbitOf 2 genXY 1).ncard = 47104)
    ∧ (orbitOf 2 genXY 64 ⊆ Set.Iio (2 ^ 24) ∧ (orbitOf 2 genXY 64).ncard = 46575)
    ∧ (orbitOf 2 genXY 4096 ⊆ Set.Iio (2 ^ 24) ∧ (orbitOf 2 genXY 4096).ncard = 4600) :=
  ⟨CFSG.KC.CoPair.orbitOf_of_orbOK KernelCoPair.w1_ok,
    CFSG.KC.CoPair.orbitOf_of_orbOK KernelCoPair.s64_ok,
    CFSG.KC.CoPair.orbitOf_of_orbOK KernelCoPair.w2_ok⟩

end Certificates
