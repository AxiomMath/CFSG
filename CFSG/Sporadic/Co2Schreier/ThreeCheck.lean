module

public import Certificates.Certificate719101

public section

namespace CFSG.Sporadic.Co2Schreier

open CFSG.Monster.B.Co2.Native CFSG.Certificates.Native CFSG.Monster.B.Mathieu

theorem p0Enum_check : enumOK p0Arrs 81 enumP0 = true :=
  Certificates.certificate719101.1

theorem p0Marked_check :
    p0MarkedIdx = [0, 1, 3, 20, 22, 28, 30, 32, 34, 35, 39, 41, 43, 45, 46, 49, 50, 54, 56, 57,
      60, 61, 64, 68, 69, 72, 76] :=
  Certificates.certificate719101.2.1

theorem p0Cube_check :
    eqA 2300 (compA 2300 enumP0.elems[4]! (compA 2300 enumP0.elems[4]! enumP0.elems[4]!))
      (idA 2300) = false :=
  Certificates.certificate719101.2.2.1

theorem p0Six_check :
    p0SixOK 56 [1, 55, 49, 61, 63, 32] = true ∧ p0SixOK 1 [43, 34, 5, 14, 54, 45] = true ∧
      p0SixOK 20 [1, 57, 30, 20, 2, 7] = true :=
  Certificates.certificate719101.2.2.2.1

theorem qCent_check : qCentIdx56 = [0, 23] :=
  Certificates.certificate719101.2.2.2.2

end CFSG.Sporadic.Co2Schreier
