module

public section

namespace CertificateChecks.KernelAJC

@[expose] def wS : List (List Int) := [[-3, 1, 3, 1], [-2, -1, -2, 3, 1, 2]]

@[expose] def wW : List (List Int) := [[-3, 4, 3], [-5, -1, 5, 1], [-3, 6, 3]]

@[expose] def wX1 : List (List Int) :=
  [[1], [-1, -1, -2, -3, -2, -4, 2, 4], [-2, -6, -3, -3, -4, 2, 4]]

@[expose] def wQ2 : List (List Int) := []

@[expose] def wA : List (List Int) := [[2]]

@[expose] def wQ1 : List (List Int) := [[-3, 1, 3], [-3, 2, 3]]

end CertificateChecks.KernelAJC

end
