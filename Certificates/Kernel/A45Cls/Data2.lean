module

public import Certificates.Kernel.A45Cls.Data

public section

namespace CertificateChecks.KernelA45

@[expose] def yW : List (List ℕ) :=
  [[1, 0, 1, 0, 1, 1, 0, 1, 0, 1], [1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0],
    [0, 1, 1, 1, 1, 0, 1], [0, 1, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 1]]

@[expose] def cbW : List (List ℕ) := [[0], [1, 0, 1, 0, 1], [1, 0, 1, 2, 1, 0, 1, 1, 1]]

@[expose] def ccW : List (List ℕ) :=
  [[2, 0], [0, 1, 1, 1, 1, 0, 1], [1, 2, 1, 2, 1, 2, 1, 0], [1, 0, 1, 1, 1, 0, 1, 1]]

@[expose] def yB : Array ℕ := img (wv (yW.getD 0 []))

@[expose] def yC : Array ℕ := img (wv (yW.getD 2 []))

@[expose] def cbGen : Array (Array ℕ) := (cbW.map fun w => img (wv w)).toArray

@[expose] def ccGen : Array (Array ℕ) := (ccW.map fun w => img (wv w)).toArray

end CertificateChecks.KernelA45

end
