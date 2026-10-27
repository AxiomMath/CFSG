module

public import Certificates.Kernel.A45Cls.Data

public section

namespace CertificateChecks.KernelA45

@[expose] def t11W : List (List ℕ) :=
  [[0], [2], [1, 1, 1, 1, 0, 1], [1, 0, 1, 0, 1, 2, 1, 0, 1, 1], [1, 1, 1, 0, 1, 0, 1, 1, 2, 1, 1]]

@[expose] def t11Gen : Array (Array ℕ) := (t11W.map fun w => img (wv w)).toArray

@[expose] def t11mW : List (List ℕ) :=
  [[1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1], [0, 1, 1, 1, 1, 0, 1],
    [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1]]

end CertificateChecks.KernelA45

end
