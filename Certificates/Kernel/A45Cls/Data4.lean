module

public import Certificates.Kernel.A45Cls.Data
public import Certificates.Data.OmegaInv

public section

namespace CertificateChecks.KernelA45

@[expose] def i7cW : List (List ℕ) :=
  [[1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1], [1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1], [], []]

@[expose] def i7oW : List (List ℕ) := [[], [1, 0, 1, 1, 1, 0, 1, 0, 1], [], []]

@[expose] def i7mW : List (List ℕ) :=
  [[0], [1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 1, 0, 1, 1, 0], [0],
    [1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0],
    [1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1],
    [1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1]]

@[expose] def i7gW : List (List ℕ) :=
  [[0, 1, 1, 1, 0, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1],
    [1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0],
    [1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 0],
    [0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1]]

@[expose] def i7giW : List (List ℕ) :=
  [[0, 1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0],
    [1, 0, 1, 1, 0, 1, 0, 1, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 0],
    [0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 0, 1, 1, 0, 1, 1, 0, 1, 1, 0, 1, 0, 1, 1],
    [1, 1, 0, 1, 1, 0, 1, 1, 1, 1, 0, 1, 0, 1, 0, 1, 0, 1, 1, 1, 0]]

@[expose] def i7kGen : Array (Array ℕ) :=
  #[img (Certificates.OmegaInv.k1 ()), img (Certificates.OmegaInv.k2 ())]

end CertificateChecks.KernelA45

end
