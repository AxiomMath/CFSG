module

public import Certificates.Kernel.Sporadic.RawGen
public import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import Certificates.Kernel.SporSch.Mathieu.Gen

public section

set_option maxRecDepth 400000

namespace CertificateChecks.KernelCatFacts.C2011KP

open CFSG.KS.SporSch.MOCG

@[expose] def wQS11 : List (List Int) :=
  [[2], [3], [1, 1, 2, 1], [1, 1, 3, 1], [1, 2, 1, 2, 1, 1, 2, 1, 1], [1, 1, 2, 1],
    [1, 1, 3, 1], [1, 2, 1, 2, 1, 1, 2, 1, 1], [1, 2, 1, 3, 1, 1, 2, 1, 1],
    [2, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 3],
    [1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3, 1, 3, 1, 2]]

meta def h11M1 : Array Nat :=
  #[5, 0, 6, 8, 7, 1, 9, 17, 13, 2, 10, 20, 15, 3, 11, 18, 16, 4, 12, 19, 14, 26, 21, 27, 29, 28,
    22, 30, 38, 34, 23, 31, 41, 36, 24, 32, 39, 37, 25, 33, 40, 35]

meta def h11M2 : Array Nat :=
  #[0, 9, 10, 11, 12, 5, 6, 7, 8, 1, 2, 3, 4, 17, 19, 20, 18, 13, 16, 14, 15, 21, 22, 23, 24, 25,
    30, 31, 32, 33, 26, 27, 28, 29, 38, 39, 40, 41, 34, 35, 36, 37]

meta def h11M3 : Array Nat :=
  #[0, 17, 20, 18, 19, 5, 6, 7, 8, 13, 15, 16, 14, 9, 12, 10, 11, 1, 3, 4, 2, 21, 22, 23, 24, 25,
    34, 35, 36, 37, 38, 39, 40, 41, 26, 27, 28, 29, 30, 31, 32, 33]

meta def SQ11 : Array (Array Nat) :=
  strongOf 42 #[h11M1, h11M2, h11M3]
    [[2], [3], [1, 1, 2, 1], [1, 1, 3, 1], [1, 2, 1, 2, 1, 1, 2, 1, 1], [1, 1, 2, 1],
      [1, 1, 3, 1], [1, 2, 1, 2, 1, 1, 2, 1, 1], [1, 2, 1, 3, 1, 1, 2, 1, 1],
      [2, 1, 2, 1, 3, 1, 1, 2, 1, 3, 1, 3],
      [1, 2, 1, 2, 3, 1, 3, 1, 2, 1, 2, 3, 1, 3, 1, 2]]

meta def baseQ11 : Array Nat := #[0, 1, 5, 2]

end CertificateChecks.KernelCatFacts.C2011KP

#ks_rawchain CertificateChecks.KernelCatFacts.C2011KP.QC11 42 6 16
  CertificateChecks.KernelCatFacts.C2011KP.SQ11 CertificateChecks.KernelCatFacts.C2011KP.baseQ11 3
  CertificateChecks.KernelCatFacts.C2011KP.wQS11
