module

public import CFSG.Certificates.Kernel.Spor.RawSound
public import Certificates.Data.Kernel.AE6E8.Defs
public meta import Certificates.Kernel.Sporadic.RawGen
public meta import Certificates.Kernel.SporSch.Mathieu.Gen
public meta import Certificates.Data.AE6CertBAE8
import CFSG.Certificates.Kernel.Common.Harness
public import Certificates.Kernel.SporSch.Mathieu.Gen

public section

set_option maxRecDepth 400000
namespace CertificateChecks.KernelAE6E8

open CFSG.KS.SporSch.MOCG

@[expose] def e8Derive : List (List Int) :=
  [[-4, 7], [-6, 5, 1], [-8, -9, 8, 9, 8], [-1, -2, 1, 2], [-11, -10, -11, -8, -11, 8, 9],
    [-12, -10, 12, 10], [-10, -11, -10, -8, -11, -1, -4, 5, 2], [-13, -12, 14, 12, 14],
    [-12, -14, -10, 14, -8, -9, 14, 9, 8], [-3, 8, 2], [17, 14, 10], [-18, -16, -14, 18]]

meta def gens16 : Array (Array Nat) :=
  (List.finRange 7).toArray.map fun i =>
    Array.ofFn fun p : Fin 16 => (Certificates.AE6CertB.wr16 (Certificates.AE6CertB.ae8Gen i) p).val

meta def strongE8 : Array (Array Nat) :=
  strongOf 16 gens16
    [[-4, 7], [-6, 5, 1], [-8, -9, 8, 9, 8], [-1, -2, 1, 2], [-11, -10, -11, -8, -11, 8, 9],
      [-12, -10, 12, 10], [-10, -11, -10, -8, -11, -1, -4, 5, 2], [-13, -12, 14, 12, 14],
      [-12, -14, -10, 14, -8, -9, 14, 9, 8], [-3, 8, 2], [17, 14, 10], [-18, -16, -14, 18]]

meta def baseE8 : Array Nat := #[4, 0, 2, 6, 12, 10, 8]

end CertificateChecks.KernelAE6E8

#ks_rawchain CertificateChecks.KernelAE6E8.E8 16 5 16 CertificateChecks.KernelAE6E8.strongE8
  CertificateChecks.KernelAE6E8.baseE8 7 CertificateChecks.KernelAE6E8.e8Derive

namespace CertificateChecks.KernelAE6E8

open CFSG.KS.Raw

theorem kOrdE8 : Nat.beq (rcnt (E8.LR 0) * rcnt (E8.LR 1) * rcnt (E8.LR 2) * rcnt (E8.LR 3) *
    rcnt (E8.LR 4) * rcnt (E8.LR 5) * rcnt (E8.LR 6)) 2580480 = true := by quickRfl

theorem kOrdE8Neg : (!Nat.beq (rcnt (E8.LR 0) * rcnt (E8.LR 1) * rcnt (E8.LR 2) * rcnt (E8.LR 3) *
    rcnt (E8.LR 4) * rcnt (E8.LR 5) * rcnt (E8.LR 6)) 1290240) = true := by quickRfl

end CertificateChecks.KernelAE6E8

end
