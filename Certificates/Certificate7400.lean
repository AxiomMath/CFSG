module

public import CFSG.Sporadic.Schreier.J1CountCheckInputs
public import Certificates.Data.CFSGNative.SporadicSchreier.MathieuOddCore
import Certificates.Kernel.SporSch.J1.Cent2163A
import Certificates.Kernel.SporSch.J1.Words7400
import CFSG.Certificates.Kernel.SporSch.ChainKReps

public section

namespace Certificates

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native CFSG.KS.SporSch.MOC
  CertificateChecks.KernelSporSch.J1

open CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.Native in
theorem certificate7400 : wordsTest 3080 2 3 [([3, 0, 1, 0, 3, 2, 1, 2], 19), ([3, 0, 1, 2], 19)] j1ATbl j1BTbl =
    true := by
  rw [wordsTest_eq_val rep_A rep_B, ← wordsTest_eq_val (rep_toTable' ea) (rep_toTable' eb),
    ← wordOrdK_eq _ sz7400 (prepS 0 (by norm_num)).1 (prepS 1 (by norm_num)).1]
  exact words7400

end Certificates
