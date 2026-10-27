module

public import CFSG.Sporadic.Recognition.LyonsAmalgamTauInputs
import Certificates.Kernel.LyTr.Tau

public section

namespace Certificates

open CertificateChecks.KernelLyTr

open CFSG.Sporadic.Recognition.LyonsSims in
theorem certificate6112 : (Ly243.tablesOK = true) ∧ (Ly243.permutesOK = true) ∧ (Ly243.fixZeroOK = true) ∧
    (Ly243.kSwapOK = true) ∧ (Ly243.txyKerOK = true) ∧ (Ly243.txyEnumOK = true) ∧
    (Ly243.txyCenterOK = true) ∧ (Ly243.cosetOK = true) ∧ (Ly243.kCompatOK = true) ∧
    (Tau.tauOK = true) :=
  ⟨tablesOK_of, permutesOK_of, fixZeroOK_of, kSwapOK_of, txyKerOK_of, txyEnumOK_of,
    txyCenterOK_of, cosetOK_of, kCompatOK_of, tauOK_of⟩

end Certificates
