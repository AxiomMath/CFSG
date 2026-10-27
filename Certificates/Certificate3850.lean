module

public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEight.NSplitData
import Certificates.Kernel.OmegaEight.C3850

public section

namespace Certificates

open CertificateChecks

open CFSG.EvenSmallLie.OmegaEight.NSplit CFSG.EvenSmallLie.OmegaEight.Stage1 CFSG.CosetTable in
theorem certificate3850 : (nsGenCheck .plus = true)
    ∧ (nsGenCheck .minus = true)
    ∧ (nsRelCheck .plus = true)
    ∧ (nsRelCheck .minus = true)
    ∧ (Finite (PG 7 relPG) ∧ Nat.card (PG 7 relPG) ≤ 1451520)
    ∧ (nsChainCheck .plus = true)
    ∧ (nsChainCheck .minus = true)
    ∧ (nsGamCheck .plus = true)
    ∧ (nsGamCheck .minus = true)
    ∧ (nsH1Check .plus = true)
    ∧ (nsH1Check .minus = true)
    ∧ (∃ Y : Array ℕ, splitTest .plus (29 * nM .plus) (fmMat .plus) (iotaMat .plus) Y = true)
    ∧ (∃ Y : Array ℕ, splitTest .minus (29 * nM .minus) (fmMat .minus) (iotaMat .minus) Y = true) := KernelO8.C3850.c3850

end Certificates
