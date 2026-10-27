module

public import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.Coordinator.GenData
import Certificates.Kernel.J4M2.C12680

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic.J4Schreier CFSG.Sporadic.GLQ CFSG.SectionRank.Native in
open CFSG.AGLEmbeddingD2.Wilson.Coordinator in
theorem certificate12680 : (slpLt 0 = true ∧ slpEq 0 = true)
    ∧ (slpLt 1 = true ∧ slpEq 1 = true)
    ∧ (slpLt 2 = true ∧ slpEq 2 = true)
    ∧ (slpLt 3 = true ∧ slpEq 3 = true)
    ∧ (slpLt 4 = true ∧ slpEq 4 = true)
    ∧ (slpLt 5 = true ∧ slpEq 5 = true)
    ∧ (slpLt 6 = true ∧ slpEq 6 = true)
    ∧ (slpLt 7 = true ∧ slpEq 7 = true)
    ∧ (O.conjOK An.1 QXn.1 (qWord 10 0 1).1 = true ∧ O.conjOK An.1 QYn.1 (qWord 0 10 6).1 = true) := KernelC12680.c12680

end Certificates
