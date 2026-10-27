module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Data
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Index
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2Multi
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeSylArr
public import CFSG.Sporadic.SmallOddCore.J2Data
public import CFSG.Sporadic.Schreier.PairJ2Cert
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42J2CheckInputs
import Certificates.Kernel.LocalQT.SV.C4127
import Certificates.Kernel.LocalQT.SV.C4127K
import CFSG.Certificates.Kernel.Common.Harness
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.SectionRank.SQT

public section

namespace Certificates

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge CFSG.QuasithinUnique.Bridge.J2Excl in
open CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Sporadic.Schreier.PairNative CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native in
theorem certificate4127 : (isInvA 315 j2A0A (invCand 315 j2A0A) = true ∧ isInvA 315 j2A1A (invCand 315 j2A1A) = true ∧
            ∀ k ∈ [1, 2, 3, 4, 5, 6, 7, 8, 9, 17, 31], permOK 315 (j2CentTbl k) = true)
    ∧ (threeConjCheck 315 [j2A0P, j2A1P] (j2TP 9) j2Row0Words j2Row0Prog [j2A0A, j2A1A] = true)
    ∧ (threeConjCheck 315 [j2A0P, j2A1P] (j2TP 17) j2Row1Words j2Row1Prog [j2A0A, j2A1A] = true)
    ∧ (threeConjCheck 315 [j2A0P, j2A1P] (j2TP 31) j2Row2Words j2Row2Prog [j2A0A, j2A1A] = true)
    ∧ (sylVerify 315 256 j2SylGens j2Par j2Lab j2Tab j2Al 4 = true)
    ∧ (j2MulOK = true ∧ j2InvOK = true ∧ j2RepsOK = true ∧ j2TripleOK = true)
    ∧ (j2PairCertsOK = true)
    ∧ (j2FrobOK = true) := CFSG.KD.LQT.C4127.facts

end Certificates
