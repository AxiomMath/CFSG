module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeSylArr
public import CFSG.Sporadic.SmallOddCore.HSData
public import CFSG.Sporadic.Schreier.PairHSCert
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.L246B42HSCheckInputs
import Certificates.Kernel.LocalQT.SV.C4126
import Certificates.Kernel.LocalQT.SV.C4126H
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

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Bridge CFSG.QuasithinUnique.Bridge.HSExcl in
open CFSG.QuasithinUnique.Setup.X1 CFSG.Sporadic.SmallOddCore CFSG.Sporadic.SmallOddCore.Native CFSG.Sporadic.Schreier CFSG.Monster.B.Co2 CFSG.Monster.B.Co2.Native in
theorem certificate4126 : (threeConjCheck 3850 [hsA0P, hsA1P] (hsTP 5) hsT0Words hsT0Prog [hsA0A, hsA1A] = true)
    ∧ (threeConjCheck 3850 [hsA0P, hsA1P] (hsTP 12) hsT1Words hsT1Prog [hsA0A, hsA1A] = true)
    ∧ (threeConjCheck 3850 [hsA0P, hsA1P] (hsTP 21) hsT2Words hsT2Prog [hsA0A, hsA1A] = true)
    ∧ (threeConjCheck 3850 [hsA0P, hsA1P] (hsTP 34) hsT3Words hsT3Prog [hsA0A, hsA1A] = true)
    ∧ (isInvA 3850 hsA0A (invCand 3850 hsA0A) = true ∧
            isInvA 3850 hsA1A (invCand 3850 hsA1A) = true ∧
            ∀ k ∈ [1, 2, 3, 4, 5, 12, 21, 34], permOK 3850 (hsCentTbl k) = true)
    ∧ (sylVerify 3850 1024 hsSylGens (parseNats hsSylParStr) (parseNats hsSylLabStr)
            (parseNats hsSylTabStr) (sylBuild 3850 1024 hsSylGens (parseNats hsSylParStr)
              (parseNats hsSylLabStr)) 6 = true) := CFSG.KD.LQT.C4126.facts

end Certificates
