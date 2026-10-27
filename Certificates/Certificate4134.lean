module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeData
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeArr
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeSylArr
public import CFSG.Sporadic.HeldB.InnerCheck
public import CFSG.Sporadic.HeldB.OuterArithCheck
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X1HeCheckInputs
import Certificates.Kernel.LocalQT.SV.C4134
import Certificates.Kernel.LocalQT.SV.C4134H
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

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup CFSG.QuasithinUnique.Setup.X1 in
open CFSG.Sporadic.HeldB CFSG.Monster.B.Co2.Native in
theorem certificate4134 : (threeConjCheck 8330 [heA0P, heA1P] heT0P heT0Words heT0Prog [heGen 0, heGen 1] = true)
    ∧ (threeConjCheck 8330 [heA0P, heA1P] heT1ArrP heT1Words heT1Prog [heGen 0, heGen 1] = true)
    ∧ (threeConjCheck 8330 [heA0P, heA1P] heUP heUWords heUProg [heGen 0, heGen 1] = true)
    ∧ (sylVerify 8330 2048 heSylGens (parseNats heSylParStr) (parseNats heSylLabStr)
            (parseNats heSylTabStr) (sylBuild 8330 2048 heSylGens (parseNats heSylParStr)
              (parseNats heSylLabStr)) 6 = true) := CFSG.KD.LQT.C4134.facts

end Certificates
