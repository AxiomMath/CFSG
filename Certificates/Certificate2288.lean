module

public import CFSG.Sporadic.SmallOddCore.McL
public import CFSG.Sporadic.SmallOddCore.AutCount
public import CFSG.Sporadic.SmallOddCore.CountSplit
public import CFSG.Sporadic.SmallOddCore.McLCountA
public import CFSG.Sporadic.Schreier.PairMcLPairs
public meta import CFSG.Sporadic.SmallOddCore.McLWords
public meta import CFSG.Sporadic.Schreier.PairMcLCheck
public import CFSG.Sporadic.Schreier.PairMcLCertInputs
public import CFSG.Sporadic.Schreier.PairMcLCheckInputs
public meta import CFSG.Sporadic.Schreier.PairMcLCert
public meta import Certificates.Data.CFSGNative.PairSchreier.Core
public meta import Certificates.Data.CFSGNative.Schreier.Check
public meta import Certificates.Data.CFSGNative.MonsterB.Co2Chain
public import CFSG.Sporadic.Schreier.PairMcLCheck
public import Certificates.Data.CFSGNative.PairSchreier.Counts
public meta import Certificates.Data.CFSGNative.PairSchreier.Counts
import Certificates.Kernel.Sporadic.OddCore.P2288
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.Sporadic.Th.F2Spec

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.SmallOddCore Subgroup CFSG.Sporadic.Th CFSG.Sporadic.Schreier in
open CFSG.Sporadic.Schreier.PairNative CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2 in
open CFSG.Monster.B.Co2.Native in
theorem certificate2288 : ordB PairMcL.bs (patW PairMcL.wA PairMcL.wB [false, true, true]) 12 = true ∧
    ordB PairMcL.bs (patW PairMcL.wA PairMcL.wB mclWPat) 7 = true := KernelSpor.P2288.facts2288

end Certificates
