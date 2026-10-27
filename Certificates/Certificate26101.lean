module

public import CFSG.LocalAnalysis.EvenSporadicStandard.Fin76b.TC3HCheck
import Certificates.Kernel.Sporadic.OddCore.Outer26101F
import Certificates.Certificate2236
import Certificates.Certificate2237
import Certificates.Certificate24602
import Certificates.Certificate24603
public import CFSG.GroupTheory.Fitting.CharacteristicP
public import CFSG.GroupTheory.LocalCores.Components
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.EvenSporadicStandard.HypOne.Rows
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic
public import CFSG.Walter.JRFacts

public section

namespace Certificates

open CertificateChecks

theorem certificate26101 : CFSG.EvenSporadicStandard.Fin76b.TC3H.j3OuterOK = true ∧
    CFSG.EvenSporadicStandard.Fin76b.TC3H.j3CountOuter = 0 :=
  ⟨KernelSpor.O26101.outerOK, KernelSpor.O26101.countOuter⟩

end Certificates
