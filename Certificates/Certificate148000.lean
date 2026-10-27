module

public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37.ModelToJ
public import CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3SevenNamed
public import CFSG.Sporadic.ON.Action
import Certificates.Kernel.Sporadic.ONL37.Glue
public import CFSG.ClassicalGroups.Symplectic.Simple
public import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.RankThree.PartTwo.KFacts.AutKindsUnique
public import CFSG.RankThree.PartTwo.Sec12.Notation
public import CFSG.RankThree.PartTwo.Sec4.Item47Diag
public import CFSG.RankThree.PartTwo.Sec4.Item47Statement
public import CFSG.RankThree.PartTwo.Sec4.Item47Witness
public import CFSG.RankThree.PartTwo.Sec4.LThreePiItem411
public import CFSG.RankThree.PartTwo.Sec4.ProjSLEquiv
public import CFSG.RankThree.PartTwo.Sec8.Statements
public import CFSG.Sporadic.Recognition.CoverChainSub

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.ON CFSG.Sporadic.ON.Native in
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.Coordinator.L37 in
open CFSG.RankThree.PartTwo.Sec4.Census.Karpilovsky.ComponentPrimary.L3Seven in
theorem certificate148000 :     ∀ k < 9, ∃ w : Fin nPts, ∀ t ∈ LSub 0 k, phiJ t • w = w :=
  fun k hk => KernelSpor.ONL37.l37_fix hk

end Certificates
