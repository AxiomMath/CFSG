module

public import CFSG.LocalAnalysis.QuasithinUnique.Ch1.TitsCoverCheck
import Certificates.Kernel.LocalQT.Cov.C4104A
import Certificates.Kernel.LocalQT.Cov.C4104B
import CFSG.Certificates.Kernel.Common.Harness
import Certificates.Kernel.Misc.Tits.Text
import CFSG.Certificates.Kernel.LocalQTCovTSound
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.CharacterTheory.Semidihedral.DihedralQuaternion
public import CFSG.LieType.Chevalley.RootCommutator
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.Sporadic.Schreier.TitsOther
public import CFSG.Sporadic.Schreier.TitsOuter
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section3.Basic
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter2.Basic

public section

namespace Certificates

open CertificateChecks

open CFSG.KD.LQT.C4104 CFSG.KC.LQT.Cov CFSG.QuasithinUnique.Ch1.TitsCover

open CFSG CFSG.QuasithinUnique CFSG.QuasithinUnique.Ch1 CFSG.QuasithinUnique.Ch1.TitsCover in
theorem certificate4104 : (CFSG.QuasithinUnique.Ch1.TitsCover.covCheck CFSG.QuasithinUnique.Ch1.TitsCover.covData = true)
    ∧ (CFSG.QuasithinUnique.Ch1.TitsCover.covData.nV = 2048) := by
  have h := covT_sound CT.chars P H 2048 SG SGI
    (fun j hj => KernelMisc.TitsText.titsDerivedArrs_get hj) kA kB
  rw [← CT.eq] at h
  exact h

end Certificates
