
module

public import Certificates.Certificate9208Base

public import CFSG.Sporadic.HNBase
public import CFSG.Sporadic.Bridge.TableSurj
public import CFSG.Sporadic.Presentation.HN
public import Certificates.Data.CFSGNative.Bridge.HNGPL
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
import Certificates.Kernel.Sporadic.HNBr.Rels
public import CFSG.Assembly.OrderReductions.InvertedSubgroup
public import CFSG.Assembly.OrderReductions.OddInversion
public import CFSG.Certificates.CosetTableShort
public import CFSG.Certificates.NativeSchreierCard
public import CFSG.GroupTheory.LocalCores.Fitting
public import CFSG.Sporadic.HN.CertificateBase
public import CFSG.Sporadic.HN.F5Chain
public import CFSG.Sporadic.Presentation.Common
public import CFSG.Sporadic.Recognition.CoverChainSub
public import CFSG.Sporadic.Th.F2Spec

public section

namespace Certificates

open CertificateChecks

open CFSG.Sporadic.F5 TauCeti in
theorem certificate9208 : ∃ φ : Sporadic.hnPresentation.Group →*
      GL (Fin (CFSG.Sporadic.HN.Native.hnData ()).d) (ZMod 5),
    J CFSG.Sporadic.HN.Native.hnData ≤ φ.range := KernelSpor.HNRels.le_range

end Certificates
