module

public import CFSG.Sporadic.J3
public import CFSG.Sporadic.Presentation.J3
public import CFSG.Sporadic.Bridge.TwoGen
public import Certificates.Data.CFSGNative.Bridge.SurjA
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Presentation
public import Certificates.Data.CFSGNative.J3.Data
import Certificates.Kernel.Sporadic.J3.Rels
public import CFSG.Sporadic.Presentation.Common

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Bridge in
open CFSG.Sporadic.Th CFSG.Sporadic.Bridge.TwoGen CFSG.Sporadic.Bridge.TwoGen.Native TauCeti in
open CFSG.Sporadic.J3 (a b J rep_a rep_b faithful j3Facts seedEquiv closure_ab) in
open CFSG.Sporadic.J3.Native (j3Data) in
theorem certificate9211 : ∀ v ∈ Sporadic.j3Presentation.relatorLetters,
    wordProd (img2 (a j3Data) (b j3Data)) v = 1 := KernelSpor.J3Rels.relators

end Certificates
