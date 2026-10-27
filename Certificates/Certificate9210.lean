module

public import CFSG.Sporadic.Bridge.TwoGen
import Certificates.Kernel.Sporadic.He.Rels
public import CFSG.Sporadic.He.Simple
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Held

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Bridge in
open CFSG.Sporadic.Th CFSG.Sporadic.Bridge.TwoGen CFSG.Sporadic.Bridge.TwoGen.Native TauCeti in
open CFSG.Sporadic.He (a b J rep_alpha rep_beta a_inv actionFacts) in
theorem certificate9210 : 
    ∀ v ∈ Sporadic.hePresentation.relatorLetters, wordProd (img2 a b) v = 1 := KernelSpor.HeRels.relators

end Certificates
