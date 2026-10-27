module

public import CFSG.Sporadic.Bridge.TwoGen
import Certificates.Kernel.Sporadic.McL.Rels
public import CFSG.Sporadic.McL.Simple
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.McLaughlin

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Bridge in
open CFSG.Sporadic.Th CFSG.Sporadic.Bridge.TwoGen CFSG.Sporadic.Bridge.TwoGen.Native TauCeti in
open CFSG.Sporadic.McL (a b J orb rep_alpha rep_alpha_inv rep_beta actionChecks_parts) in
theorem certificate9216 : 
    ∀ v ∈ Sporadic.mclPresentation.relatorLetters, wordProd (img2 a b) v = 1 := KernelSpor.McLRels.relators

end Certificates
