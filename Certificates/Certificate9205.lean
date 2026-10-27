module

public import CFSG.Sporadic.Bridge.TwoGen
import Certificates.Kernel.Sporadic.Fi22.Rels
public import CFSG.Sporadic.Fi22.Class
public import TauCeti.GroupTheory.SpecificGroups.CFSG.Sporadic.Fischer.TwentyTwo

public section

namespace Certificates

open CertificateChecks

open CFSG CFSG.Sporadic CFSG.Sporadic.Bridge in
open CFSG.Sporadic.Th CFSG.Sporadic.Bridge.TwoGen CFSG.Sporadic.Bridge.TwoGen.Native TauCeti in
open CFSG.Sporadic.Fi22 (a b J orb rep_alpha rep_beta a_inv actionChecks_parts) in
theorem certificate9205 : 
    ∀ v ∈ Sporadic.fi22Presentation.relatorLetters, wordProd (img2 a b) v = 1 := KernelSpor.Fi22Rels.relators

end Certificates
