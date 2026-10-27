module

public import CFSG.Sporadic.Recognition.Fi24PrimeMultiplierModelInputs
public import CFSG.YGroups.Model432FInputs
public import CFSG.YGroups.Exact.Model
import Certificates.Kernel.YModel.C24053

public section

namespace Certificates

open CertificateChecks

open CFSG.YGroups CFSG.Sporadic.Recognition.Fi24PrimeMultiplier
  CFSG.Sporadic.Presentation.Fi24Prime in
open CFSG.CosetTable (subsetOf) in
open CFSG.Certificates.CosetEnumeration (evalWord) in
theorem certificate24053 :
    CFSG.Sporadic.Recognition.Fi24PrimeMultiplier.m0 = 11 ∧
    (subsetOf CFSG.Sporadic.Recognition.Fi24PrimeMultiplier.m0 [0, 1, 2, 3, 4, 5, 6, 7, 9, 10]).length = 10 ∧
    ((X0.getD r0Idx []).filter fun l => l.1.val == 8).length % 2 = 1 ∧
    ∀ w ∈ X1, CFSG.Certificates.CosetEnumeration.evalWord (arrGen 31671 y432FArrays) (expandX w) = 1 :=
  ⟨KernelPG10.m0_eq, KernelPG10.n10_eq, KernelYModel.c24053_r0, KernelYModel.c24053_rels⟩

end Certificates
