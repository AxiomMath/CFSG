module

public import CFSG.OddTranspositions.PartThree.Eleven.Plus.FactorsCheck
import Certificates.Kernel.PlusFactors.Facts

public section

namespace Certificates

open CertificateChecks

open CFSG.OddTranspositions.PartThree in
theorem certificate1383003 :
    plusFactorsEnumA () = true ∧
    plusFactorsEnumB () = true ∧
    plusFactorsSizeA () = true ∧
    plusFactorsSizeB () = true ∧
    plusFactorsSimpleA () = true ∧
    plusFactorsSimpleB () = true ∧
    plusFactorsTableOK () = true ∧
    plusFactorsMemGens () = true ∧
    plusFactorsCommGens () = true ∧
    plusFactorsDisjoint () = true ∧
    plusFactorsConjGens () = true ∧
    plusFactorsNonabelian () = true ∧
    plusFactorsInvolutions () = true :=
  KernelPlusF.facts

end Certificates
