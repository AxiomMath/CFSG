
module

public import Certificates.Kernel.F4Gamma.Final

open CFSG.RankThree.PartTwo.Sec21.FF81.F4 CFSG.LieType.Ree CFSG.Blueprint.Chevalley

public section

namespace Certificates

open CFSG.RankThree.PartTwo.Sec21.FF81.F4 CFSG.LieType.Ree CFSG.Blueprint.Chevalley in
theorem certificate799600 : ∀
      (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime], Nat.card K = 2 →
    ∃ V₀ : Subgroup (adjointGroup ReeTag.F4.tag K),
      CFSG.RankThree.PartTwo.Sec21.FF79.IsSylowOf 2 V₀ (reeFixed ReeTag.F4 K 0) ∧
        invClosure V₀ ≠ V₀ :=
  fun K _ _ _ hK => CFSG.KC.F4Gamma.gamma_sylow2_kc K hK

end Certificates
