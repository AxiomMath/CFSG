
module


public import Certificates.Certificate799600

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
  CFSG.RankThree.PartTwo.Sec21.FF79.L41 CFSG.RankThree.PartTwo.Sec21.FF81
open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Ree
open CFSG.SeitzReduction.F4Pilot

section Cert

theorem gamma_sylow2 (K : Type) [Field K] [Finite K] [CharP K ReeTag.F4.prime]
    (hK : Nat.card K = 2) :
    ∃ V₀ : Subgroup (adjointGroup ReeTag.F4.tag K),
      IsSylowOf 2 V₀ (reeFixed ReeTag.F4 K 0) ∧ invClosure V₀ ≠ V₀ :=
  Certificates.certificate799600 K hK

theorem kf_F4Graph_holds : KF_F4Graph :=
  kf_F4Graph_of_gamma (by intro K _ _ _ hK; exact gamma_sylow2 K hK)

end Cert

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
