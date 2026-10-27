module

public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.CoindBasis
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Induced

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

namespace FDRep

section Finrank
section FinrankInd

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

/--
The dimension of a coinduced representation is the number of right cosets times
the dimension of the original representation.
-/
theorem finrank_coind_rightRel
    (I : Subgroup G)
    (σ : FDRep k I) :
      finrank (FDRep.coind I σ) =
      Nat.card (Quotient (QuotientGroup.rightRel I)) * finrank σ := by
  exact
    FDRep.finrank_coind_of_basis
      (I := I) (σ := σ)
      (Module.finBasis k σ.V)

/--
The dimension of an induced representation, expressed using the right-coset
quotient appearing in the explicit coinduced basis.
-/
theorem finrank_ind_rightRel
    (I : Subgroup G)
    (σ : FDRep k I) :
    (FDRep.ind I σ).finrank =
      Nat.card (Quotient (QuotientGroup.rightRel I)) * σ.finrank := by
  calc
    (FDRep.ind I σ).finrank
        = (FDRep.coind I σ).finrank := by
            exact finrank_congr (FDRep.indIsoCoind I σ)
    _ = Nat.card (Quotient (QuotientGroup.rightRel I)) * σ.finrank := by
            simpa [finrank] using FDRep.finrank_coind_rightRel I σ

end FinrankInd

end Finrank

end FDRep
