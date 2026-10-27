module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1Main
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChSyl

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53

namespace S35

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem ctx_of_caseI (hS : Sit H M S) (hI : CaseI H M) : Ch.Ctx H M S where
  sit := hS
  caseI := hI
  orthZ := fun _ hδ => (C1.caseI_orthSec hS hI hδ).2
  hR := fun _ _ _ _ hβ hl hlδ hlδ' hδβ hδ'β hδδ' =>
    ⟨C1.inter_eq hS hβ hl hlδ hδβ hlδ' hδ'β, C1.inter_eq' hS hβ hl hlδ hδβ hlδ' hδδ'.symm,
      C1.stab_le_normalizer_inter hS hβ hl hlδ hδβ⟩

end S35

end F53.Stellmacher

end CFSG.Quasithin
