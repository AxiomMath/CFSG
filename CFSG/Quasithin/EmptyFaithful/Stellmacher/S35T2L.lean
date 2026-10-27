module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T2LD
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ColMain
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Defs
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T2LC

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.T2L

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem inputs_of_sit (hS : Sit H M S) : Inputs H M :=
  ⟨maximal_input hS, fun _ _ hδ hl => plane_input hS hδ hl⟩

theorem commonHyp_of_link (hS : Sit H M S) (hN : S35.II.NbarFull H M) {β l : Geo H M}
    (hβ : vtype β = false) (hl : l ∈ nbrs β) {y : G} (hy : y ∈ stab β)
    (hmov : y ∉ Subgroup.normalizer (Zv l : Set G))
    (hlink : (Wl l ⊓ conjSub y (Wl l)).relIndex (Wl l) = 2) :
    S35.II.CommonHyp β (Wl l ⊓ conjSub y (Wl l)) :=
  commonHyp_of_link_aux hS hN (inputs_of_sit hS) hβ hl hy hmov hlink

theorem step2L (hS : Sit H M S) (_hII : CaseII H M) : S35.II.Step2L H M :=
  step2L_of_inputs hS (inputs_of_sit hS) (S35.Col.zvInf_II hS)

end S35.T2L

end F53.Stellmacher

end CFSG.Quasithin
