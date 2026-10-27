module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.PushCoreBasic
public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Basic

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher CFSG.Quasithin.F53Push
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem relIndex_Qv_inf_Qv {δ μ : Geo H M} (hδ : vtype δ = false) (hμ : μ ∈ nbrs δ) :
    (Qv δ ⊓ Qv μ).relIndex (Qv δ) = 2 := by
  have hvμ := vtype_true_of_mem_nbrs_false hμ hδ
  have hδμ : δ ∈ nbrs μ := mem_nbrs_comm hμ
  have h28 := C.h28 C.hb1 μ δ hδμ (C.bAt_eq_of_true hvμ)
  have h2 := relIndex_Qv_inf_true C.hA hδμ hvμ
  have hn : Qv δ ≤ Subgroup.normalizer (Qv μ : Set G) := fun x hx =>
    le_normalizer_pCoreOf 2 (stab μ) ((Qv_le_inf C.hA hμ hx).2)
  have e := relIndex_sup_eq_relIndex_inf_right hn
  rw [h28, h2, inf_comm] at e
  exact e.symm

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
