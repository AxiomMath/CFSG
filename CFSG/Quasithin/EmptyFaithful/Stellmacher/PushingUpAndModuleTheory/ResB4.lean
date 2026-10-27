module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ModPack28Proof
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.CriticalDistanceGeometry.ThompsonEdge
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.PushingUpAndModuleTheory.ResA1

public section

set_option linter.unusedSectionVars false

namespace CFSG.Quasithin.F53

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CosetGeom Equiv CFSG.Quasithin.F53Mod
open CFSG.Quasithin.F53Push
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace ConfR

variable {δ μ : Geo H M} {U : Subgroup G}

theorem Zv_mu_le_Qv (h : ConfR δ μ U) : Zv μ ≤ Qv δ :=
  Zv_le_Qv_of_dist_lt (by
    have h1 : dist μ δ = 1 := dist_eq_one_iff_adj.mpr h.sig.adj.symm
    have h2 := bMin_le_bAt (H := H) (M := M) μ
    have := h.b
    omega)

theorem hmod (hA : F53Amalgam H M S) (h : ConfR δ μ U) :
    (∀ g ∈ Qv μ, g ^ 2 ∈ Qv δ) ∧
      ¬ quasithinOmegaOneCenter (stab δ ⊓ stab μ) ≤ centerOf (stab δ) := by
  have hν : μ ∈ nbrs δ := h.sig.adj
  exact F53.Stellmacher.hss28ModAt_of_modPack28 F53.Stellmacher.modPack28_holds hA δ μ hν
    (h.vtype_delta hA) h.hQδ (not_thompsonJ_le_Qv hA hν h.hQδ)
    (centralizer_omegaOneCenter_Qv hA hν h.hQδ h.Zv_mu_le_Qv)

end ConfR

end CFSG.Quasithin.F53
