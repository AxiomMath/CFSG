module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.Defs

public section

namespace CFSG.Quasithin.Kleidman.F53Hss36

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod CFSG.Quasithin.F53 CFSG.Quasithin.F53.Stellmacher
open CFSG.Quasithin.CosetGeom CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

set_option linter.unusedSectionVars false

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Ctx

variable {α β α' : Geo H M} (C : Ctx H M S α β α')

include C

theorem of_crit {κ ρ δ : Geo H M} (hκρ : κ ∈ nbrs ρ) (hvκ : vtype κ = true)
    (hδ : vtype δ = false) (hd : dist κ δ = bMin H M) (hd' : dist ρ δ + 1 = bMin H M)
    (hZ : ¬ Zv κ ≤ Qv δ) : Ctx H M S κ ρ δ := by
  have hvρ : vtype ρ = false := vtype_false_of_mem_nbrs_true (mem_nbrs_comm hκρ) hvκ
  refine ⟨C.hA, C.h28, C.h32, ⟨mem_nbrs_comm hκρ, C.bAt_eq_of_true hvκ, hd, hd', hZ⟩, hvκ, ?_,
    C.card_Zv_true hvκ, C.card_Zv_false hvρ, C.isNatSec hvρ, C.hb5⟩
  have hZs : Zv κ ≤ stab δ := C.Zv_le_stab_of_true hvκ hd.le
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx y hy
  have hyc : y ∈ Subgroup.centralizer (stab δ : Set G) := (C.Zv_le_center hδ hy).2
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact Subgroup.mem_centralizer_iff.mp hyc x (hZs hx)

theorem Wnn_le_of_claim4
    (h4 : ∀ {κ ρ δ : Geo H M}, Ctx H M S κ ρ δ → Vn ρ ≤ oTwoRes (stab δ) ⊔ Qv δ)
    {β' δ μ' : Geo H M} (hβ' : vtype β' = false) (hδ : vtype δ = false)
    (hd : dist β' δ + 3 ≤ bMin H M) (hdμ : dist β' μ' + 4 ≤ bMin H M) :
    Wnn β' ≤ stab μ' ⊓ (oTwoRes (stab δ) ⊔ Qv δ) := by
  refine iSup₂_le fun ν hν => iSup₂_le fun ρ hρ => ?_
  have hvν : vtype ν = true := vtype_true_of_mem_nbrs_false hν hβ'
  have hvρ : vtype ρ = false := vtype_false_of_mem_nbrs_true hρ hvν
  have hβρ : dist β' ρ ≤ 2 := by
    have h1 := dist_le_dist_nbr hρ β'
    rw [dist_eq_one_iff_adj.mpr hν] at h1
    omega
  have hρδ : dist ρ δ ≤ dist β' δ + 2 := by
    have := dist_triangle C.hA.amalgam.gen ρ β' δ
    rw [CosetGeom.dist_comm ρ β'] at this
    omega
  have hρμ : dist ρ μ' + 2 ≤ bMin H M := by
    have := dist_triangle C.hA.amalgam.gen ρ β' μ'
    rw [CosetGeom.dist_comm ρ β'] at this
    omega
  refine le_inf ((C.Vn_le_Qv_of_dist hvρ hρμ).trans (pCoreOf_le 2 _)) ?_
  by_cases hall : ∀ κ ∈ nbrs ρ, Zv κ ≤ Qv δ
  · exact (iSup₂_le hall).trans le_sup_right
  push Not at hall
  obtain ⟨κ, hκ, hZκ⟩ := hall
  have hvκ : vtype κ = true := vtype_true_of_mem_nbrs_false hκ hvρ
  have hκδ : dist κ δ = bMin H M := by
    have h1 : dist κ δ ≤ dist ρ δ + 1 := by
      have := dist_le_dist_nbr hκ δ
      rwa [CosetGeom.dist_comm δ κ, CosetGeom.dist_comm δ ρ] at this
    have h2 : ¬ dist κ δ < bMin H M := fun hlt => hZκ (C.Zv_le_Qv_of_true hvκ hlt)
    omega
  have hρδ' : dist ρ δ + 1 = bMin H M := by
    have h1 : dist κ δ ≤ dist ρ δ + 1 := by
      have := dist_le_dist_nbr hκ δ
      rwa [CosetGeom.dist_comm δ κ, CosetGeom.dist_comm δ ρ] at this
    omega
  exact h4 (C.of_crit hκ hvκ hδ hκδ hρδ' hZκ)

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
