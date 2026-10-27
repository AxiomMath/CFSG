module

public import CFSG.Quasithin.Recognition.Kleidman.F53Hss36.NatAPI
public import CFSG.Quasithin.Recognition.F112WSetup

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

theorem Vn_le_stab_pair {δ δ' : Geo H M} (hd : dist δ δ' + 1 = bMin H M) : Vn δ ≤ stab δ' :=
  (hss114_d C.hA C.hb3 hd).1

theorem not_Vn_le_Qv_symm {δ δ' : Geo H M} (hδ : vtype δ = false) (hδ' : vtype δ' = false)
    (hd : dist δ δ' + 1 = bMin H M) (hne : ¬ Vn δ ≤ Qv δ') : ¬ Vn δ' ≤ Qv δ := by
  intro hle
  obtain ⟨x, hxV, hxQ⟩ := Set.not_subset.mp hne
  have hxs : x ∈ stab δ' := C.Vn_le_stab_pair hd hxV
  have h4 := C.four_le_relIndex_commSec hδ' hxs hxQ
  have hcomm : ⁅Vn δ', Subgroup.zpowers x⁆ ≤ Zv δ := by
    rw [← C.comm_Vn_Qv_eq hδ, Subgroup.commutator_comm]
    exact Subgroup.commutator_mono ((Subgroup.zpowers_le).mpr hxV) hle
  have hle2 : commSec (Subgroup.zpowers x) (F53B3.Cv δ') (Vn δ') ≤ Zv δ ⊔ F53B3.Cv δ' :=
    sup_le_sup_right hcomm _
  have hCN : F53B3.Cv δ' ≤ Subgroup.normalizer (Zv δ : Set G) :=
    ((inf_le_left : F53B3.Cv δ' ≤ Vn δ').trans (hle.trans (pCoreOf_le 2 _))).trans (stab_le_normalizer_Zv C.hA δ)
  have h2 : (F53B3.Cv δ').relIndex (Zv δ ⊔ F53B3.Cv δ') ≤ 2 := by
    rw [F112W.relIndex_sup_eq_relIndex_inf hCN, ← C.card_Zv_false hδ]
    have := Subgroup.relIndex_mul_card (H := Zv δ ⊓ F53B3.Cv δ') (K := Zv δ)
    have hpos : 0 < Nat.card ↥((Zv δ ⊓ F53B3.Cv δ') ⊓ Zv δ) := Nat.card_pos
    nlinarith
  have h3 := Subgroup.relIndex_le_of_le_right (H := F53B3.Cv δ') hle2
    (relIndex_ne_zero_of_finite _ _)
  omega

theorem not_Vn_beta_le : ¬ Vn β ≤ Qv α' := fun h =>
  C.hc.not_le ((Zv_le_Vn_of_mem_nbrs (mem_nbrs_comm C.hc.adj)).trans h)

theorem dist_beta : dist β α' + 1 = bMin H M := C.hc.dist_eq'

theorem not_Vn_alpha'_le : ¬ Vn α' ≤ Qv β :=
  C.not_Vn_le_Qv_symm C.vtype_beta C.vtype_alpha' C.dist_beta C.not_Vn_beta_le

theorem exists_mirror : ∃ μ : Geo H M, Ctx H M S μ α' β := by
  have hne := C.not_Vn_alpha'_le
  obtain ⟨μ, hμ, hZμ⟩ : ∃ μ ∈ nbrs α', ¬ Zv μ ≤ Qv β := by
    by_contra h
    push Not at h
    exact hne (iSup₂_le fun μ hμ => h μ hμ)
  have hvμ : vtype μ = true := vtype_true_of_mem_nbrs_false hμ C.vtype_alpha'
  have hd' : dist α' β + 1 = bMin H M := by rw [CosetGeom.dist_comm]; exact C.dist_beta
  have hdμ : dist μ β = bMin H M := by
    have h1 : dist μ β ≤ dist α' β + 1 := by
      have := dist_le_dist_nbr hμ β
      rwa [CosetGeom.dist_comm β μ, CosetGeom.dist_comm β α'] at this
    have h2 : ¬ dist μ β < bMin H M := fun hlt => hZμ (C.Zv_le_Qv_of_true hvμ hlt)
    omega
  refine ⟨μ, ⟨C.hA, C.h28, C.h32, ⟨mem_nbrs_comm hμ, C.bAt_eq_of_true hvμ, hdμ, hd', hZμ⟩,
    hvμ, ?_, C.card_Zv_true hvμ, C.card_Zv_false C.vtype_alpha', C.isNatSec C.vtype_alpha',
    C.hb5⟩⟩
  have hZs : Zv μ ≤ stab β := C.Zv_le_stab_of_true hvμ hdμ.le
  rw [eq_bot_iff, Subgroup.commutator_le]
  intro x hx y hy
  have hyc : y ∈ Subgroup.centralizer (stab β : Set G) := (C.Zv_le_center C.vtype_beta hy).2
  rw [Subgroup.mem_bot, commutatorElement_eq_one_iff_mul_comm]
  exact Subgroup.mem_centralizer_iff.mp hyc x (hZs hx)

end Ctx

end CFSG.Quasithin.Kleidman.F53Hss36
