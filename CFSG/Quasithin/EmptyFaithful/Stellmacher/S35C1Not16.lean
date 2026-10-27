module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1Inter
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1c3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

namespace S35.C1

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem card_inter_eq (hS : Sit H M S) {β l δ β' l' δ' : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) (hδ : l ∈ nbrs δ) (hne : δ ≠ β) (hβ' : vtype β' = false)
    (hl' : l' ∈ nbrs β') (hδ' : l' ∈ nbrs δ') (hne' : δ' ≠ β') :
    Nat.card ↥(Vn β' ⊓ Vn δ') = Nat.card ↥(Vn β ⊓ Vn δ) := by
  obtain ⟨g, rfl, -, rfl⟩ := Std.arc_trans hS hβ hl hδ hne hβ' hl' hδ' hne'
  rw [Vn_smul, Vn_smul, ← conjSub_inf, card_conjSub]

theorem not_card_sixteen (hS : Sit H M S)
    (hCZ : ∀ δ : Geo H M, vtype δ = false → S34.Cb δ = Zv δ)
    {β l δ : Geo H M} (hβ : vtype β = false) (hl : l ∈ nbrs β) (hlδ : l ∈ nbrs δ)
    (hδβ : δ ≠ β) (hcard : Nat.card ↥(Vn β ⊓ Vn δ) = 16) : False := by
  have hA := hS.glob.amalg
  have hlt : vtype l = true := Std.vtype_nbr_S5 hβ hl
  have hlβ : β ∈ nbrs l := Std.mem_nbrs_symm.mpr hl
  obtain ⟨α', hc⟩ := exists_critData hA (hS.glob.crit l hlt) hlβ
  let P := critPathOf hc
  have hb5 := hS.b5
  have hodd := hS.glob.odd
  have hm : P.γ ∈ nbrs α' := Std.mem_nbrs_symm.mpr (P.γ_adj (by omega))
  have hmg : P.γ ∈ nbrs P.δ := P.δ_adj (by omega)
  have hvα' : vtype α' = false := by
    have h := P.vtype_iff hA (j := bMin H M) le_rfl
    rw [P.p_b] at h
    cases hv : vtype α'
    · rfl
    · exfalso
      have he : Even (bMin H M) := h.mp (by rw [hv, hlt])
      obtain ⟨k, hk⟩ := hodd
      obtain ⟨j, hj⟩ := he
      omega
  have dgα : dist P.δ α' = 2 := by
    have := P.dist_of_le (i := bMin H M - 2) (j := bMin H M) (by omega) le_rfl
    rw [P.p_b] at this
    simpa [show bMin H M - (bMin H M - 2) = 2 by omega] using this
  have hgα : P.δ ≠ α' := by
    intro h
    rw [h, CosetGeom.dist_self] at dgα
    omega
  have dβm : dist β P.γ = bMin H M - 2 := by
    have := P.dist_of_le (i := 1) (j := bMin H M - 1) (by omega) (by omega)
    rw [P.p_one] at this
    simpa [show bMin H M - 1 - 1 = bMin H M - 2 by omega] using this
  have dβg : dist β P.δ = bMin H M - 3 := by
    have := P.dist_of_le (i := 1) (j := bMin H M - 2) (by omega) (by omega)
    rw [P.p_one] at this
    simpa [show bMin H M - 2 - 1 = bMin H M - 3 by omega] using this
  have hc' := hc.dist_eq'
  have hcard' := card_inter_eq hS hβ hl hlδ hδβ hvα' hm hmg hgα
  rw [hcard] at hcard'
  have hZα' : Zv α' ≤ Vn α' ⊓ Vn P.δ :=
    (Std.Zv_le_Zv_of_nbr hS hvα' hm).trans (Zv_le_inter hm hmg)
  have hCb := hCZ α' hvα'
  have hle : S34.Cb α' ≤ Vn α' ⊓ Vn P.δ := by rw [hCb]; exact hZα'
  have hcC : Nat.card ↥(S34.Cb α') = 2 := by rw [hCb]; exact hS.cardZ5 α' hvα'
  have hidx : (S34.Cb α').relIndex (Vn α' ⊓ Vn P.δ) = 8 := by
    have h := Subgroup.relIndex_mul_card (H := S34.Cb α') (K := Vn α' ⊓ Vn P.δ)
    rw [inf_eq_left.mpr hle, hcC, hcard'] at h
    omega
  obtain ⟨v, hvZ, hvQ⟩ := Set.not_subset.mp hc.not_le
  have hvV : v ∈ Vn β := Std.Zv_le_Vn hl hvZ
  have hvst : v ∈ stab α' := Std.Vn_le_stab_dist hS (by omega) hvV
  have hvm : v ∈ Qv P.γ := Std.Vn_le_Qv_dist hS (by omega) hvV
  have hcomm : ∀ u ∈ Vn α' ⊓ Vn P.δ, ⁅v, u⁆ ∈ S34.Cb α' := by
    intro u hu
    have := Std.Vn_commute_dist hS (δ := β) (ρ := P.δ) (by omega) v hvV u hu.2
    rw [commutatorElement_eq_one_iff_mul_comm.mpr this]
    exact Subgroup.one_mem _
  exact hvQ (faithful_on_order_eight hS hvα' hm hle inf_le_left
    (fun g hg => stab_le_normalizer_inter hS hvα' hm hmg hgα hg.2) hidx
    ⟨hvst, pCoreOf_le 2 _ hvm⟩ hcomm)

end S35.C1

end F53.Stellmacher

end CFSG.Quasithin
