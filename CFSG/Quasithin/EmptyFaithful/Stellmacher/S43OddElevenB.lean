module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddElevenA
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddCore4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddElevenMod
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddLoc

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

namespace Eleven

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

section Crit

variable {α' ν β : Geo H M}

theorem mem_Mab_of_caseL (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (hL : ∀ δ ∈ nbrs α, 2 ^ 7 ≤ Nat.card (Vn δ))
    (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α') (hdν : dist α ν + 1 = bMin H M)
    (hβ : β ∈ nbrs α) (hdβ : dist β ν + 2 = bMin H M) {w : G} (hw : w ∈ Wn α ⊓ stab ν) :
    w ∈ Mab ν α' := by
  by_contra hwM
  have hα'v : vtype α' = true := Core.vtype_crit hA hs ho hc
  have hνv : vtype ν = false := Core.vtype_nu hA hs ho hc hν
  have hs' : Sit43 ν := hs.of_vtype_false hνv
  have hα'ν : α' ∈ nbrs ν := nbrs_symm hν
  obtain ⟨z, hz, hzQ, hzE, hzC⟩ := exists_z hA hs hc hν hdν
  have hgen : Qv α' ⊔ Subgroup.zpowers w = stab ν :=
    hs'.sup_Qv_zpowers_eq_stab hA h26 hα'ν hw.2 hwM
  have hQE : Qv α' ≤ stab ν ⊓ stab α' :=
    le_inf (Qv_le_stab_of_mem_nbrs hA hν) (pCoreOf_le 2 _)
  have hnorm : stab ν ≤ Subgroup.normalizer ((⁅Vn β, Vn α'⁆ ⊔ Zv ν : Subgroup G) : Set G) := by
    rw [← hgen]
    exact sup_le (hQE.trans (edge_le_normalizer hA h26 hs ho hc hν hdν hβ hdβ))
      ((Subgroup.zpowers_le).mpr (Wn_inf_stab_le_normalizer hA h26 hs ho hb5 hc hν hβ hdβ hw))
  have hRZ : ⁅Vn β, Vn α'⁆ ≤ Zv ν :=
    le_Zv_of_normalized hA h26 hs hνv hα'ν (comm_Vn_le_Vn_crit hA hs hc hν hβ hdβ) hnorm
  have h6 : Nat.card (Vn α') = 2 ^ 6 :=
    (hs.comm_le_Zv_iff hA h26 (by omega) hα'v hν hzE hzC hzQ).mp
      ((comm_zpowers_le hβ hz).trans hRZ)
  have h7 := hL β hβ
  rw [card_Vn_eq (Core.vtype_beta hs hβ) hα'v, h6] at h7
  omega

theorem exists_comm_not_mem_Zv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb : 3 ≤ bMin H M) (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α')
    (hdν : dist α ν + 1 = bMin H M) (hβ : β ∈ nbrs α) (hdβ : dist β ν + 2 = bMin H M)
    {l : Geo H M} (hl : l ∈ nbrs α') (hlν : l ≠ ν) :
    ∃ g ∈ ⁅Zv l, Zv α ⊓ Qv α'⁆, g ∉ Zv α' := by
  have hα'v : vtype α' = true := Core.vtype_crit hA hs ho hc
  have hlv : vtype l = false := Sit43.vtype_false_of_adj hα'v hl
  obtain ⟨D⟩ := (hs.of_vtype_false hlv).exists_dict5 hA (nbrs_symm hl)
  have h4d := crit4d hA h26 hs ho hb hc hν hdν hβ hdβ hl hlν
  obtain ⟨x, hxA, hxC⟩ : ∃ x ∈ Zv α ⊓ Qv α', x ∉ Subgroup.centralizer (Zv l : Set G) := by
    by_contra hcon
    push Not at hcon
    apply h4d.1
    rw [Subgroup.commutator_comm]
    exact Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun x hx => hcon x hx
  have hxl : x ∈ stab l := Qv_le_stab_of_mem_nbrs hA hl hxA.2
  have hxY : x ∈ Subgroup.centralizer (Yv α' : Set G) :=
    Qv_le_centralizer_Yv hA hν (Core.Zv_le_Qv_nu hs hdν hxA.1)
  have ha : D.ψ ⟨x, hxl⟩ ∈ S5That := by
    refine (D.mem_centralizer_Y_iff ⟨x, hxl⟩).mp ⟨⟨hxl, pCoreOf_le 2 _ hxA.2⟩, ?_⟩
    rw [← hs.Yv_eq_comm_comm hA h26 hα'v hl]
    exact hxY
  have ha1 : D.ψ ⟨x, hxl⟩ ≠ 1 := fun h =>
    hxC (Qv_le_centralizer_Zv hA l ((D.ker_iff _).mp h))
  obtain ⟨u, hu⟩ := exists_comm_not_mem_fixW ha ha1
  have he : D.φ (orth.act (D.ψ ⟨x, hxl⟩) u * u⁻¹) = ⁅x, D.φ u⁆ := by
    rw [map_mul, map_inv, D.act_eq, commutatorElement_def]
  refine ⟨D.φ (orth.act (D.ψ ⟨x, hxl⟩) u * u⁻¹), ?_, ?_⟩
  · rw [he, Subgroup.commutator_comm]
    exact Subgroup.commutator_mem_commutator hxA (D.φ_mem u)
  · rw [← hs.Zv_inf_centralizer hA h26 hα'v hl, D.fix_eq]
    rintro ⟨u', hu', he'⟩
    exact hu (D.inj he' ▸ hu')

theorem mem_stab_of_mem_Mab (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (ho : Odd (bMin H M)) (hb5 : 5 ≤ bMin H M) (hc : IsCritPair₁ α α') (hν : ν ∈ nbrs α')
    (hdν : dist α ν + 1 = bMin H M) (hβ : β ∈ nbrs α) (hdβ : dist β ν + 2 = bMin H M)
    {w : G} (hw : w ∈ Wn α ⊓ stab ν) (hwM : w ∈ Mab ν α') : w ∈ stab α' := by
  by_contra hwα'
  have hα'v : vtype α' = true := Core.vtype_crit hA hs ho hc
  have hνv : vtype ν = false := Core.vtype_nu hA hs ho hc hν
  obtain ⟨D⟩ := (hs.of_vtype_false hνv).exists_dict5 hA (nbrs_symm hν)
  have h4 : D.ψ ⟨w, hw.2⟩ 4 = 4 := (Sit43.mem_Mab_iff D ⟨w, hw.2⟩).mp hwM
  have hσ : D.ψ ⟨w, hw.2⟩ ∉ S5Syl := fun h => hwα' ((D.mem_S_iff ⟨w, hw.2⟩).mpr h).2
  obtain ⟨l, l', h29⟩ := Core.exists_sit29_nu hA h26 hs ho hc hν
  have hl : l ∈ nbrs α' := h29.n₂
  have hlν : l ≠ ν := h29.ne₁₂.symm
  obtain ⟨g, hgT, hgZ⟩ := exists_comm_not_mem_Zv hA h26 hs ho (by omega) hc hν hdν hβ hdβ hl hlν
  have h4d := (crit4d hA h26 hs ho (by omega) hc hν hdν hβ hdβ hl hlν).2 hgT
  have hgV : g ∈ Vn β :=
    comm_Vn_le_Vn_beta hA hs ho hc hν hβ hdβ (Subgroup.commutator_mono inf_le_left le_rfl h4d.1)
  have hwg : w * g * w⁻¹ = g := by
    rw [isElemAbelian_comm (isElemAbelian_Wn_of_five hA hs hb5) hw.1 (hs.Vn_le_Wn hA h26 hβ hgV)]
    group
  have hgY := h4d.2
  rw [hs.Yv_eq_comm_comm hA h26 hα'v hν, D.comm_comm_eq] at hgY
  obtain ⟨u, hu, rfl⟩ := hgY
  have hfix : orth.act (D.ψ ⟨w, hw.2⟩) u = u := D.inj (by rw [D.act_eq]; exact hwg)
  apply hgZ
  rw [← hs.Zv_inf_centralizer hA h26 hα'v hν, D.fix_eq]
  exact ⟨u, mem_fixW_of_act_eq h4 hσ hu hfix, rfl⟩

end Crit

end Eleven

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
