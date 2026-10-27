module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1d4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1b4
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1Not16
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C1Step2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53 CFSG.Quasithin.EmptyFaithful.Stellmacher
open scoped commutatorElement

namespace S35.C1

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

omit [Finite G] in
theorem card_Vn_eq {δ δ' : Geo H M} (hδ : vtype δ = false) (hδ' : vtype δ' = false) :
    Nat.card ↥(Vn δ') = Nat.card ↥(Vn δ) := by
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq (hδ.trans hδ'.symm)
  rw [Vn_smul, card_conjSub]

omit [Finite G] in
theorem Cb_eq_Zv_all {β : Geo H M} (hβ : vtype β = false) (h : S34.Cb β = Zv β)
    {δ : Geo H M} (hδ : vtype δ = false) : S34.Cb δ = Zv δ := by
  obtain ⟨g, rfl⟩ := exists_smul_of_vtype_eq (hβ.trans hδ.symm)
  rw [S34.Cb_smul, Zv_smul, h]

theorem card_Vn_of_Cb_eq (hS : Sit H M S) {β : Geo H M} (hβ : vtype β = false)
    (h : S34.Cb β = Zv β) : Nat.card ↥(Vn β) = 32 := by
  have h16 := IsOrthSec.relIndex_eq (hS.orth β hβ)
  have hm := Subgroup.relIndex_mul_card (H := S34.Cb β) (K := Vn β)
  rw [inf_eq_left.mpr (S34.Cb_le_Vn β), h16, h, hS.cardZ5 β hβ] at hm
  omega

theorem inter_ne_Vn (hS : Sit H M S) {β l δ : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) (hlδ : l ∈ nbrs δ) (hδβ : δ ≠ β) : Vn β ⊓ Vn δ ≠ Vn β := by
  intro h
  have hlt := Std.vtype_nbr_S5 hβ hl
  have hlβ : β ∈ nbrs l := Std.mem_nbrs_symm.mpr hl
  have hnl : stab l ≤ Subgroup.normalizer (Vn β : Set G) := by
    have := stab_le_normalizer_inter hS hβ hl hlδ hδβ
    rwa [h] at this
  have hbot : Vn β = ⊥ := by
    refine eq_bot_of_normalizer_transitive_vertex hS.glob.amalg (α := β) (β := l)
      (show (graph (H ⊔ M) H M).Adj β l from hl) (U := Vn β) ?_ ?_ ?_
    · refine le_inf ((Std.Vn_le_Qv_self hS β).trans (pCoreOf_le 2 _)) ?_
      exact (Std.Vn_le_Qv_dist hS (by
        rw [dist_eq_one_iff_adj.mpr hl]
        have := hS.b5
        omega)).trans (pCoreOf_le 2 _)
    · intro ε hε ε' hε'
      obtain ⟨g, hg, hgε⟩ := stab_transitive_on_nbrs hε hε'
      exact ⟨g, Std.Vn_normal β hg, smul_eq_of_mem_stab hg, hgε⟩
    · intro ε hε ε' hε'
      obtain ⟨g, hg, hgε⟩ := stab_transitive_on_nbrs hε hε'
      exact ⟨g, hnl hg, smul_eq_of_mem_stab hg, hgε⟩
  exact Zv_ne_bot hS.glob.amalg l (le_bot_iff.mp (hbot ▸ Std.Zv_le_Vn hl))

theorem inter_dichotomy_aux (hS : Sit H M S) {β l δ : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) (hlδ : l ∈ nbrs δ) (hδβ : δ ≠ β) :
    Vn β ⊓ Vn δ = Zv l ∨ (Zv l < Vn β ⊓ Vn δ ∧ Nat.card ↥(Vn β ⊓ Vn δ) = 8 ∧
      Nat.card ↥(Vn β) = 32 ∧ S34.Cb β = Zv β) := by
  by_cases hR : Vn β ⊓ Vn δ = Zv l
  · exact Or.inl hR
  right
  have hA := hS.glob.amalg
  have hlt := Std.vtype_nbr_S5 hβ hl
  have hVU := Vn_le_comm_of_ne hS hβ hl hlδ hδβ
    (fun y hy hy2 hyc => omegaOneCenter_Qv_le_Zv hS hlt hy hy2 hyc) hR
  have hel := Std.Vn_isElemAbelian hS β
  have hCle : S34.Cb β ≤ Zv β := by
    refine collapse (quot_stab_five hA hβ) (Std.Vn_normal β) hel.2
      (fun x hx y hy => by
        have := hel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
        exact congrArg Subtype.val this)
      (S34.Zv_le_Cb hS.glob hβ)
      (fun z hz f hf => Subgroup.mem_centralizer_iff.mp (hS.glob.central β hβ hz).2 f hf)
      rfl (Std.comm_Vn_Qv hS hβ).le
      (comm_oTwoRes_of_comm (Std.Vn_normal β) hel.2
        (fun x hx y hy => by
          have := hel.1.is_comm.comm ⟨x, hx⟩ ⟨y, hy⟩
          exact congrArg Subtype.val this) hVU)
      (hS.orth β hβ)
  have hCb : S34.Cb β = Zv β := le_antisymm hCle (S34.Zv_le_Cb hS.glob hβ)
  have hV32 := card_Vn_of_Cb_eq hS hβ hCb
  have hZR : Zv l ≤ Vn β ⊓ Vn δ := Zv_le_inter hl hlδ
  have hlt' : Zv l < Vn β ⊓ Vn δ := lt_of_le_of_ne hZR (Ne.symm hR)
  have hc4 := hS.cardZ3 l hlt
  have hgt : 4 < Nat.card ↥(Vn β ⊓ Vn δ) := by
    have := Subgroup.card_lt_of_lt hlt'
    omega
  have hdvd : Nat.card ↥(Vn β ⊓ Vn δ) ∣ 32 := hV32 ▸ Subgroup.card_dvd_of_le inf_le_left
  have hlt32 : Nat.card ↥(Vn β ⊓ Vn δ) < 32 := by
    have hlt'' : Vn β ⊓ Vn δ < Vn β := lt_of_le_of_ne inf_le_left (inter_ne_Vn hS hβ hl hlδ hδβ)
    have := Subgroup.card_lt_of_lt hlt''
    omega
  have hc : Nat.card ↥(Vn β ⊓ Vn δ) = 8 := by
    have hle : Nat.card ↥(Vn β ⊓ Vn δ) ≤ 32 := Nat.le_of_dvd (by norm_num) hdvd
    have hcases : Nat.card ↥(Vn β ⊓ Vn δ) = 8 ∨ Nat.card ↥(Vn β ⊓ Vn δ) = 16 := by
      interval_cases h : Nat.card ↥(Vn β ⊓ Vn δ) <;> simp_all
    rcases hcases with h | h
    · exact h
    · exact (not_card_sixteen hS (fun δ' hδ' => Cb_eq_Zv_all hβ hCb hδ') hβ hl hlδ hδβ h).elim
  exact ⟨hlt', hc, hV32, hCb⟩

end S35.C1

end F53.Stellmacher

end CFSG.Quasithin
