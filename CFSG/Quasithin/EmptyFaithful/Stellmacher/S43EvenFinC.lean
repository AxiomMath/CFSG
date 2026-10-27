module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43EvenFinB
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseF2

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace EvenFin

theorem orth_fix_stab_four : ∀ σ : Perm (Fin 5), σ 4 = 4 → ∀ v : orth.W,
    (∀ b ∈ S5SylF, orth.act b v = v) → orth.act σ v = v := by
  decide +kernel

omit [Finite G] in
theorem Wcomm_le_Wn (α : Geo H M) : Wcomm α ≤ Wn α := by
  rw [Wcomm, Subgroup.commutator_le]
  intro w hw g hg
  have h1 : g * w⁻¹ * g⁻¹ ∈ Wn α :=
    (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Wn α hg) w⁻¹).mp (inv_mem hw)
  rw [commutatorElement_def, show w * g * w⁻¹ * g⁻¹ = w * (g * w⁻¹ * g⁻¹) by group]
  exact mul_mem hw h1

omit [Finite G] in
theorem stab_le_normalizer_Wcomm (α : Geo H M) :
    stab α ≤ Subgroup.normalizer (Wcomm α : Set G) := by
  intro x hx
  rw [Subgroup.mem_normalizer_iff_map_conj_eq, Wcomm, Subgroup.map_commutator,
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (stab_le_normalizer_Wn α hx),
    Subgroup.mem_normalizer_iff_map_conj_eq.mp (Subgroup.le_normalizer hx)]

theorem Mab_le_centralizer_Zv (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) {β : Geo H M} (hβ : β ∈ nbrs α) :
    Mab α β ≤ Subgroup.centralizer (Zv β : Set G) := by
  obtain ⟨D⟩ := hs.exists_dict5 hA hβ
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  have hZb : Zv β = (fixW orth S5Syl).map D.φ := by
    rw [← D.bar_S, D.map_fixW inf_le_left, hs.Zv_inf_centralizer hA h26 hβv (nbrs_symm hβ)]
  intro m hm
  have hmA : m ∈ stab α := Mab_le_stab α β hm
  have h4 : D.ψ ⟨m, hmA⟩ 4 = 4 := (Sit43.mem_Mab_iff D ⟨m, hmA⟩).mp hm
  rw [Subgroup.mem_centralizer_iff]
  intro z hz
  rw [hZb] at hz
  obtain ⟨v, hv, rfl⟩ := hz
  have hfix := orth_fix_stab_four _ h4 v fun b hb => hv b ((mem_S5Syl_iff b).mpr hb)
  have e := D.act_eq ⟨m, hmA⟩ v
  rw [hfix] at e
  have e' : D.φ v = m * D.φ v * m⁻¹ := e
  calc D.φ v * m = (m * D.φ v * m⁻¹) * m := by rw [← e']
    _ = m * D.φ v := by group

end EvenFin

open EvenFin in
theorem final_contradiction_of (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α)
    (hsec : IsOrthSec (stab α) (Zv α) (Wcomm α)) (hZW : Zv α ≤ Wcomm α)
    (hcomm : ⁅Wcomm α, Qv α⁆ ≤ Zv α) (hMC : Mcent α ≤ Cst β) (hCM : ¬ Cst β ≤ Mcent α)
    (hW : (Subgroup.centralizer (Cst β : Set G)).relIndex (Wcomm α) = 2)
    (hPC : stab α ⊓ stab β ≤ Subgroup.normalizer (Cst β : Set G))
    (hMabC : Mab α β ≤ Subgroup.normalizer (Cst β : Set G)) {Q : Subgroup G}
    (hQP : Q ≤ stab α ⊓ stab β) (hMabQ : Mab α β ≤ Subgroup.normalizer (Q : Set G))
    (hQQa : ¬ Q ≤ Qv α) (hQC : ⁅Q ⊓ Qv α, Mab α β⁆ ≤ Cst β) : False := by
  obtain ⟨D⟩ := hs.exists_dict5 hA hβ
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  have hαβ : α ∈ nbrs β := nbrs_symm hβ
  have hCQ : Cst β ≤ Qv α := by
    intro c hc
    rw [← hs.centralizer_Zv hA hs.vα]
    exact Subgroup.mem_inf.mpr ⟨Qv_le_stab_of_mem_nbrs hA hαβ (Subgroup.mem_inf.mp hc).1,
      Subgroup.centralizer_le (Sit43.Zv_le_Vn hβ) (Subgroup.mem_inf.mp hc).2⟩
  have hE : EndHyp (stab α) (Qv α) (Zv α) (Wcomm α) (Cst β) (Mcent α) (Zv β)
      (stab α ⊓ stab β) (Mab α β) Q D.ψ :=
    { surj := D.surj
      ker := fun x hx => (D.ker_iff x).mp hx
      mem_Mab := fun x => Sit43.mem_Mab_iff D x
      Mab_le := Mab_le_stab α β
      max := fun _ h1 h2 => hs.Mab_eq_or_eq_stab hA hβ h1 h2
      Za_le := hZW
      W_le := (Wcomm_le_Wn α).trans (hs.Wn_le_Qv hA hb)
      Qa_le := hs.Qv_le_Mab hA hβ
      Qa_cent := Qv_le_centralizer_Zv hA α
      comm_mem := fun w hw q hq => by
        have h1 := hcomm (Subgroup.commutator_mem_commutator hw hq)
        rwa [commutatorElement_def] at h1
      norm_W := stab_le_normalizer_Wcomm α
      norm_Qa := le_normalizer_pCoreOf 2 (stab α)
      C_le := hCQ
      Mc_eq := rfl
      Mc_le := hMC
      not_C_le := hCM
      P_le := hs.stab_inf_le_Mab hA hβ
      P_two := (sylow_stab_inf_left hA hβ).2.1
      Za_two := IsPGroup.of_card (n := 4) (by rw [hs.card_Zv_false hs.vα]; norm_num)
      P_norm_C := hPC
      Mab_norm_C := hMabC
      relIndex_U := by
        rw [Subgroup.inf_relIndex_left]
        exact hW
      Zb_eq := (hs.Zv_inf_centralizer hA h26 hβv hαβ).le
      card_Zb := hs.card_Zv_true hA h26 hβv
      Zb_le := hs.Zv_le_Zv_nbr hA h26 hβv hαβ
      Mab_cent_Zb := Mab_le_centralizer_Zv hA h26 hs hβ
      center := hs.centerOf_eq_bot hA h26 hs.vα hβ
      Q_le := hQP
      Mab_norm_Q := hMabQ
      not_Q_le := hQQa
      comm_Q := hQC
      irred := fun N h1 h2 h3 => hsec.irred N h1 h2 h3
      relIndex_Za := by
        rw [hsec.relIndex_eq]
        norm_num }
  exact hE.false

theorem final_contradiction (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) {α : Geo H M}
    (hs : Sit43 α) (hb : 3 ≤ bMin H M) {β : Geo H M} (hβ : β ∈ nbrs α) (h : Hyp18 α β)
    (h19 : Out19 α β) (h20 : Out20 α β) : False := by
  have hQP : Qgrp α β ≤ stab α ⊓ stab β := by
    unfold Qgrp cSecIn
    exact (Subgroup.closure_le _).mpr fun x hx => hx.1
  have hQQa : ¬ Qgrp α β ≤ Qv α := fun hle => by
    have h1 := h20.relIndex_inf
    rw [inf_eq_left.mpr hle, h20.relIndex_C_Q] at h1
    exact absurd h1 (by norm_num)
  refine final_contradiction_of hA h26 hs hb hβ h.sec (by rw [← h.inf_eq]; exact inf_le_right)
    ((Subgroup.commutator_mono (EvenFin.Wcomm_le_Wn α) le_rfl).trans h.comm_Wn_Qv)
    h19.M_le_C h20.not_C_le_M h20.relIndex_W
    ((inf_le_right.trans le_sup_right).trans h20.C_normal) (le_sup_left.trans h20.C_normal)
    hQP (le_sup_left.trans h20.Q_normal) hQQa h20.comm_le

end CFSG.Quasithin.F53.Stellmacher.S43.Even
