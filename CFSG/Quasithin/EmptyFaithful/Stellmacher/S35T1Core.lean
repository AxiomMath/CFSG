module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35T1Gen
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Ch2Cent
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std4

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53

namespace S35.T1

open Equiv S35.Std S35.II S35.Fin S35.Ch2 S35.Ch
open S34 (Cb)

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {β α' m γ' : Geo H M}

@[expose] def Sg (γ' m α' : Geo H M) (hZ : Zv α' ≤ Zv m) (r : G) : Subgroup G where
  carrier := {x | x ∈ Xg γ' m ∧ ⁅r, x⁆ ∈ Zv α'}
  one_mem' := ⟨(Xg γ' m).one_mem, by simp⟩
  mul_mem' := fun {a b} ha hb => by
    refine ⟨(Xg γ' m).mul_mem ha.1 hb.1, ?_⟩
    have e : ⁅r, a * b⁆ = ⁅r, a⁆ * (a * ⁅r, b⁆ * a⁻¹) := by
      simp only [commutatorElement_def]; group
    have hc : a * ⁅r, b⁆ * a⁻¹ = ⁅r, b⁆ := by
      have := (mem_Xg.mp ha.1).2 _ (hZ hb.2)
      rw [mul_inv_eq_iff_eq_mul, ← this]
    rw [e, hc]
    exact (Zv α').mul_mem ha.2 hb.2
  inv_mem' := fun {a} ha => by
    refine ⟨(Xg γ' m).inv_mem ha.1, ?_⟩
    have e : ⁅r, a⁻¹⁆ = a⁻¹ * ⁅r, a⁆⁻¹ * a := by
      simp only [commutatorElement_def]; group
    have hc : a⁻¹ * ⁅r, a⁆⁻¹ * a = ⁅r, a⁆⁻¹ := by
      have := (mem_Xg.mp ha.1).2 _ (hZ ((Zv α').inv_mem ha.2))
      rw [mul_assoc, this, ← mul_assoc, inv_mul_cancel, one_mul]
    rw [e, hc]
    exact (Zv α').inv_mem ha.2

theorem arc_main (hS : Sit H M S) (hp : S34.PD β α') (hb : Back H M β α' m γ')
    (htr : HasTransp β α') (hV : Vn β ≤ That2 α' m)
    (hW : ∀ w ∈ Wb β, ∀ z ∈ Zv α', ⁅w, z⁆ = 1) (hWm : ¬ Wb β ≤ stab m)
    (nbt : NbarThat H M) (rc : RCent H M) (rkz : RkZvEq H M) :
    stab α' ⊓ stab m ≤ (Qv γ' ⊓ Qv m) ⊔ Qv α' := by
  by_contra hcon
  obtain ⟨hm3, hγ5, hne, -, -⟩ := back_facts hp hb
  have hα5 : vtype α' = false := hp.vδ'
  have hm' : m ∈ nbrs α' := hb.1
  have hγm : γ' ∈ nbrs m := hb.2.1
  have hm : m ∈ nbrs γ' := mem_nbrs_symm.mp hγm
  have hαm : α' ∈ nbrs m := mem_nbrs_symm.mp hm'
  obtain ⟨hQT, hTD, hidx⟩ := thatFacts hS α' m hα5 hm'
  have hN1 : That2 α' m ≤ (Qv γ' ⊓ Qv m) ⊔ Qv α' := nbt γ' m α' hγ5 hm hm' hne.symm
  have hNeq : (Qv γ' ⊓ Qv m) ⊔ Qv α' = That2 α' m := by
    rcases eq_or_eq_of_relIndex_two hN1 (arcN_le hS (δ := γ') hm') hidx with h | h
    · exact h
    · exact absurd (h ▸ le_rfl) hcon
  have hNp : Qv γ' ⊓ Qv m ≤ Qv m ⊓ That2 α' m :=
    le_inf inf_le_right (le_sup_left.trans hNeq.le)
  have hT : That2 γ' m ≤ (Qv m ⊓ That2 α' m) ⊔ Qv γ' := by
    refine (nbt α' m γ' hα5 hm' hm hne).trans ?_
    exact sup_le_sup_right (le_inf inf_le_right (inf_le_left.trans hQT)) _
  have hX := Xg_le_sup hS hp hb hW hWm (inf_le_left : Qv m ⊓ That2 α' m ≤ Qv m) hNp hT
  obtain ⟨v, hvV, hvα, hv2⟩ := htr
  obtain ⟨c⟩ := exists_chart2 hS hα5 (δ := α')
  have hv2' : (c.θ ⟨v, hvα⟩).IsSwap :=
    (c.rk_eq_two_iff hvα).mp ((rkz α' hα5 v hvα).symm.trans hv2)
  obtain ⟨x, y, hxy, hxe⟩ := hv2'
  have hex : ∃ w : orth.W, orth.act (swap x y) w ≠ w := by
    by_contra hall
    push Not at hall
    have h1 := eq_one_of_act_eq_self hall
    have := congrArg (fun σ : Perm (Fin 5) => σ x) h1
    simp [Equiv.swap_apply_left, hxy.symm] at this
  obtain ⟨w, hw⟩ := hex
  have hs : orth.act (swap x y) w * w⁻¹ = ep x y := by
    have hmem : orth.act (swap x y) w * w⁻¹ ∈ commW orth (Subgroup.zpowers (swap x y)) ⊤ :=
      Subgroup.subset_closure ⟨_, Subgroup.mem_zpowers _, w, Subgroup.mem_top _, rfl⟩
    rcases (mem_commW_swap_iff hxy _).mp hmem with h | h
    · exact absurd (mul_inv_eq_one.mp h) hw
    · exact h
  obtain ⟨u, hu⟩ := c.π_surj w
  set r : G := v * (u : G) * v⁻¹ * (u : G)⁻¹ with hr
  have hrV : r ∈ Vn α' := (conjV ⟨v, hvα⟩ u * u⁻¹ : ↥(Vn α')).2
  have hπr : c.π ⟨r, hrV⟩ = ep x y := by
    have : (⟨r, hrV⟩ : ↥(Vn α')) = conjV ⟨v, hvα⟩ u * u⁻¹ := rfl
    rw [this, map_mul, map_inv, c.π_conj, hu, hxe]
    exact hs
  have hrR : r ∈ ⁅Vn β, Vn α'⁆ := Subgroup.commutator_mem_commutator hvV u.2
  have hrβ : r ∈ Vn β := (PD_comm_le hS hp hrR).1
  have hZ : Zv α' ≤ Zv m := Zv_le_Zv_of_nbr hS hα5 hm'
  have hWS : Wb β ≤ Sg γ' m α' hZ r := by
    intro w hw
    refine ⟨Wb_le_Xg hS hp hb hW hw, ?_⟩
    have := Subgroup.commutator_mem_commutator hrβ hw
    rw [comm_Vn_Wb hS β, Subgroup.mem_bot] at this
    rw [this]
    exact (Zv α').one_mem
  have hQS : Qv m ⊓ That2 α' m ≤ Sg γ' m α' hZ r := by
    intro q hq
    refine ⟨inf_le_left.trans (Qv_le_Xg hS hγm) hq, ?_⟩
    have h1 := rc β α' m γ' hp hb hV r hrR q hq.2
    rw [← commutatorElement_inv]
    exact (Zv α').inv_mem h1
  have hXS : Xg γ' m ≤ Sg γ' m α' hZ r := hX.trans (sup_le hWS hQS)
  obtain ⟨g0, hg0, hg0ne⟩ := exists_act_ep_ne (c.card_Dl hS hm') hxy
  obtain ⟨a, ha, rfl⟩ := (c.mem_bar_iff).mp hg0
  have haD : (a : G) ∈ Qv α' ⊔ Qv m := by
    rw [← stab_inf_eq hS hα5 hm']
    exact ha
  have hnorm : Qv m ≤ Subgroup.normalizer (Qv α' : Set G) :=
    (Qv_le_stab hS hαm).trans (le_normalizer_pCoreOf 2 (stab α'))
  obtain ⟨n, hn, q, hq, hnq⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hnorm).mp haD
  have hqs : q ∈ stab α' := Qv_le_stab hS hαm hq
  have hns : n ∈ stab α' := Qv_le_stab' α' hn
  have hθq : c.θ a = c.θ ⟨q, hqs⟩ := by
    have : a = ⟨n, hns⟩ * ⟨q, hqs⟩ := Subtype.ext hnq
    rw [this, map_mul, (c.ker_iff hS hα5 ⟨n, hns⟩).mpr hn, one_mul]
  have hqS := hXS (Qv_le_Xg hS hγm hq)
  have hqc : q * r * q⁻¹ * r⁻¹ ∈ Cb α' := by
    refine S34.Zv_le_Cb hS.glob hα5 ?_
    have : q * r * q⁻¹ * r⁻¹ = ⁅q, r⁆ := rfl
    rw [this, ← commutatorElement_inv]
    exact (Zv α').inv_mem hqS.2
  have := (c.comm_mem_iff ⟨q, hqs⟩ ⟨r, hrV⟩).mp hqc
  rw [hπr, ← hθq] at this
  exact hg0ne this

end S35.T1

end F53.Stellmacher

end CFSG.Quasithin
