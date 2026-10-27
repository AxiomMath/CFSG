module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddThreeB
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43OddLoc

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits Equiv
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

namespace Odd

namespace Three

private theorem commTwoF_inter : ∀ w : orth.W, w ∈ commTwoF →
    orth.act (swap 1 2 * swap 3 4) w ∈ commTwoF → w = 1 := by
  decide +kernel

theorem commIter_two_inter : ∀ w ∈ F53Mod.commIter orth S5Syl 2,
    orth.act (swap 1 2 * swap 3 4) w ∈ F53Mod.commIter orth S5Syl 2 → w = 1 := by
  intro w hw hw'
  rw [mem_commIter_two_iff] at hw hw'
  exact commTwoF_inter w hw hw'

theorem conj_swap_four_ne :
    ((swap 1 2 * swap 3 4) * swap 1 3 * (swap 1 2 * swap 3 4)⁻¹ : Perm (Fin 5)) 4 ≠ 4 := by
  decide

end Three

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G} {α : Geo H M}

open Three in
theorem exists_nbr_Yv_inf (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    {β : Geo H M} (hβ : β ∈ nbrs α) :
    ∃ α' ∈ nbrs α, Yv β ⊓ Yv α' = ⊥ ∧ (stab α ⊓ stab β) ⊔ Qst α' = stab α := by
  have hβv := Sit43.vtype_true_of_adj hs.vα hβ
  have hαβ : α ∈ nbrs β := nbrs_symm hβ
  obtain ⟨D⟩ := hs.exists_dict hA hβ
  obtain ⟨g₀, hg₀⟩ := D.surj (swap 1 2 * swap 3 4)
  set g : ↥(H ⊔ M) := ⟨(g₀ : G), stab_le α g₀.2⟩ with hg
  have hgg : (g : G) = (g₀ : G) := rfl
  have hα' : g • β ∈ nbrs α := smul_mem_nbrs_of_mem_stab g g₀.2 hβ
  refine ⟨g • β, hα', ?_, ?_⟩
  · have hYβ : Yv β = (F53Mod.commIter orth S5Syl 2).map D.φ := by
      rw [hs.Yv_eq_comm_comm hA h26 hβv hαβ]
      exact D.comm_comm_eq
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨hy1, hy2⟩ := Subgroup.mem_inf.mp hy
    rw [hYβ] at hy1
    obtain ⟨u, hu, rfl⟩ := hy1
    rw [Yv_smul, mem_conjSub, hgg, hYβ] at hy2
    obtain ⟨u', hu', hu'e⟩ := hy2
    have h1 : D.φ (orth.act (swap 1 2 * swap 3 4) u') = D.φ u := by
      rw [← hg₀, D.act_eq g₀ u', hu'e]
      group
    have h2 := D.inj h1
    have h3 : u' = 1 := commIter_two_inter u' hu' (h2 ▸ hu)
    rw [Subgroup.mem_bot, ← h2, h3, map_one, map_one]
  · have hQα : Qst (g • β) ≤ stab α := fun k hk =>
      Qv_le_stab_of_mem_nbrs hA (nbrs_symm hα') hk.1
    by_contra hne
    have hle := le_Mab (sup_le inf_le_left hQα) le_sup_left hne
    obtain ⟨k₀, hk₀, hk₀α, hψ⟩ := hs.exists_Qst_of_S5That hA h26 hβ D (τ := swap 1 3)
      (Subgroup.subset_closure (Set.mem_insert_of_mem _ (Set.mem_singleton _)))
    have hk : (g₀ : G) * k₀ * (g₀ : G)⁻¹ ∈ Qst (g • β) := by
      rw [Qst_smul, hgg]
      exact mul_mem_conjSub hk₀
    have hkα : (g₀ : G) * k₀ * (g₀ : G)⁻¹ ∈ stab α := hQα hk
    have h4 := (Sit43.mem_Mab_iff D ⟨_, hkα⟩).mp (hle (le_sup_right (b := Qst (g • β)) hk))
    have e : (⟨(g₀ : G) * k₀ * (g₀ : G)⁻¹, hkα⟩ : ↥(stab α)) = g₀ * ⟨k₀, hk₀α⟩ * g₀⁻¹ := rfl
    rw [e, map_mul, map_mul, map_inv, hψ, hg₀] at h4
    exact conj_swap_four_ne h4

open Three in
theorem false_of_caseL_three (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (h3 : bMin H M = 3) {β : Geo H M} (hβ : β ∈ nbrs α) (hL : 2 ^ 7 ≤ Nat.card (Vn β)) :
    False := by
  have hb : 3 ≤ bMin H M := h3.ge
  have hβv := Sit43.vtype_true_of_adj hs.vα hβ
  have hαβ : α ∈ nbrs β := nbrs_symm hβ
  obtain ⟨α', hα', hY, hgen⟩ := exists_nbr_Yv_inf hA h26 hs hβ
  have hα'v := Sit43.vtype_true_of_adj hs.vα hα'
  have hα'α : α ∈ nbrs α' := nbrs_symm hα'
  obtain ⟨x, hxV, hxQ⟩ : ∃ x ∈ Vn α', x ∉ Qv β := by
    by_contra hcon
    push Not at hcon
    exact not_Vn_le_Qv_of_Yv_inf hA h26 hs h3 hβ hα' hY fun x hx => hcon x hx
  have hxQα : x ∈ Qv α := hs.Vn_le_Qv_of_nbr hA h26 hb hs.vα hα' hxV
  have hxE : x ∈ stab α ⊓ stab β := ⟨pCoreOf_le 2 _ hxQα, Qv_le_stab_of_mem_nbrs hA hβ hxQα⟩
  have hxC : x ∈ Subgroup.centralizer (Yv β : Set G) :=
    Subgroup.centralizer_le (Yv_le_Zv hαβ) (Qv_le_centralizer_Zv hA α hxQα)
  set K := ⁅Vn β, Subgroup.zpowers x⁆ with hK
  have hKV : K ≤ Vn β := commutator_zpowers_le_self (stab_le_normalizer_Vn β hxE.2)
  have hKV' : K ≤ Vn α' := by
    have hxn : x ∈ Subgroup.normalizer (Vn α' : Set G) :=
      stab_le_normalizer_Vn α' (pCoreOf_le 2 _ (hs.Vn_le_Qv_of_true hα'v hxV))
    refine commutator_zpowers_le hxn fun v hv => ?_
    have hvα' : v ∈ stab α' :=
      Qv_le_stab_of_mem_nbrs hA hα' (hs.Vn_le_Qv_of_nbr hA h26 hb hs.vα hβ hv)
    have e : ⁅v, x⁆ = (v * x * v⁻¹) * x⁻¹ := by simp only [commutatorElement_def]
    rw [e]
    exact (Vn α').mul_mem ((Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn α' hvα') x).mp
      hxV) ((Vn α').inv_mem hxV)
  have hN1 : stab α ⊓ stab β ≤ Subgroup.normalizer ((K ⊔ Zv α : Subgroup G) : Set G) := by
    have hE : K ⊔ Zv α = (K ⊔ Yv β) ⊔ Zv α := by
      rw [sup_assoc, sup_eq_right.mpr (Yv_le_Zv hαβ)]
    rw [hE]
    exact F1.le_normalizer_sup (edge_le_normalizer_comm_sup hA h26 hs hs.vα hβ hxE hxC hxQ)
      (inf_le_left.trans (stab_le_normalizer_Zv hA α))
  have hN2 : Qst α' ≤ Subgroup.normalizer ((K ⊔ Zv α : Subgroup G) : Set G) := by
    refine le_normalizer_of_conjSub_le fun k hk => ?_
    have hkα : k ∈ stab α := Qv_le_stab_of_mem_nbrs hA hα'α hk.1
    rw [conjSub_sup, F1.conjSub_eq_of_mem_normalizer (stab_le_normalizer_Zv hA α hkα)]
    refine sup_le (fun z hz => ?_) le_sup_right
    rw [mem_conjSub] at hz
    have h1 : ⁅k⁻¹ * z * k, k⁆ ∈ Yv α' := hs.comm_Vn_Qst hA h26 hα'v hα'α ▸
      Subgroup.commutator_mem_commutator (hKV' hz) hk
    have e : z = ⁅k⁻¹ * z * k, k⁆⁻¹ * (k⁻¹ * z * k) := by
      simp only [commutatorElement_def]; group
    rw [e]
    exact Subgroup.mul_mem _ (Subgroup.mem_sup_right ((Yv_le_Zv hα'α) (Subgroup.inv_mem _ h1)))
      (Subgroup.mem_sup_left hz)
  have hNα : stab α ≤ Subgroup.normalizer ((K ⊔ Zv α : Subgroup G) : Set G) := by
    rw [← hgen]
    exact sup_le hN1 hN2
  have hKZ : K ≤ Zv α := le_Zv_of_normalized hA h26 hs hs.vα hβ hKV hNα
  have h64 := (hs.comm_le_Zv_iff hA h26 hb hβv hαβ hxE hxC hxQ).mp hKZ
  rw [h64] at hL
  norm_num at hL

end Odd

end F53.Stellmacher.S43

end CFSG.Quasithin
