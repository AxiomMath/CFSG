module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseB
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseModD

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits
open CFSG.Quasithin.EmptyFaithful.Stellmacher.OrdinaryProofs
open scoped commutatorElement

namespace F53.Stellmacher.S43

open CosetGeom

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

namespace Sit43

variable {α : Geo H M}

theorem exists_dict (hA : F53Amalgam H M S) (hs : Sit43 α) {δ : Geo H M} (hδ : δ ∈ nbrs α) :
    Nonempty (Dict5 (stab α) (stab α ⊓ stab δ) (Zv α)) :=
  nonempty_dict5 (quot_stab_five hA hs.vα) (sylow_stab_inf_left hA hδ) hs.orth

omit [Finite G] in
theorem Vn_le_Qv (hs : Sit43 α) {δ : Geo H M} (hδ : δ ∈ nbrs α) :
    Vn δ ≤ Qv δ := by
  have hδv : vtype δ = true := vtype_true_of_adj hs.vα hδ
  refine iSup₂_le fun l hl => ?_
  have hlv : vtype l = false := vtype_false_of_adj hδv hl
  refine hs.Zv_le_Qv_of_dist_lt_false hlv ?_
  rw [dist_eq_one_iff_adj.mpr (nbrs_symm hl)]
  exact hs.b1

omit [Finite G] in
theorem Zv_le_Vn {δ : Geo H M} (hδ : δ ∈ nbrs α) : Zv α ≤ Vn δ :=
  le_iSup₂_of_le (f := fun (m : Geo H M) (_ : m ∈ nbrs δ) => Zv m) α (nbrs_symm hδ) le_rfl

theorem S13 (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) {δ : Geo H M}
    (hδ : δ ∈ nbrs α) {N : Subgroup G} (hN : stab α ≤ Subgroup.normalizer (N : Set G))
    (hZN : Zv α ≤ N) (hNV : N ≤ Vn δ) : N = Zv α := by
  obtain ⟨D⟩ := hs.exists_dict hA hδ
  have hδv : vtype δ = true := vtype_true_of_adj hs.vα hδ
  have hαδ : α ∈ nbrs δ := nbrs_symm hδ
  have hNQ : N ≤ Qv δ := hNV.trans (hs.Vn_le_Qv hδ)
  have hNX : N ≤ stab α := hNQ.trans (Qv_le_stab_of_mem_nbrs hA hαδ)
  have hN2 : IsPGroup 2 N := (pCoreOf_isPGroup (r := 2) (stab δ)).to_le hNQ
  have hc := hs.centerOf_eq_bot hA h26 hs.vα hδ
  have hcen : N ⊓ Subgroup.centralizer (stab α : Set G) = ⊥ := by
    rw [eq_bot_iff, ← hc]
    exact fun g hg => ⟨hNX hg.1, hg.2⟩
  have hQs : Qst δ ≤ stab α := inf_le_left.trans (Qv_le_stab_of_mem_nbrs hA hαδ)
  have hKN : ∀ n ∈ N, ∀ k ∈ Qst δ, ⁅n, k⁆ ∈ Zv α := fun n hn k hk =>
    Yv_le_Zv hαδ (hs.comm_Vn_Qst hA h26 hδv hαδ ▸
      Subgroup.commutator_mem_commutator (hNV hn) hk)
  have hYc := hs.Yv_eq_comm_comm hA h26 hδv hαδ
  have hKodd : ∃ k ∈ Qst δ, ∃ hk : k ∈ stab α, D.ψ ⟨k, hk⟩ = Equiv.swap 0 2 := by
    have hTh : (Equiv.swap 0 2 : Equiv.Perm (Fin 5)) ∈ S5That :=
      Subgroup.subset_closure (by simp)
    have hSyl : (Equiv.swap 0 2 : Equiv.Perm (Fin 5)) ∈ D.bar (stab α ⊓ stab δ) := by
      rw [D.bar_S]; exact S5That_le_S5Syl hTh
    obtain ⟨x, hxS, hxψ⟩ := (D.mem_bar_iff _).mp hSyl
    have hxC : (x : G) ∈ (stab α ⊓ stab δ) ⊓ Subgroup.centralizer (Yv δ : Set G) := by
      rw [hYc]
      exact (D.mem_centralizer_Y_iff x).mpr (by rw [hxψ]; exact hTh)
    rw [← hs.Qv_sup_Qst hA h26 hδv hαδ] at hxC
    obtain ⟨q, hq, a, ha, hqa⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes
      (((inf_le_left : Qst δ ≤ Qv δ).trans (Qv_le_stab_of_mem_nbrs hA hαδ)).trans
        (le_normalizer_pCoreOf 2 (stab α)))).mp hxC
    have hqX : q ∈ stab α := pCoreOf_le 2 _ hq
    refine ⟨a, ha, hQs ha, ?_⟩
    have h1 : D.ψ ⟨q, hqX⟩ = 1 := (D.ker_iff _).mpr hq
    have h2 : x = ⟨q, hqX⟩ * ⟨a, hQs ha⟩ := Subtype.ext hqa
    rw [← hxψ, h2, map_mul, h1, one_mul]
  exact D.eq_of_normalised_comm
    (fun a ha b hb => comm_of_mem_isElemAbelian (isElemAbelian_Zv hA α) ha hb)
    (fun q hq z hz => (Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hA α hq) z hz).symm)
    (stab_le_normalizer_Zv hA α) (hs.card_Zv_false hs.vα) hN hNX hN2 hZN hcen hKN hKodd
    (hs.card_Yv hA h26 hδv) (fun n hn t ht => hs.comm_Vn_Qst hA h26 hδv hαδ ▸
      Subgroup.commutator_mem_commutator (hNV hn) (Qv_inf_Qv_le_Qst hA hαδ ht))
    (hs.relIndex_Qv_Qv hA h26 hs.vα hδ)

omit [Finite G] in
theorem le_normalizer_of_conj_mem {L N : Subgroup G} (h : ∀ l ∈ L, ∀ n ∈ N, l * n * l⁻¹ ∈ N) :
    L ≤ Subgroup.normalizer (N : Set G) := by
  intro l hl
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨fun hx => h l hl x hx, fun hx => ?_⟩
  have := h l⁻¹ (L.inv_mem hl) _ hx
  simpa [mul_assoc] using this

theorem S13' (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) {E : Subgroup G}
    (hE : stab α ≤ Subgroup.normalizer (E : Set G)) (hZE : Zv α ≤ E)
    (hEL : ⁅E, Lres α⁆ ≤ Zv α) {δ : Geo H M} (hδ : δ ∈ nbrs α) : Vn δ ⊓ E = Zv α := by
  have hZN : Zv α ≤ Vn δ ⊓ E := le_inf (Zv_le_Vn hδ) hZE
  have hLn : Lres α ≤ Subgroup.normalizer ((Vn δ ⊓ E : Subgroup G) : Set G) := by
    refine le_normalizer_of_conj_mem fun l hl n hn => ?_
    have hz : l * n * l⁻¹ * n⁻¹ ∈ Zv α := by
      have h1 := (Zv α).inv_mem (hEL (Subgroup.commutator_mem_commutator hn.2 hl))
      have e : ⁅n, l⁆⁻¹ = l * n * l⁻¹ * n⁻¹ := by simp only [commutatorElement_def]; group
      rwa [e] at h1
    have h2 : l * n * l⁻¹ = (l * n * l⁻¹ * n⁻¹) * n := by group
    rw [h2]
    exact (Vn δ ⊓ E).mul_mem (hZN hz) hn
  have hSn : stab α ⊓ stab δ ≤ Subgroup.normalizer ((Vn δ ⊓ E : Subgroup G) : Set G) := by
    intro s hs'
    rw [Subgroup.mem_normalizer_iff]
    intro x
    have h1 := Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Vn δ hs'.2) x
    have h2 := Subgroup.mem_normalizer_iff.mp (hE hs'.1) x
    exact ⟨fun h => Subgroup.mem_inf.mpr ⟨h1.mp (Subgroup.mem_inf.mp h).1,
      h2.mp (Subgroup.mem_inf.mp h).2⟩, fun h => Subgroup.mem_inf.mpr
      ⟨h1.mpr (Subgroup.mem_inf.mp h).1, h2.mpr (Subgroup.mem_inf.mp h).2⟩⟩
  have hX : stab α ≤ oTwoRes (stab α) ⊔ (stab α ⊓ stab δ) :=
    le_oTwoRes_sup_of_isSylowTwoOf (sylow_stab_inf_left hA hδ)
  exact hs.S13 hA h26 hδ ((hX.trans (sup_le hLn hSn))) hZN inf_le_left

end Sit43

end F53.Stellmacher.S43

end CFSG.Quasithin
