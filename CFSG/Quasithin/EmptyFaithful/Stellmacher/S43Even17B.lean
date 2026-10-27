module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S43BaseE2

public section

namespace CFSG.Quasithin.F53.Stellmacher.S43.Even.E17

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod CosetGeom
open CFSG.LieType.BorelTits
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem mem_normalizer_of_conj_mem {x : G} {N : Subgroup G} (h : ∀ n ∈ N, x * n * x⁻¹ ∈ N) :
    x ∈ Subgroup.normalizer (N : Set G) := by
  apply mem_normalizer_of_conjSub_eq
  have hle : conjSub x N ≤ N := by
    rintro _ ⟨n, hn, rfl⟩
    exact h n hn
  exact Subgroup.eq_of_le_of_card_ge hle (by rw [card_conjSub])

theorem mem_normalizer_of_comm_mem {x : G} {N Z : Subgroup G} (hZN : Z ≤ N)
    (h : ∀ n ∈ N, x * n * x⁻¹ * n⁻¹ ∈ Z) : x ∈ Subgroup.normalizer (N : Set G) :=
  mem_normalizer_of_conj_mem fun n hn => by
    have e : x * n * x⁻¹ = (x * n * x⁻¹ * n⁻¹) * n := by group
    rw [e]
    exact N.mul_mem (hZN (h n hn)) hn

omit [Finite G] in
theorem comm_mul_eq (x a b : G) :
    x * (a * b) * x⁻¹ * (a * b)⁻¹ = (x * a * x⁻¹ * a⁻¹) * (a * (x * b * x⁻¹ * b⁻¹) * a⁻¹) := by
  group

namespace Sit43'

variable {α : Geo H M}

theorem sup_eq_Wn (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) {δ : Geo H M}
    (hδ : δ ∈ nbrs α) {E : Subgroup G} (hEW : E ≤ Wn α)
    (hn : stab α ≤ Subgroup.normalizer ((Vn δ ⊔ E : Subgroup G) : Set G)) :
    Vn δ ⊔ E = Wn α := by
  apply le_antisymm (sup_le (hs.Vn_le_Wn hA h26 hδ) hEW)
  rw [hs.Wn_eq_iSup_conj hA h26 hs.vα hδ]
  refine iSup₂_le fun g hg => ?_
  rintro _ ⟨v, hv, rfl⟩
  exact (Subgroup.mem_normalizer_iff.mp (hn hg) v).mp (le_sup_left (a := Vn δ) hv)

theorem not_stab_le_normalizer_Vn (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb : 3 ≤ bMin H M) {δ : Geo H M} (hδ : δ ∈ nbrs α)
    (hn : stab α ≤ Subgroup.normalizer (Vn δ : Set G)) : False := by
  have hU : Vn δ ≤ stab α ⊓ stab δ := le_inf
    ((hs.Vn_le_Qv_of_nbr hA h26 hb hs.vα hδ).trans (pCoreOf_le 2 _))
    ((hs.Vn_le_Qv hδ).trans (pCoreOf_le 2 _))
  have hbot := eq_bot_of_normalizes_both hA (show (graph (H ⊔ M) H M).Adj α δ from hδ) hU hn
    (stab_le_normalizer_Vn δ)
  exact Zv_ne_bot hA α (le_bot_iff.mp (hbot ▸ Sit43.Zv_le_Vn hδ))

theorem Vn_le_Qv₂ (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α)
    (hb4 : bMin H M = 4) {β α₂ δ : Geo H M} (hβ : β ∈ nbrs α) (h2 : α₂ ∈ nbrs β)
    (d2 : dist α α₂ = 2) (hδ : δ ∈ nbrs α) (hYY : Yv δ ⊓ Yv β = ⊥) : Vn δ ≤ Qv α₂ := by
  have hG := hA.amalgam.gen
  have hδv : vtype δ = true := Sit43.vtype_true_of_adj hs.vα hδ
  have hβv : vtype β = true := Sit43.vtype_true_of_adj hs.vα hβ
  have h2v : vtype α₂ = false := hs.vtype_of_dist_two hA (by rw [CosetGeom.dist_comm]; exact d2)
  have dδ : dist α δ = 1 := dist_eq_one_iff_adj.mpr hδ
  have dβ : dist α β = 1 := dist_eq_one_iff_adj.mpr hβ
  have d2β : dist β α₂ = 1 := dist_eq_one_iff_adj.mpr h2
  have hl : ∀ l ∈ nbrs δ, vtype l = false ∧ dist l α₂ ≤ 4 ∧ dist l β ≤ 3 := by
    intro l hl
    have dl : dist l δ = 1 := dist_eq_one_iff_adj.mpr (nbrs_symm hl)
    have t1 := CosetGeom.dist_triangle hG l δ α₂
    have t2 := CosetGeom.dist_triangle hG δ α α₂
    have t3 := CosetGeom.dist_triangle hG l δ β
    have t4 := CosetGeom.dist_triangle hG δ α β
    rw [CosetGeom.dist_comm δ α] at t2 t4
    exact ⟨Sit43.vtype_false_of_adj hδv hl, by omega, by omega⟩
  have hV2 : Vn δ ≤ stab α₂ := iSup₂_le fun l hl' =>
    hs.Zv_le_stab_of_dist_le_false hA (hl l hl').1 (by rw [hb4]; exact (hl l hl').2.1)
  have hVβ : Vn δ ≤ Qv β := iSup₂_le fun l hl' =>
    hs.Zv_le_Qv_of_dist_lt_false (hl l hl').1 (by rw [hb4]; have := (hl l hl').2.2; omega)
  have hZQδ : Zv α₂ ≤ Qv δ := by
    refine hs.Zv_le_Qv_of_dist_lt_false h2v ?_
    have t := CosetGeom.dist_triangle hG α₂ α δ
    rw [CosetGeom.dist_comm α₂ α] at t
    omega
  have hZQα : Zv α₂ ≤ Qv α :=
    hs.Zv_le_Qv_of_dist_lt_false h2v (by rw [CosetGeom.dist_comm]; omega)
  have hZst : Zv α₂ ≤ Qst δ := fun z hz => ⟨hZQδ hz, Subgroup.mem_centralizer_iff.mpr fun y hy =>
    Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hA α (hZQα hz)) y
      (Yv_le_Zv (nbrs_symm hδ) hy)⟩
  have h1 : ⁅Vn δ, Zv α₂⁆ ≤ Yv δ := by
    rw [← hs.comm_Vn_Qst hA h26 hδv (nbrs_symm hδ)]
    exact Subgroup.commutator_mono le_rfl hZst
  have hVα : Vn δ ≤ Qv α := hs.Vn_le_Qv_of_nbr hA h26 (by omega) hs.vα hδ
  have hVst : Vn δ ≤ Qst β := fun v hv => ⟨hVβ hv, Subgroup.mem_centralizer_iff.mpr fun y hy =>
    Subgroup.mem_centralizer_iff.mp (Qv_le_centralizer_Zv hA α (hVα hv)) y
      (Yv_le_Zv (nbrs_symm hβ) hy)⟩
  have h2' : ⁅Vn δ, Zv α₂⁆ ≤ Yv β := by
    rw [Subgroup.commutator_comm, ← hs.comm_Vn_Qst hA h26 hβv (nbrs_symm hβ)]
    exact Subgroup.commutator_mono (Sit43.Zv_le_Vn_nbrs h2) hVst
  have hbot : ⁅Vn δ, Zv α₂⁆ = ⊥ := le_bot_iff.mp (hYY ▸ le_inf h1 h2')
  have hC : Vn δ ≤ Subgroup.centralizer (Zv α₂ : Set G) :=
    Subgroup.commutator_eq_bot_iff_le_centralizer.mp hbot
  rw [← hs.centralizer_Zv hA h2v]
  exact le_inf hV2 hC

theorem relIndex_Vn_le_two (hA : F53Amalgam H M S) {α₂ α₃ α' δ : Geo H M}
    (h2v : vtype α₂ = false) (h3 : α₃ ∈ nbrs α₂) (h' : α' ∈ nbrs α₃) (hV : Vn δ ≤ Qv α₂) :
    (Vn δ ⊓ stab α').relIndex (Vn δ) ≤ 2 := by
  have hQ : Qv α₂ ≤ stab α₂ ⊓ stab α₃ := le_inf (pCoreOf_le 2 _) (Qv_le_stab_of_mem_nbrs hA h3)
  have h2 := Sit43.relIndex_Qv_edge hA h2v h3
  have hQ' : Qv α₃ ≤ stab α' := Qv_le_stab_of_mem_nbrs hA h'
  calc (Vn δ ⊓ stab α').relIndex (Vn δ) ≤ (Vn δ ⊓ Qv α₃).relIndex (Vn δ) :=
        Subgroup.relIndex_le_of_le_left (inf_le_inf_left _ hQ')
          ((relIndex_ne_zero_of_finite _ _))
    _ = (Qv α₃).relIndex (Vn δ) := by rw [inf_comm, Subgroup.inf_relIndex_right]
    _ ≤ (Qv α₃).relIndex (stab α₂ ⊓ stab α₃) :=
        Subgroup.relIndex_le_of_le_right (hV.trans hQ) (by rw [h2]; norm_num)
    _ = 2 := h2

theorem two_classes (hA : F53Amalgam H M S) (h26 : Hss26AAt H M) (hs : Sit43 α) {δ α' : Geo H M}
    (hδ : δ ∈ nbrs α) {x : G} (hb : 3 ≤ bMin H M)
    (hxH : ∀ h ∈ Wn α ⊓ stab α', h * x * h⁻¹ * x⁻¹ ∈ Zv α)
    (h2 : (Vn δ ⊓ stab α').relIndex (Vn δ) ≤ 2) :
    ∀ v₁ ∈ Vn δ, ∀ v₂ ∈ Vn δ, x * v₁ * x⁻¹ * v₁⁻¹ ∉ Zv α → x * v₂ * x⁻¹ * v₂⁻¹ ∉ Zv α →
      (x * v₁ * x⁻¹ * v₁⁻¹)⁻¹ * (x * v₂ * x⁻¹ * v₂⁻¹) ∈ Zv α := by
  have hK : ∀ v ∈ Vn δ ⊓ stab α', x * v * x⁻¹ * v⁻¹ ∈ Zv α := by
    intro v hv
    have h1 := (Zv α).inv_mem (hxH v ⟨hs.Vn_le_Wn hA h26 hδ hv.1, hv.2⟩)
    have e : (v * x * v⁻¹ * x⁻¹)⁻¹ = x * v * x⁻¹ * v⁻¹ := by group
    rwa [e] at h1
  intro v₁ hv₁ v₂ hv₂ h₁ h₂
  have hn₁ : v₁ ∉ Vn δ ⊓ stab α' := fun h => h₁ (hK v₁ h)
  have hn₂ : v₂ ∉ Vn δ ⊓ stab α' := fun h => h₂ (hK v₂ h)
  have hpos : 0 < (Vn δ ⊓ stab α').relIndex (Vn δ) :=
    Nat.pos_of_ne_zero (relIndex_ne_zero_of_finite _ _)
  have h2' : (Vn δ ⊓ stab α').relIndex (Vn δ) = 2 := by
    rcases (by omega : (Vn δ ⊓ stab α').relIndex (Vn δ) = 1 ∨
      (Vn δ ⊓ stab α').relIndex (Vn δ) = 2) with h | h
    · exact absurd (Subgroup.relIndex_eq_one.mp h hv₁) hn₁
    · exact h
  have hm := hK _ (inv_mul_mem_of_relIndex_two h2' hv₁ hv₂ hn₁ hn₂)
  have e := comm_mul_eq x v₁ (v₁⁻¹ * v₂)
  rw [mul_inv_cancel_left] at e
  rw [e, ← mul_assoc, inv_mul_cancel, one_mul]
  have hv₁α : v₁ ∈ stab α :=
    (hs.Vn_le_Qv_of_nbr hA h26 hb hs.vα hδ).trans (pCoreOf_le 2 _) hv₁
  exact (Subgroup.mem_normalizer_iff.mp (stab_le_normalizer_Zv hA α hv₁α) _).mp hm

end Sit43'

end CFSG.Quasithin.F53.Stellmacher.S43.Even.E17
