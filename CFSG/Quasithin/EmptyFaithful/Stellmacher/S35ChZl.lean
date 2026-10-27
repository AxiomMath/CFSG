module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChSyl
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.Ch

open S35.Std S35.Fin

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem index_ptStab (p : Fin 5) : (ptStab p).index = 5 := by
  unfold ptStab
  rw [MulAction.index_stabilizer_of_transitive]
  simp

theorem ptStab_ne_top (p : Fin 5) : ptStab p ≠ ⊤ := fun h => by
  have := index_ptStab p
  rw [h, Subgroup.index_top] at this
  omega

theorem cj_ptStab (g : Perm (Fin 5)) (p : Fin 5) : cj g (ptStab p) = ptStab (g p) := by
  ext σ
  rw [mem_cj, mem_ptStab, mem_ptStab]
  simp only [Perm.mul_apply]
  constructor
  · intro h
    have := congrArg g h
    simpa using this
  · intro h
    rw [Equiv.Perm.inv_def]
    simp [h]

theorem cj_cj_inv' (g : Perm (Fin 5)) (B : Subgroup (Perm (Fin 5))) :
    cj g (cj g⁻¹ B) = B := by
  ext x
  rw [mem_cj, mem_cj]
  simp [mul_assoc]

theorem le_ptStab_of_le {D R : Subgroup (Perm (Fin 5))} (hD : Nat.card D = 8) (hDR : D ≤ R)
    (hne : R ≠ ⊤) : R ≤ ptStab (fixPt D) := by
  obtain ⟨g, rfl⟩ := exists_cj hD
  have hp : fixPt (cj g S5Syl) = g 4 := fixPt_eq hD (isFixPt_cj_std_iff.mpr rfl)
  rw [hp, ← cj_ptStab]
  have h1 : S5Syl ≤ cj g⁻¹ R := by
    intro s hs
    rw [mem_cj]
    apply hDR
    rw [mem_cj]
    simpa [mul_assoc] using hs
  have h2 : cj g⁻¹ R ≠ ⊤ := by
    intro h
    apply hne
    rw [eq_top_iff]
    intro x _
    have : x ∈ cj g (cj g⁻¹ R) := by rw [h, mem_cj]; exact Subgroup.mem_top _
    rwa [cj_cj_inv'] at this
  have h3 := S34.C3b.le_S4pt_of_syl_le h1 h2
  have h4 : R ≤ cj g (cj g⁻¹ R) := by rw [cj_cj_inv']
  refine h4.trans ?_
  intro x hx
  rw [mem_cj] at hx ⊢
  exact h3 hx

theorem zpowers_vp_inj {p q : Fin 5} (h : Subgroup.zpowers (vp p) = Subgroup.zpowers (vp q)) :
    p = q := by
  apply vp_injective
  have : vp p ∈ Subgroup.zpowers (vp q) := h ▸ Subgroup.mem_zpowers _
  rcases (mem_zpowers_iff_of_mul_self (vp_mul_self q)).mp this with h2 | h2
  · exact absurd h2 (vp_ne_one p)
  · exact h2

omit [Finite G] in
theorem card_eq_relIndex_mul {A B : Subgroup G} (h : A ≤ B) :
    Nat.card B = A.relIndex B * Nat.card A := by
  have := Subgroup.relIndex_mul_card (H := A) (K := B)
  rw [inf_eq_left.mpr h] at this
  exact this.symm

theorem comm_mem_Zv_nbr (hS : Sit H M S) {δ l : Geo H M} (hδ : vtype δ = false)
    (hl : l ∈ nbrs δ) {a z : G} (ha : a ∈ stab δ ⊓ stab l) (hz : z ∈ Zv l) :
    a * z * a⁻¹ * z⁻¹ ∈ Zv δ := by
  have h1 := Subgroup.commutator_mem_commutator (Subgroup.mem_zpowers a) hz
  rw [Subgroup.commutator_comm] at h1
  have h2 := S34.aon_edge hS.glob hδ hl (g := a) ⟨ha.2, ha.1⟩
  have h3 : ⁅Zv l, Subgroup.zpowers a⁆ ≤ Zv δ := by
    by_cases hq : a ∈ Qv l
    · rw [h2.1 hq]; exact bot_le
    · rw [h2.2 hq]
  have h4 := h3 h1
  rwa [commutatorElement_def] at h4

namespace Chart

variable {δ : Geo H M} (c : Chart δ)

include c

theorem Zv_nbr_le_fixSecIn (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ) :
    Zv l ≤ fixSecIn (stab δ ⊓ stab l) (Zv δ) (Vn δ) := by
  intro z hz
  have hzV : z ∈ Vn δ := Zv_le_Vn hl hz
  refine (c.mem_fixSecIn_iff inf_le_left ⟨z, hzV⟩).mpr ?_
  rw [mem_fixW]
  intro σ hσ
  obtain ⟨a, ha, rfl⟩ := (c.mem_bar_iff).mp hσ
  exact (c.comm_mem_iff a ⟨z, hzV⟩).mp (comm_mem_Zv_nbr hS hδ hl ha hz)

theorem Zv_nbr_eq_fixSecIn (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M}
    (hl : l ∈ nbrs δ) : Zv l = fixSecIn (stab δ ⊓ stab l) (Zv δ) (Vn δ) := by
  set F := fixSecIn (stab δ ⊓ stab l) (Zv δ) (Vn δ) with hF
  have hZl := Zv_le_Zv_of_nbr hS hδ hl
  have hlF := c.Zv_nbr_le_fixSecIn hS hδ hl
  have hFV : F ≤ Vn δ := fixSecIn_le_Vn _
  have hZF : Zv δ ≤ F := c.Zv_le_fixSecIn inf_le_left
  have h1 : (Zv δ).relIndex F = 2 := by
    rw [← c.card_img hZF hFV, hF, c.img_fixSecIn inf_le_left]
    exact card_fixW_sylow (c.card_Dl hS hl)
  have h2 : (Zv δ).relIndex (Zv l) = 2 := by
    have := card_eq_relIndex_mul hZl
    rw [hS.cardZ3 l (vtype_nbr_S5 hδ hl), hS.cardZ5 δ hδ] at this
    omega
  have h3 := Subgroup.relIndex_mul_relIndex (Zv δ) (Zv l) F hZl hlF
  rw [h1, h2] at h3
  have h4 : (Zv l).relIndex F = 1 := by omega
  exact le_antisymm hlF (Subgroup.relIndex_eq_one.mp h4)

theorem img_Zv_nbr (hS : Sit H M S) (hδ : vtype δ = false) {l : Geo H M} (hl : l ∈ nbrs δ) :
    c.img (Zv l) = Subgroup.zpowers (vp (fixPt (c.Dl l))) := by
  rw [c.Zv_nbr_eq_fixSecIn hS hδ hl, c.img_fixSecIn inf_le_left]
  exact fixW_sylow (c.card_Dl hS hl) (isFixPt_fixPt (c.card_Dl hS hl))

end Chart

end S35.Ch

end F53.Stellmacher

end CFSG.Quasithin
