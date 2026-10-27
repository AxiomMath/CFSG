module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35FnChart
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChCent
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChFin
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35ChMbl

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

theorem card_ptStab (p : Fin 5) : Nat.card (ptStab p) = 24 := by
  have h := Subgroup.card_mul_index (ptStab p)
  have h5 : Nat.card (Fin 5) = 5 := by simp
  rw [index_ptStab, Nat.card_perm, h5] at h
  norm_num [Nat.factorial] at h
  omega

theorem inf_eq_Qv (hC : Ctx H M S) {β : Geo H M} (hβ : vtype β = false) {x : G}
    (hx : x ∈ stab β) (h : ∀ l ∈ nbrs β, x ∈ Subgroup.normalizer (Zv l : Set G)) :
    x ∈ Qv β := by
  obtain ⟨c⟩ := hC.nonempty_chart hβ
  rw [← c.iInf_Mbl hC.sit hβ]
  exact Subgroup.mem_iInf.mpr fun l => Subgroup.mem_iInf.mpr fun hl => ⟨h l hl, hx⟩

theorem exists_normalizer_not_mem_stab (hC : Ctx H M S) {β l : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) : ∃ y ∈ stab β, y ∈ Subgroup.normalizer (Zv l : Set G) ∧ y ∉ stab l := by
  obtain ⟨c⟩ := hC.nonempty_chart hβ
  by_contra hcon
  push Not at hcon
  have hle : Mbl β l ≤ stab β ⊓ stab l := fun y hy => ⟨hy.2, hcon y hy.2 hy.1⟩
  have h1 := c.bar_mono hle
  rw [c.Mbl_eq_preθ hC.sit hβ hl, c.bar_preθ] at h1
  have h2 := Subgroup.card_le_of_le h1
  have h3 : Nat.card (c.Dl l) = 8 := c.card_Dl hC.sit hl
  have h4 : Nat.card (c.bar (stab β ⊓ stab l)) = 8 := h3
  rw [h4, card_ptStab] at h2
  omega

theorem le_normalizer_or_eq (hC : Ctx H M S) {β l : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) {P : Subgroup G} (hinf : stab β ⊓ stab l ≤ P) (hP : P ≤ stab β) :
    P ≤ Subgroup.normalizer (Zv l : Set G) ∨ P = stab β := by
  obtain ⟨c⟩ := hC.nonempty_chart hβ
  rcases c.eq_or_le_Mbl hC.sit hβ hl hP hinf with h | h
  · exact Or.inr h
  · exact Or.inl (h.trans inf_le_left)

theorem inter_Rl_le (hC : Ctx H M S) {β l μ δ δ' : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) (hμ : μ ∈ nbrs β) (hne : μ ≠ l) (hZ : Zv μ = Zv l) (hlδ : l ∈ nbrs δ)
    (hδ : δ ≠ β) (hμδ : μ ∈ nbrs δ') (hδ' : δ' ≠ β) :
    Vn β ⊓ Vn δ ⊓ (Vn β ⊓ Vn δ') ≤ Zv l := by
  obtain ⟨c⟩ := hC.nonempty_chart hβ
  rw [← hC.Rl_eq hβ hl (mem_nbrs_symm.mp hlδ) hδ, ← hC.Rl_eq hβ hμ (mem_nbrs_symm.mp hμδ) hδ']
  have hpt : c.pt l = c.pt μ := ((c.Zv_eq_iff hC.sit hβ hμ hl).mp hZ).symm
  have hD : c.Dl l ≠ c.Dl μ := fun h => hne (c.Dl_injOn hC.sit hβ hμ hl h.symm)
  intro x hx
  have hxV : x ∈ Vn β := hC.Rl_le_Vn hβ hl hx.1
  have h1 : c.π ⟨x, hxV⟩ ∈ c.img (Rl β l) := (c.mem_img_iff (hC.Zv_le_Rl hβ hl) _).mpr hx.1
  have h2 : c.π ⟨x, hxV⟩ ∈ c.img (Rl β μ) := (c.mem_img_iff (hC.Zv_le_Rl hβ hμ) _).mpr hx.2
  rw [c.img_Rl hC hβ hl] at h1
  rw [c.img_Rl hC hβ hμ] at h2
  have h3 := inf_commW_le_vp (c.card_Dl hC.sit hl) (c.card_Dl hC.sit hμ) hpt hD ⟨h1, h2⟩
  rw [← c.img_Zv_nbr hC.sit hβ hl] at h3
  exact (c.mem_img_iff (Zv_le_Zv_of_nbr hC.sit hβ hl) _).mp h3

theorem chartFacts (hC : Ctx H M S) : S35.Fn.ChartFacts H M where
  inf_eq := fun _ hβ _ hx h => inf_eq_Qv hC hβ hx h
  ex_out := fun _ _ hβ hl => exists_normalizer_not_mem_stab hC hβ hl
  block := fun _ _ _ hβ hl hinf hP => le_normalizer_or_eq hC hβ hl hinf hP
  inter := fun _ _ _ _ _ hβ hl hμ hne hZ hlδ hδ hμδ hδ' =>
    inter_Rl_le hC hβ hl hμ hne hZ hlδ hδ hμδ hδ'

end S35.Ch

end F53.Stellmacher

end CFSG.Quasithin
