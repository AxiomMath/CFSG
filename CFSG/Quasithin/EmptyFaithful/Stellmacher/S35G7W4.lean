module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35G7W3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Fin5

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.F7 CFSG.Quasithin.F53Mod
open CFSG.LieType.BorelTits Equiv
open CFSG.Quasithin.F53.Stellmacher.S35.Fin
open scoped commutatorElement

namespace F53.Stellmacher.S35.G7

open CosetGeom F53

variable {G : Type} [Group G] [Finite G]

namespace WM

variable {H M S : Subgroup G} {β : Geo H M} {c : Ch.Chart β} {E K : Subgroup G}
  (b : WBase (stab β) E K (Wb β) c.θ) (hS : Sit H M S)

include hS in
theorem Wl_eq_sup {l₀ : Geo H M} (hβ : vtype β = false) (hl₀ : l₀ ∈ nbrs β) :
    ∃ δ δ' : Geo H M, δ ∈ nbrs l₀ ∧ δ' ∈ nbrs l₀ ∧ δ ≠ β ∧ δ' ≠ β ∧
      Wl l₀ = Vn β ⊔ Vn δ ⊔ Vn δ' := by
  have hlt : vtype l₀ = true := Std.vtype_nbr_S5 hβ hl₀
  have hβl : β ∈ nbrs l₀ := Std.mem_nbrs_symm.mp hl₀
  obtain ⟨δ, -, hδ, -, hδβ, -, -⟩ := Std.exists_two_others hS hlt hβl
  obtain ⟨δ'', hδ'', h1, h2, hall⟩ := Std.nbrs_S3_third hS hlt hβl hδ hδβ.symm
  refine ⟨δ, δ'', hδ, hδ'', hδβ, h1, le_antisymm (Std.Wl_le fun ρ hρ => ?_)
    (sup_le (sup_le (Std.Vn_le_Wl hβl) (Std.Vn_le_Wl hδ)) (Std.Vn_le_Wl hδ''))⟩
  rcases hall ρ hρ with rfl | rfl | rfl
  · exact le_sup_left.trans le_sup_left
  · exact le_sup_right.trans le_sup_left
  · exact le_sup_right

include hS in
theorem image_Wl (hI : CaseI H M) (h6b : Claim6b H M) (hβ : vtype β = false) {l₀ : Geo H M}
    (hl₀ : l₀ ∈ nbrs β)
    (hS5 : ((stab β ⊓ stab l₀).subgroupOf (stab β)).map c.θ = S5Syl)
    (hnE : stab β ≤ Subgroup.normalizer (E : Set G)) (hVE : Vn β ≤ E) (hEW : E ≤ Wb β)
    (hEL : ⁅E, Lr β⁆ ≤ Vn β) :
    ((Wl l₀).subgroupOf (Wb β)).map (fm b) = commW orth (Subgroup.zpowers zStd) ⊤ := by
  obtain ⟨δ, δ', hδ, hδ', hδβ, hδ'β, hW⟩ := Wl_eq_sup hS hβ hl₀
  have hP : ∀ ε ∈ nbrs l₀, ε ≠ β →
      ((Vn ε).subgroupOf (Wb β)).map (fm b) = commW orth (Subgroup.zpowers zStd) ⊤ :=
    fun ε hε hεβ => eq_commW_z_of_card_four card_S5Syl ((isCentInv_std_iff zStd).mpr rfl)
      (isInvSub_image_Vn b hS hβ hl₀ hS5 hε)
      (card_image_Vn b hS hI h6b hβ hl₀ hε hεβ hnE hVE hEW hEL)
  have hVβ : Vn β ≤ Wb β := Std.Vn_le_Wb_self hS hβ
  have hbot : ((Vn β).subgroupOf (Wb β)).map (fm b) = ⊥ := by
    rw [eq_bot_iff]
    rintro _ ⟨x, hx, rfl⟩
    exact (fm_eq_one_iff b x).mpr (hVE (Subgroup.mem_subgroupOf.mp hx))
  have hVδ := Vn_le_Wb_of_nbr hS hβ hl₀ hδ
  have hVδ' := Vn_le_Wb_of_nbr hS hβ hl₀ hδ'
  rw [hW, Subgroup.subgroupOf_sup (sup_le hVβ hVδ) hVδ', Subgroup.subgroupOf_sup hVβ hVδ,
    Subgroup.map_sup, Subgroup.map_sup, hbot, hP δ hδ hδβ, hP δ' hδ' hδ'β, bot_sup_eq, sup_idem]

omit [Finite G] in
theorem conj_mem_Wl {g : ↥(H ⊔ M)} {l₀ : Geo H M} {x : G} (hx : x ∈ Wl (g • l₀)) :
    (g : G)⁻¹ * x * (g : G) ∈ Wl l₀ := by
  have h : Wl (g • l₀) ≤ conjSub (g : G) (Wl l₀) := Std.Wl_le fun ρ hρ => by
    obtain ⟨ρ₀, rfl⟩ : ∃ ρ₀, ρ = g • ρ₀ := ⟨g⁻¹ • ρ, by simp⟩
    have hρ₀ : ρ₀ ∈ nbrs l₀ := (Std.smul_mem_nbrs_iff' g).mp hρ
    rw [Vn_smul]
    exact conjSub_mono _ (Std.Vn_le_Wl hρ₀)
  exact mem_conjSub.mp (h hx)

end WM

end F53.Stellmacher.S35.G7

end CFSG.Quasithin
