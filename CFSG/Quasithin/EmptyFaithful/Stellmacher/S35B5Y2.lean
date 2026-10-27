module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35B5Y1

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod
open scoped commutatorElement

namespace F53.Stellmacher

open CosetGeom F53 Equiv

namespace S35.B5

open S35.Std

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem relIndex_Vn_arc (hC : Ch.Ctx H M S) {β l δ : Geo H M} (hβ : vtype β = false)
    (hl : l ∈ nbrs β) (hlδ : δ ∈ nbrs l) (hδ : δ ≠ β) :
    (Vn β).relIndex (Vn δ) = 4 := by
  have hvδ : vtype δ = false := vtype_nbr_S3 (vtype_nbr_S5 hβ hl) hlδ
  have h1 := (hC.caseI β l δ hβ hl (mem_nbrs_symm.mp hlδ) hδ).1
  have h2 := (hC.caseI δ l β hvδ (mem_nbrs_symm.mp hlδ) hl (Ne.symm hδ)).2
  have h3 := Subgroup.relIndex_mul_card (Vn β) (Vn δ)
  rw [h1, h2] at h3
  omega

theorem Vn_le_stab_of_dist_two (hS : Sit H M S) {β γ : Geo H M} (h : dist γ β = 2) :
    Vn γ ≤ stab β :=
  Vn_le_stab_dist hS (by have := hS.b5; omega)

theorem relIndex_sup_Vn (hS : Sit H M S) {β γ : Geo H M} (h : dist γ β = 2) :
    (Vn β).relIndex (Vn γ ⊔ Vn β) = (Vn β).relIndex (Vn γ) := by
  have hn : Vn γ ≤ Subgroup.normalizer (Vn β : Set G) :=
    (Vn_le_stab_of_dist_two hS h).trans (Vn_normal β)
  rw [← relIndex_inf_eq_relIndex_sup hn, Subgroup.inf_relIndex_left]

omit [Finite G] in
theorem Yg_eq (β δ γ : Geo H M) : Yg β δ γ = Vn δ ⊔ (Vn γ ⊔ Vn β) := by
  unfold Yg; rw [sup_assoc]

theorem Y_card (hC : Ch.Ctx H M S) {β l δ l0 γ : Geo H M} (hcfg : Cfg H M β l δ l0 γ)
    (_hcomm : ⁅Vn δ, Vn γ⁆ = ⊥) :
    Vn δ ⊔ Vn γ ≤ Wb β ∧ (Vn β).relIndex (Yg β δ γ) ≤ 16 := by
  have hS := hC.sit
  refine ⟨sup_le hcfg.Vδ_le_Wb hcfg.Vγ_le_Wb, ?_⟩
  have hδ4 := relIndex_Vn_arc hC hcfg.vβ hcfg.l_nbr hcfg.δ_nbr hcfg.δ_ne
  have hγ4 := relIndex_Vn_arc hC hcfg.vβ hcfg.l0_nbr hcfg.γ_nbr hcfg.γ_ne
  have hVδn : Vn δ ≤ Subgroup.normalizer ((Vn γ ⊔ Vn β : Subgroup G) : Set G) := fun x hx =>
    mem_normalizer_sup (Vn_normal γ (hcfg.Vδ_le_stab_γ hS hx))
      (Vn_normal β (Vn_le_stab_of_dist_two hS hcfg.dist_δβ hx))
  have hP : (Vn β).relIndex (Vn γ ⊔ Vn β) = 4 := by
    rw [relIndex_sup_Vn hS hcfg.dist_γβ, hγ4]
  have hY : (Vn γ ⊔ Vn β).relIndex (Vn δ ⊔ (Vn γ ⊔ Vn β)) ≤ 4 := by
    have h := relIndex_inf_eq_relIndex_sup hVδn
    have hle : Vn δ ⊓ Vn β ≤ Vn δ ⊓ (Vn γ ⊔ Vn β) :=
      inf_le_inf_left _ le_sup_right
    have hne : (Vn δ ⊓ Vn β).relIndex (Vn δ) ≠ 0 := by
      rw [Subgroup.inf_relIndex_left, hδ4]; norm_num
    have := Subgroup.relIndex_le_of_le_left (L := Vn δ) hle hne
    rw [h, Subgroup.inf_relIndex_left, hδ4] at this
    exact this
  rw [Yg_eq, ← Subgroup.relIndex_mul_relIndex (Vn β) (Vn γ ⊔ Vn β)
    (Vn δ ⊔ (Vn γ ⊔ Vn β)) le_sup_right le_sup_right, hP]
  omega

end S35.B5

end F53.Stellmacher

end CFSG.Quasithin
