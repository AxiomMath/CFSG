module

public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35L81Base
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56cG
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56Irr
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35C56cMD
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Std3
public import CFSG.Quasithin.EmptyFaithful.Stellmacher.S35Stmt2

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.QuasithinUnique CFSG.LieType.BorelTits CFSG.Quasithin.F7
open CFSG.Quasithin.F53Mod

namespace F53.Stellmacher

open CosetGeom F53
open scoped commutatorElement

namespace S35.L81

variable {G : Type} [Group G] [Finite G] {H M S : Subgroup G}

theorem relIndex_sup_le_four (hS : Sit H M S) {β l δ : Geo H M} (E : Subgroup G)
    (hβ : vtype β = false) (hl : l ∈ nbrs β) (hlδ : l ∈ nbrs δ) (hδ : δ ≠ β)
    (hnE : stab β ≤ Subgroup.normalizer (E : Set G)) (hVE : Vn β ≤ E) (hEW : E ≤ Wb β)
    (hO : IsOrthSec (stab β) E (Wb β)) : E.relIndex (E ⊔ Vn δ) ≤ 4 := by
  have hA := hS.glob.amalg
  have hq := S35.C56.quot_five hS hβ
  have hl' : β ∈ nbrs l := Std.mem_nbrs_symm.mp hl
  have hlδ' : δ ∈ nbrs l := Std.mem_nbrs_symm.mp hlδ
  have hvδ : vtype δ = false := (Std.vtype_eq_of_nbrs hlδ' hl').trans hβ
  have hWQ : Wb β ≤ pCoreOf 2 (stab β) := Std.Wb_le_Qv hS β
  have hQX : pCoreOf 2 (stab β) ≤ stab β := pCoreOf_le 2 _
  have hδW : Vn δ ≤ Wb β :=
    Std.Vn_le_Wb (Std.dist_eq_two_iff.mpr ⟨l, hl, hlδ', hδ⟩)
  have hQl : Qv l ≤ stab β := Std.Qv_le_stab hS hl'
  have hQlδ : Qv l ≤ stab δ := Std.Qv_le_stab hS hlδ'
  have hUF : E ⊔ Vn δ ≤ Wb β := sup_le hEW hδW
  have hFX : Wb β ≤ stab β := fun y hy => hQX (hWQ hy)
  have hBF_N : Vn δ ≤ Subgroup.normalizer (E : Set G) := fun y hy => hnE (hFX (hδW hy))
  have hc : ∀ a ∈ Qv l ⊓ Qv δ, ∀ u ∈ E ⊔ Vn δ, a * u * a⁻¹ * u⁻¹ ∈ E := by
    intro a ha u hu
    obtain ⟨e, he, y, hy, rfl⟩ := (F1.mem_sup_iff_exists_mul_of_normalizes hBF_N).mp hu
    have hcomm : a * y * a⁻¹ * y⁻¹ ∈ E := by
      have h1 : y * a * y⁻¹ * a⁻¹ ∈ ⁅Vn δ, Qv δ⁆ :=
        Subgroup.commutator_mem_commutator hy ha.2
      rw [Std.comm_Vn_Qv hS hvδ] at h1
      have h2 : a * y * a⁻¹ * y⁻¹ = (y * a * y⁻¹ * a⁻¹)⁻¹ := by group
      rw [h2]
      exact E.inv_mem (hVE (Std.Zv_le_Vn hl (Std.Zv_le_Zv_of_nbr hS hvδ hlδ h1)))
    have hae : a * e * a⁻¹ ∈ E :=
      (Subgroup.mem_normalizer_iff.mp (hnE (hQl ha.1)) e).mp he
    have e1 : a * (e * y) * a⁻¹ * (e * y)⁻¹ = (a * e * a⁻¹) * (a * y * a⁻¹ * y⁻¹) * e⁻¹ := by
      group
    rw [e1]
    exact E.mul_mem (E.mul_mem hae hcomm) (E.inv_mem he)
  have hAY : Qv l ≤ Subgroup.normalizer ((Qv l ⊓ Qv δ : Subgroup G) : Set G) :=
    le_normalizer_inf (fun x hx => le_normalizer_pCoreOf 2 (stab l) (pCoreOf_le 2 _ hx))
      (fun x hx => le_normalizer_pCoreOf 2 (stab δ) (hQlδ hx))
  have hsyl : IsSylowTwoOf (Qv l ⊔ pCoreOf 2 (stab β)) (stab β) := by
    have e : stab β ⊓ stab l = Qv l ⊔ pCoreOf 2 (stab β) := by
      rw [Std.stab_inf_eq hS hβ hl, sup_comm]
      rfl
    rw [← e]
    exact sylow_stab_inf_left hA hl
  exact S35.C56.relIndex_le_four hq hO hQl inf_le_left hAY hsyl
    (S35.C56.not_inf_Qv_le hS hβ hl hlδ hδ) le_sup_left hUF hc

theorem lem191II (hS : Sit H M S) (hII : CaseII H M) (h6 : Claim6b H M) :
    S35.II.Lem191 H M := by
  intro β hβ E hnE hVE hEW hEL hO
  obtain ⟨l, hl, δ, hδl, hδne⟩ := S35.C56.exists_arc hS hβ
  have hlδ : l ∈ nbrs δ := Std.mem_nbrs_symm.mp hδl
  have hδW : Vn δ ≤ Wb β :=
    Std.Vn_le_Wb (Std.dist_eq_two_iff.mpr ⟨l, hl, hδl, hδne⟩)
  have h6' := h6 β l δ E hβ hl hlδ hδne hnE hVE hEW hEL
  have h4 := relIndex_sup_le_four hS E hβ hl hlδ hδne hnE hVE hEW hO
  have hVN : Vn δ ≤ Subgroup.normalizer (E : Set G) :=
    fun y hy => hnE ((Std.Wb_le_Qv hS β).trans (pCoreOf_le 2 _) (hδW hy))
  have h5 := relIndex_inf_eq_relIndex_sup hVN
  rw [h6'] at h5
  have h8 := relIndex_ge_eight hS hII hβ hl hlδ hδne
  rw [h5, sup_comm] at h8
  omega

end S35.L81

end F53.Stellmacher

end CFSG.Quasithin
