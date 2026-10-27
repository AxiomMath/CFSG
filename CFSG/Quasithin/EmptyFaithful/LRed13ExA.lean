module

public import CFSG.Quasithin.Background.B1Basic
public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin

namespace LRed13

open CFSG.Open
open scoped commutatorElement

section Abstract

variable {V : Type*} [CommGroup V] [Finite V]

theorem exists_quadratic_ffLe (hV : ∀ v : V, v ^ 2 = 1) {X A : Subgroup (MulAut V)}
    (hA : IsFFStarOffender X A) :
    ∃ P : Subgroup (MulAut V), IsFFStarOffender X P ∧ FFLe X P A ∧ IsQuadratic P := by
  classical
  let S : Set (Subgroup (MulAut V)) := {B | IsFFStarOffender X B ∧ FFLe X B A}
  have hAS : A ∈ S := ⟨hA, hA.isA2, hA.isA2, le_rfl, rfl⟩
  obtain ⟨P, hP, hmin⟩ := Set.exists_min_image S (fun B => Nat.card B) (Set.toFinite S) ⟨A, hAS⟩
  refine ⟨P, hP.1, hP.2, ?_⟩
  have hPmin : IsFFStarMin X P := by
    refine ⟨hP.1, fun B hB hBP => ?_⟩
    have hBA : FFLe X B A :=
      ⟨hBP.1, hA.isA2, hBP.2.2.1.trans hP.2.2.2.1, hBP.2.2.2.trans hP.2.2.2.2⟩
    exact Subgroup.eq_of_le_of_card_ge hBP.2.2.1 (hmin B ⟨hB, hBA⟩)
  exact B1_4_3 hV hPmin

end Abstract

section Internal

variable {G : Type*} [Group G] {U D : Subgroup G}

theorem commutator_commutator_eq_bot_of_isQuadratic (hU : IsElemAbelian 2 U)
    (hDN : D ≤ Subgroup.normalizer (U : Set G)) (hq : IsQuadratic (autI hU D)) :
    ⁅⁅U, D⁆, D⁆ = ⊥ := by
  rw [Subgroup.commutator_eq_bot_iff_le_centralizer, Subgroup.commutator_le]
  intro u hu d hd
  rw [Subgroup.mem_centralizer_iff]
  intro d' hd'
  have hdn : d ∈ Subgroup.normalizer (U : Set G) := hDN hd
  have hu' : u⁻¹ ∈ U := U.inv_mem hu
  set φ : MulAut (IntMod U hU) := convI hU ⟨d, hdn⟩ with hφ
  set v : IntMod U hU := IntMod.mk hU ⟨u⁻¹, hu'⟩ with hv
  have hφmem : φ ∈ autI hU D := convI_mem_autI hU hd hdn
  have hw : φ v * v⁻¹ ∈ commV (autI hU D) :=
    Subgroup.subset_closure ⟨φ, hφmem, v, rfl⟩
  have hwfix : φ v * v⁻¹ ∈ fixV (autI hU D) := hq hw
  have hψmem : convI hU ⟨d', hDN hd'⟩ ∈ autI hU D :=
    convI_mem_autI hU hd' (hDN hd')
  have h1 := hwfix _ hψmem
  have h2 := congrArg (fun x : IntMod U hU => x.val) h1
  simp only [convI_apply_val] at h2
  have hval : (φ v * v⁻¹).val = u * d * u⁻¹ * d⁻¹ := by
    have e1 : (φ v).val = d * u⁻¹ * d⁻¹ := by
      rw [hφ, convI_apply_val]
      rfl
    have e2 : (v⁻¹).val = u := by
      rw [IntMod.val_inv]
      exact inv_inv u
    rw [IntMod.val_mul, e1, e2]
    have hcomm : (φ v).val * u = u * (φ v).val := IntMod.val_comm (φ v) (IntMod.mk hU ⟨u, hu⟩)
    have e3 : (φ v).val * u = u * (d * u⁻¹ * d⁻¹) := by rw [e1] at hcomm; exact hcomm
    calc d * u⁻¹ * d⁻¹ * u = u * (d * u⁻¹ * d⁻¹) := e3
      _ = u * d * u⁻¹ * d⁻¹ := by group
  rw [hval] at h2
  have h3 : d' * (u * d * u⁻¹ * d⁻¹) * d'⁻¹ = u * d * u⁻¹ * d⁻¹ := h2
  show d' * ⁅u, d⁆ = ⁅u, d⁆ * d'
  rw [commutatorElement_def]
  calc d' * (u * d * u⁻¹ * d⁻¹) = (d' * (u * d * u⁻¹ * d⁻¹) * d'⁻¹) * d' := by group
    _ = (u * d * u⁻¹ * d⁻¹) * d' := by rw [h3]

end Internal

end LRed13

end CFSG.Quasithin
