module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7RChar
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7RJ
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7Sys
public import CFSG.Quasithin.Background.PushS3Main
public import CFSG.Quasithin.Background.GoldschmidtAmalgamLab7RKlein

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.QuasithinUnique.Setup
  CFSG.Quasithin.F7 CFSG.Quasithin.F6.GoldAmL CFSG.Quasithin.F6.GoldAmLab6
open scoped commutatorElement

namespace F6

namespace GoldAmLab7

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {V V₂ : Subgroup D} {z c : D}

theorem comm_mem_of_campbell (h : TwoSys A B z V c V₂)
    (hN : B ≤ Subgroup.normalizer ((pCoreOf 2 A ⊓ pCoreOf 2 B : Subgroup D) : Set D))
    {y : D} (hyB : y ∈ B) (hy3 : orderOf y = 3) :
    ∀ r ∈ pCoreOf 2 A ⊓ pCoreOf 2 B, y * r * y⁻¹ * r⁻¹ ∈ V₂ := by
  have hne : pCoreOf 2 A ≠ pCoreOf 2 B := fun e =>
    not_pCoreOf_le h.gold (by have := h.card_ge; omega) e.le
  set R : Subgroup D := pCoreOf 2 A ⊓ pCoreOf 2 B with hR
  set H : Subgroup D := (R ⊔ Subgroup.zpowers y) ⊔ pCoreOf 2 A with hH
  have hR2 : IsPGroup 2 R := (pCoreOf_isPGroup 2 A : IsPGroup 2 (pCoreOf 2 A)).to_le inf_le_left
  have hHB : H ≤ B := sup_zpowers_sup_le h.gold hyB
  have hV₂R : V₂ ≤ R := le_inf h.V₂_le fun x hx => (h.nat₂.le_center hx).1
  have hV₂H : V₂ ≤ H := hV₂R.trans (le_sup_left.trans le_sup_left)
  have hNH : H ≤ Subgroup.normalizer (V₂ : Set D) := hHB.trans h.nat₂.reduced.2.1
  have hyH : y ∈ H := Subgroup.mem_sup_left (Subgroup.mem_sup_right (Subgroup.mem_zpowers y))
  obtain ⟨a, haS, n₀, hn₀V, hn₀⟩ := exists_moved_of_natural h.gold hne h.nat₂
  have hfree := fixed_point_free_of_natural h.gold.vertex_right h.nat₂ hyB hy3
  have hcamp := F6.PushS3.two_subgroup_card_le_four_of_campbell H (pCoreOf 2 A) V₂ y a
    le_sup_right (pCoreOf_isPGroup 2 A) (relIndex_pCoreOf_sup h.gold hne hN hyB hy3)
    (not_le_normalizer_sup h.gold hne hyB hy3) hV₂H (isKleinFour_of_natural h.nat₂) hNH hyH hy3
    hfree haS ⟨n₀, hn₀V, hn₀⟩ (charTwo_rH h.gold hne hN hyB hy3)
    (fun C hCS hC0 hch => noCharNormal_rH h.gold hyB hy3 C hCS hC0 hch)
    (not_thompsonJ_le_centralizer h.gold hN h.nat₂ h.V₂_le)
  have hyR : ∀ r ∈ R, y * r * y⁻¹ ∈ R := fun r hr =>
    (Subgroup.mem_normalizer_iff.mp (hN hyB) r).mp hr
  set X : Subgroup D := Subgroup.closure {g | ∃ r ∈ R, g = ⁅r, y⁆} with hX
  have hXR : X ≤ R := by
    refine (Subgroup.closure_le R).mpr ?_
    rintro _ ⟨r, hr, rfl⟩
    have e : ⁅r, y⁆ = r * (y * r⁻¹ * y⁻¹) := by rw [commutatorElement_def]; group
    rw [e]
    exact R.mul_mem hr (hyR r⁻¹ (R.inv_mem hr))
  have hXodd : X ≤ oddOrderSubgroup H := by
    refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨r, hr, rfl⟩
    have hrH : r ∈ H := Subgroup.mem_sup_left (Subgroup.mem_sup_left hr)
    have o1 : r * y * r⁻¹ ∈ oddOrderSubgroup H := by
      refine Subgroup.subset_closure ⟨H.mul_mem (H.mul_mem hrH hyH) (H.inv_mem hrH), ?_⟩
      have := orderOf_injective (MulAut.conj r).toMonoidHom (MulAut.conj r).injective y
      simp only [MulEquiv.coe_toMonoidHom, MulAut.conj_apply] at this
      rw [this, hy3]
      decide
    have o2 : y⁻¹ ∈ oddOrderSubgroup H := by
      refine Subgroup.subset_closure ⟨H.inv_mem hyH, ?_⟩
      rw [orderOf_inv, hy3]
      decide
    have e : ⁅r, y⁆ = (r * y * r⁻¹) * y⁻¹ := by rw [commutatorElement_def]
    rw [e]
    exact (oddOrderSubgroup H).mul_mem o1 o2
  have hcard : Nat.card X ≤ 4 := hcamp X hXodd (hR2.to_le hXR)
  have hab : ∀ a ∈ V₂, ∀ b ∈ V₂, a * b = b * a := fun a ha b hb =>
    isElemAbelian_comm h.nat₂.reduced.2.2.1 ha hb
  have hyV : ∀ x ∈ V₂, y * x * y⁻¹ ∈ V₂ := fun x hx =>
    (Subgroup.mem_normalizer_iff.mp (h.nat₂.reduced.2.1 hyB) x).mp hx
  have hNX : V₂ ≤ X := fun n hn => by
    obtain ⟨m, hm, rfl⟩ := exists_comm_eq_of_fixed_free hab hyV hfree n hn
    exact Subgroup.subset_closure ⟨m, hV₂R hm, rfl⟩
  have hXN : V₂ = X := Subgroup.eq_of_le_of_card_ge hNX (by rw [h.nat₂.card_eq]; exact hcard)
  intro r hr
  have hmem : ⁅r, y⁆ ∈ V₂ := by
    rw [hXN]
    exact Subgroup.subset_closure ⟨r, hr, rfl⟩
  have e : y * r * y⁻¹ * r⁻¹ = ⁅r, y⁆⁻¹ := by rw [commutatorElement_def]; group
  rw [e]
  exact V₂.inv_mem hmem

end GoldAmLab7

end F6

end CFSG.Quasithin
