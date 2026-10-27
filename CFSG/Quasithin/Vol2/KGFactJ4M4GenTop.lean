module

public import CFSG.Quasithin.Vol2.KGFactJ4M4GenSpec

public section

namespace CFSG.Quasithin.KGC31.J4M4.Gen

open CFSG.Sporadic.J4 CFSG.Sporadic.J4.QT CFSG.Quasithin.KGC31.J4

theorem eq_top_of_conj_closure {Γ : Type*} [Group Γ] [Finite Γ] {J : Subgroup Γ} {s : Set Γ}
    (hJ : J = Subgroup.closure s) {K : Subgroup J} (g : Γ)
    (h : ∀ x ∈ s, ∃ k ∈ K, (k : Γ) = g * x * g⁻¹) : K = ⊤ := by
  have hJ' : J.map (MulAut.conj g).toMonoidHom = Subgroup.closure ((MulAut.conj g) '' s) := by
    rw [hJ, MonoidHom.map_closure]
    rfl
  have hL : J.map (MulAut.conj g).toMonoidHom ≤ K.map J.subtype := by
    rw [hJ', Subgroup.closure_le]
    rintro _ ⟨x, hx, rfl⟩
    obtain ⟨k, hk, hkx⟩ := h x hx
    exact ⟨k, hk, by rw [MulAut.conj_apply]; exact hkx⟩
  have hKJ : K.map J.subtype ≤ J := by
    rintro _ ⟨k, -, rfl⟩
    exact k.2
  have hcard : Nat.card ↥J ≤ Nat.card ↥(J.map (MulAut.conj g).toMonoidHom) :=
    (Subgroup.card_map_of_injective (MulAut.conj g).injective).ge
  have hEq : J.map (MulAut.conj g).toMonoidHom = J :=
    Subgroup.eq_of_le_of_card_ge (hL.trans hKJ) hcard
  rw [eq_top_iff]
  intro x _
  obtain ⟨k, hk, hkx⟩ : (x : Γ) ∈ K.map J.subtype := hL (hEq.ge x.2)
  have : k = x := Subtype.ext hkx
  exact this ▸ hk

theorem closure_w1_w2_c_eq_top :
    Subgroup.closure ({CFSG.Quasithin.KGJ4.w1, CFSG.Quasithin.KGJ4.w2, cElt} : Set G₀) = ⊤ := by
  obtain ⟨-, -, -, -, gM, hga, hgb⟩ := chkGen_facts
  set K := Subgroup.closure ({CFSG.Quasithin.KGJ4.w1, CFSG.Quasithin.KGJ4.w2, cElt} : Set G₀)
  have hw₁ : CFSG.Quasithin.KGJ4.w1 ∈ K := Subgroup.subset_closure (by simp)
  have hw₂ : CFSG.Quasithin.KGJ4.w2 ∈ K := Subgroup.subset_closure (by simp)
  have hc : cElt ∈ K := Subgroup.subset_closure (by simp)
  obtain ⟨ha, hb⟩ := apElt_bpElt_mem K hw₁ hw₂ hc
  refine eq_top_of_conj_closure (J := J) (s := {gA, gB}) rfl gM ?_
  rintro x (rfl | rfl)
  · refine ⟨apElt, ha, ?_⟩
    rw [← hga, mul_inv_cancel_right]
  · refine ⟨bpElt, hb, ?_⟩
    rw [← hgb, mul_inv_cancel_right]

end CFSG.Quasithin.KGC31.J4M4.Gen

end
