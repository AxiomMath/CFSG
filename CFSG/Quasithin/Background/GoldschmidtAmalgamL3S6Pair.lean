module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3YBase

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem isPair_decomp {x ρ μ μ' : CosetGeom (A ⊔ B) A B} (hx : vtype x = true)
    (hρ : (graph (A ⊔ B) A B).Adj x ρ) (hμ : (graph (A ⊔ B) A B).Adj x μ)
    (hμ' : (graph (A ⊔ B) A B).Adj x μ') (hρμ : ρ ≠ μ) (hρμ' : ρ ≠ μ') (hμμ' : μ ≠ μ') {c : D}
    (hc : IsPair z V x ρ c) :
    ∃ a a' : D, a ∈ Vv V μ ∧ a ∉ Zv z x ∧ a' ∈ Vv V μ' ∧ a' ∉ Zv z x ∧ c = a * a' := by
  obtain ⟨ν, ν', a, a', hν, hν', hνρ, hν'ρ, hνν', ha, ha1, ha', ha'1, rfl⟩ := hc
  have hab := h.elemAbelian_Vv_B hx
  have hν0 := vtype_eq_false_of_adj hν hx
  have hν'0 := vtype_eq_false_of_adj hν' hx
  have hVν : Vv V ν ≤ Vv V x := Vv_le_Vv_of_adj hν.symm hν0
  have hVν' : Vv V ν' ≤ Vv V x := Vv_le_Vv_of_adj hν'.symm hν'0
  have hcases : ∀ w, (graph (A ⊔ B) A B).Adj x w → w ≠ ρ → w = μ ∨ w = μ' := by
    intro w hw hwρ
    rcases h.eq_or_eq_of_adj hρ hμ hμ' hw hρμ hρμ' hμμ' with e | e | e
    · exact absurd e hwρ
    · exact Or.inl e
    · exact Or.inr e
  rcases hcases ν hν hνρ with e | e <;> rcases hcases ν' hν' hν'ρ with e' | e'
  · exact absurd (e.trans e'.symm) hνν'
  · subst e e'
    exact ⟨a, a', ha, ha1, ha', ha'1, rfl⟩
  · subst e e'
    exact ⟨a', a, ha', ha'1, ha, ha1, isElemAbelian_comm hab (hVν ha) (hVν' ha')⟩
  · exact absurd (e.trans e'.symm) hνν'

theorem exists_isPair {x ρ : CosetGeom (A ⊔ B) A B} (hx : vtype x = true)
    (hρ : (graph (A ⊔ B) A B).Adj x ρ) : ∃ c : D, IsPair z V x ρ c := by
  obtain ⟨μ, μ', hμ, hμ', hρμ, hρμ', hμμ'⟩ := h.exists_two_others hρ
  have hμ0 := vtype_eq_false_of_adj hμ hx
  have hμ'0 := vtype_eq_false_of_adj hμ' hx
  obtain ⟨a, ha, ha1⟩ := h.exists_Vv_not_mem_Zv hμ0 hμ.symm
  obtain ⟨a', ha', ha'1⟩ := h.exists_Vv_not_mem_Zv hμ'0 hμ'.symm
  exact ⟨a * a', μ, μ', a, a', hμ, hμ', hρμ.symm, hρμ'.symm, hμμ', ha, ha1, ha', ha'1, rfl⟩

theorem isPair_not_both {β s₁ s₃ x : CosetGeom (A ⊔ B) A B} (hβ : vtype β = true)
    (h1 : (graph (A ⊔ B) A B).Adj β s₁) (h3 : (graph (A ⊔ B) A B).Adj β s₃)
    (hx : (graph (A ⊔ B) A B).Adj β x) (n13 : s₁ ≠ s₃) (n1x : s₁ ≠ x) (n3x : s₃ ≠ x) {m : D}
    (hm : IsPair z V β x m) (hm' : IsPair z V β s₁ m) : False := by
  obtain ⟨a, a', ha, ha1, ha', ha'1, rfl⟩ :=
    h.isPair_decomp hβ hx h1 h3 n1x.symm n3x.symm n13 hm
  obtain ⟨e, e', he, he1, he', he'1, hee⟩ := h.isPair_decomp hβ h1 h3 hx n13 n1x n3x hm'
  have hs1 := vtype_eq_false_of_adj h1 hβ
  have hs3 := vtype_eq_false_of_adj h3 hβ
  have hxx := vtype_eq_false_of_adj hx hβ
  have hab := h.elemAbelian_Vv_B hβ
  have haV : a ∈ Vv V β := Vv_le_Vv_of_adj h1.symm hs1 ha
  have ha'V : a' ∈ Vv V β := Vv_le_Vv_of_adj h3.symm hs3 ha'
  have heV : e ∈ Vv V β := Vv_le_Vv_of_adj h3.symm hs3 he
  have hζ : a' * e⁻¹ ∈ Zv z β := h.mul_inv_mem_Zv_of_Vv hs3 h3.symm he he1 ha' ha'1
  have hc1 : e⁻¹ * a = a * e⁻¹ := isElemAbelian_comm hab ((Vv V β).inv_mem heV) haV
  have hc2 : e⁻¹ * a' = a' * e⁻¹ := isElemAbelian_comm hab ((Vv V β).inv_mem heV) ha'V
  have hform : e' = a * (a' * e⁻¹) :=
    calc e' = e⁻¹ * (e * e') := by group
      _ = e⁻¹ * (a * a') := by rw [← hee]
      _ = (e⁻¹ * a) * a' := by group
      _ = (a * e⁻¹) * a' := by rw [hc1]
      _ = a * (e⁻¹ * a') := by group
      _ = a * (a' * e⁻¹) := by rw [hc2]
  have he'1V : e' ∈ Vv V s₁ := by
    rw [hform]
    exact (Vv V s₁).mul_mem ha (h.Zv_le_Vv h1.symm hs1 hζ)
  exact he'1 (h.mem_Zv_of_mem_Vv_of_mem_Vv hβ hx h1 n1x.symm he' he'1V)

theorem not_stab_inf_le_ballStab_one_right {u v : CosetGeom (A ⊔ B) A B}
    (huv : (graph (A ⊔ B) A B).Adj u v) (hu : vtype u = false) :
    ¬ stab u ⊓ stab v ≤ ballStab 1 v := by
  obtain ⟨g, rfl, rfl⟩ := exists_smul_edge_AB huv hu
  rw [stab_smul, stab_smul, ballStab_smul, ballStab_one_γ₁_eq_pCoreOf h.gold,
    stab_γ₀ (le_sup_left : A ≤ A ⊔ B), stab_γ₁ (le_sup_right : B ≤ A ⊔ B), ← conjSub_inf]
  intro hle
  have h1 : A ⊓ B ≤ pCoreOf 2 B := by
    have := (conjSub_le_iff (g : D)).mp hle
    rwa [conjSub_conjSub_inv] at this
  have h2 : (pCoreOf 2 B).relIndex (A ⊓ B) = 1 := Subgroup.relIndex_eq_one.mpr h1
  rw [h.gold.relIndex_pCoreOf_T_right] at h2
  omega

theorem exists_swap_B {β u x x' : CosetGeom (A ⊔ B) A B}
    (hu : (graph (A ⊔ B) A B).Adj β u) (hu0 : vtype u = false)
    (hx : (graph (A ⊔ B) A B).Adj β x) (hx' : (graph (A ⊔ B) A B).Adj β x') (hux : u ≠ x)
    (hux' : u ≠ x') (hxx' : x ≠ x') :
    ∃ k : ↥(A ⊔ B), (k : D) ∈ stab β ∧ (k : D) ∈ stab u ∧ k • x = x' := by
  obtain ⟨k, hk, hkx⟩ := h.exists_smul_of_not_le hu hx hx' hux hux' hxx'
    (H := stab u ⊓ stab β) inf_le_right inf_le_left
    (h.not_stab_inf_le_ballStab_one_right hu.symm hu0)
  exact ⟨k, hk.2, hk.1, hkx⟩

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
