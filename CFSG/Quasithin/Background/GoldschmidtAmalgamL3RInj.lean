module

public import CFSG.Quasithin.Background.GoldschmidtAmalgamL3RVertex

public section

namespace CFSG.Quasithin

open CFSG.Open CFSG.LieType.BorelTits CFSG.QuasithinUnique CFSG.Quasithin.F7
  CFSG.Quasithin.CosetGeom CFSG.Quasithin.F6.GoldAmL

namespace F6

namespace GoldAmL3

variable {D : Type*} [Group D] [Finite D] {A B : Subgroup D} {z : D} {V : Subgroup D}

theorem eq_of_card_two_of_mem {X Y : Subgroup D} (hX : Nat.card X = 2) (hY : Nat.card Y = 2)
    {c : D} (hcX : c ∈ X) (hcY : c ∈ Y) (hc : c ≠ 1) : X = Y := by
  have hpos : 0 < orderOf c := orderOf_pos c
  have h1 : orderOf c ≠ 1 := fun e => hc (orderOf_eq_one_iff.mp e)
  have hz : Nat.card (Subgroup.zpowers c) = orderOf c := Nat.card_zpowers c
  have hXz : Subgroup.zpowers c = X :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcX) (by omega)
  have hYz : Subgroup.zpowers c = Y :=
    Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hcY) (by omega)
  rw [← hXz, ← hYz]

omit [Finite D] in
theorem exists_ne_one_of_card_two {X : Subgroup D} (hX : Nat.card X = 2) : ∃ c ∈ X, c ≠ 1 := by
  have hne : X ≠ ⊥ := fun e => by
    rw [e, Subgroup.card_bot] at hX
    omega
  obtain ⟨a, ha⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hne
  exact ⟨(a : D), a.2, fun e => ha (Subtype.ext e)⟩

namespace GoldHyp3

variable (h : GoldHyp3 A B z V)

include h

theorem Zv_eq_of_mem {v v' : CosetGeom (A ⊔ B) A B} (hv : vtype v = true) (hv' : vtype v' = true)
    {c : D} (hc : c ∈ Zv z v) (hc' : c ∈ Zv z v') (hc1 : c ≠ 1) : Zv z v = Zv z v' :=
  eq_of_card_two_of_mem (h.card_Zv hv) (h.card_Zv hv') hc hc' hc1

omit [Finite D] in
theorem exists_ne_one_mem_Zv {v : CosetGeom (A ⊔ B) A B} (hv : vtype v = true) :
    ∃ c ∈ Zv z v, c ≠ 1 :=
  exists_ne_one_of_card_two (h.card_Zv hv)

theorem Zv_ne_two {x₀ x₁ x₂ : CosetGeom (A ⊔ B) A B} (h₀₁ : (graph (A ⊔ B) A B).Adj x₀ x₁)
    (h₁₂ : (graph (A ⊔ B) A B).Adj x₁ x₂) (hx₁ : vtype x₁ = false) (n₀₂ : x₀ ≠ x₂) :
    Zv z x₀ ≠ Zv z x₂ := fun hzz => n₀₂ (h.eq_of_Zv_eq hx₁ h₀₁.symm h₁₂ hzz)

theorem Zv_ne_four {x₀ x₁ x₂ x₃ x₄ : CosetGeom (A ⊔ B) A B}
    (h₀₁ : (graph (A ⊔ B) A B).Adj x₀ x₁) (h₁₂ : (graph (A ⊔ B) A B).Adj x₁ x₂)
    (h₂₃ : (graph (A ⊔ B) A B).Adj x₂ x₃) (h₃₄ : (graph (A ⊔ B) A B).Adj x₃ x₄)
    (hx₁ : vtype x₁ = false) (n₀₂ : x₀ ≠ x₂) (n₁₃ : x₁ ≠ x₃) : Zv z x₀ ≠ Zv z x₄ := by
  intro hzz
  have hx₀ : vtype x₀ = true := vtype_eq_true_of_adj h₀₁.symm hx₁
  have hx₂ : vtype x₂ = true := vtype_eq_true_of_adj h₁₂ hx₁
  have hx₃ : vtype x₃ = false := vtype_eq_false_of_adj h₂₃ hx₂
  obtain ⟨c, hc, hc1⟩ := h.exists_ne_one_mem_Zv hx₀
  have hc₁ : c ∈ Vv V x₁ := h.Zv_le_Vv h₀₁.symm hx₁ hc
  have hc₃ : c ∈ Vv V x₃ := h.Zv_le_Vv h₃₄ hx₃ (hzz ▸ hc)
  have hc₂ : c ∈ Zv z x₂ := h.mem_Zv_of_mem_Vv_of_mem_Vv hx₂ h₁₂.symm h₂₃ n₁₃ hc₁ hc₃
  exact h.Zv_ne_two h₀₁ h₁₂ hx₁ n₀₂ (h.Zv_eq_of_mem hx₀ hx₂ hc hc₂ hc1)

theorem Zv_ne_six (hU : Nat.card (conjClosure V B) = 8)
    {x₀ x₁ x₂ x₃ x₄ x₅ x₆ : CosetGeom (A ⊔ B) A B}
    (h₀₁ : (graph (A ⊔ B) A B).Adj x₀ x₁) (h₁₂ : (graph (A ⊔ B) A B).Adj x₁ x₂)
    (h₂₃ : (graph (A ⊔ B) A B).Adj x₂ x₃) (h₃₄ : (graph (A ⊔ B) A B).Adj x₃ x₄)
    (h₄₅ : (graph (A ⊔ B) A B).Adj x₄ x₅) (h₅₆ : (graph (A ⊔ B) A B).Adj x₅ x₆)
    (hx₁ : vtype x₁ = false) (n₀₂ : x₀ ≠ x₂) (n₁₃ : x₁ ≠ x₃) (n₂₄ : x₂ ≠ x₄) :
    Zv z x₀ ≠ Zv z x₆ := by
  intro hzz
  have hx₀ : vtype x₀ = true := vtype_eq_true_of_adj h₀₁.symm hx₁
  have hx₂ : vtype x₂ = true := vtype_eq_true_of_adj h₁₂ hx₁
  have hx₃ : vtype x₃ = false := vtype_eq_false_of_adj h₂₃ hx₂
  have hx₄ : vtype x₄ = true := vtype_eq_true_of_adj h₃₄ hx₃
  have hx₅ : vtype x₅ = false := vtype_eq_false_of_adj h₄₅ hx₄
  obtain ⟨c, hc, hc1⟩ := h.exists_ne_one_mem_Zv hx₀
  have hc₂ : c ∈ Vv V x₂ := Vv_le_Vv_of_adj h₁₂ hx₁ (h.Zv_le_Vv h₀₁.symm hx₁ hc)
  have hc₄ : c ∈ Vv V x₄ := Vv_le_Vv_of_adj h₄₅.symm hx₅ (h.Zv_le_Vv h₅₆ hx₅ (hzz ▸ hc))
  have hc₃ : c ∉ Vv V x₃ := fun hc₃ => by
    obtain ⟨δ, hδ, hcδ⟩ := h.exists_adj_mem_Zv hx₃ hc₃ hc1
    have hδt : vtype δ = true := vtype_eq_true_of_adj hδ hx₃
    exact h.Zv_ne_four h₀₁ h₁₂ h₂₃ hδ hx₁ n₀₂ n₁₃ (h.Zv_eq_of_mem hx₀ hδt hc hcδ hc1)
  have key : ∀ y : CosetGeom (A ⊔ B) A B, vtype y = true → Vv V x₃ ≤ Vv V y → c ∈ Vv V y →
      Vv V y = Vv V x₃ ⊔ Subgroup.zpowers c := by
    intro y hy hle hcy
    obtain ⟨M, hMdef⟩ : ∃ M : Subgroup D, M = Vv V x₃ ⊔ Subgroup.zpowers c := ⟨_, rfl⟩
    have hM₁ : Vv V x₃ ≤ M := hMdef ▸ le_sup_left
    have hcM : c ∈ M := hMdef ▸ Subgroup.mem_sup_right (Subgroup.mem_zpowers c)
    have hM : M ≤ Vv V y := hMdef ▸ sup_le hle (Subgroup.zpowers_le.mpr hcy)
    have h4 : Nat.card (Vv V x₃) = 4 := h.card_Vv_A hx₃
    have h8 : Nat.card (Vv V y) = 8 := h.card_Vv_B hU hy
    have hd1 : 4 ∣ Nat.card M := by
      have := Subgroup.card_dvd_of_le hM₁
      rwa [h4] at this
    have hle8 : Nat.card M ≤ 8 := by
      have := Subgroup.card_le_of_le hM
      rwa [h8] at this
    have hpos : 0 < Nat.card M := Nat.card_pos
    have hne : Nat.card M ≠ 4 := fun e => by
      have heq : Vv V x₃ = M := Subgroup.eq_of_le_of_card_ge hM₁ (by omega)
      exact hc₃ (heq ▸ hcM)
    rw [← hMdef]
    exact (Subgroup.eq_of_le_of_card_ge hM (by omega)).symm
  have hVeq : Vv V x₂ = Vv V x₄ :=
    (key x₂ hx₂ (Vv_le_Vv_of_adj h₂₃.symm hx₃) hc₂).trans
      (key x₄ hx₄ (Vv_le_Vv_of_adj h₃₄ hx₃) hc₄).symm
  have hnorm : stab x₃ ≤ Subgroup.normalizer (Vv V x₂ : Set D) := by
    rw [← h.sup_stab_inf_eq hx₃ h₂₃.symm h₃₄ n₂₄]
    refine sup_le (inf_le_right.trans (stab_le_normalizer_Vv h.natural.reduced.2.1 x₂)) ?_
    have := stab_le_normalizer_Vv (V := V) h.natural.reduced.2.1 x₄
    rw [← hVeq] at this
    exact inf_le_right.trans this
  exact h.not_stab_le_normalizer_Vv h₂₃.symm hx₃ hnorm

end GoldHyp3

end GoldAmL3

end F6

end CFSG.Quasithin
