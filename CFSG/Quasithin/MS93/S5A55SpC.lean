module

public import CFSG.Quasithin.MS93.S5A56Sp

public section

namespace CFSG.Quasithin.MS93.S5

open Matrix MSP

variable {F : Type} [Field F]

abbrev gv (ν : F) : V4 F := ν • e₁ F + e₂ F

theorem gv_ne_zero (ν : F) : gv ν ≠ 0 := fun h => by
  have := congrFun h (.inl 1)
  simp at this

theorem gv_mem_ln₀ (ν : F) : gv ν ∈ ln₀ F := mem_ln₀.2 ⟨by simp, by simp⟩

theorem span_gv_le_ln₀ (ν : F) : F ∙ gv ν ≤ ln₀ F :=
  (Submodule.span_singleton_le_iff_mem _ _).2 (gv_mem_ln₀ ν)

theorem isPoint_gv (ν : F) : IsPoint (F ∙ gv ν) := isPoint_span (gv_ne_zero ν)

theorem gv_not_mem_span_e₁ (ν : F) : gv ν ∉ F ∙ e₁ F := fun h => by
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 h
  have := congrFun ht (.inl 1)
  simp at this

theorem span_gv_ne_pt₀ (ν : F) : F ∙ gv ν ≠ pt₀ F := fun h => by
  rw [pt₀_eq_span] at h
  exact gv_not_mem_span_e₁ ν (h ▸ Submodule.mem_span_singleton_self _)

theorem span_gv_inj {ν μ : F} (h : (F ∙ gv ν) = F ∙ gv μ) : ν = μ := by
  have hm : gv ν ∈ F ∙ gv μ := h ▸ Submodule.mem_span_singleton_self _
  obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 hm
  have h1 := congrFun ht (.inl 1)
  have h0 := congrFun ht (.inl 0)
  simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul] at h1 h0
  simp at h1 h0
  rw [h1, one_mul] at h0
  exact h0.symm

theorem span_gv_le_perp (ν μ : F) : F ∙ gv μ ≤ perp (F ∙ gv ν) :=
  (span_gv_le_ln₀ μ).trans (isLine_ln₀.le_perp.trans (perp_antitone (span_gv_le_ln₀ ν)))

theorem eq_pt₀_or_span_gv {c : Submodule F (V4 F)} (hc : IsPoint c) (hcl : c ≤ ln₀ F) :
    c = pt₀ F ∨ ∃ ν : F, c = F ∙ gv ν := by
  obtain ⟨x, hx0, rfl⟩ := exists_eq_span_of_isPoint hc
  have hxl : x ∈ ln₀ F := hcl (Submodule.mem_span_singleton_self x)
  obtain ⟨h2, h3⟩ := mem_ln₀.1 hxl
  by_cases h1 : x (.inl 1) = 0
  · left
    have hx : x = x (.inl 0) • e₁ F :=
      ext4 (by simp) (by simp [h1]) (by simp [h2]) (by simp [h3])
    have h0 : x (.inl 0) ≠ 0 := fun h => hx0 (by rw [hx, h, zero_smul])
    rw [pt₀_eq_span, hx, Submodule.span_singleton_smul_eq (IsUnit.mk0 _ h0)]
  · right
    refine ⟨x (.inl 0) / x (.inl 1), ?_⟩
    have hx : x = x (.inl 1) • gv (x (.inl 0) / x (.inl 1)) := by
      refine ext4 ?_ ?_ ?_ ?_
      · simp
        field_simp
      · simp
      · simp [h2]
      · simp [h3]
    conv_lhs => rw [hx]
    rw [Submodule.span_singleton_smul_eq (IsUnit.mk0 _ h1)]

theorem transv_gv_mem_Q₁ (ν s : F) : transv (gv ν) s ∈ Q₁ F :=
  transv_mem_qLine isLine_ln₀ (gv_mem_ln₀ ν) s

theorem entry_transv_gv (ν s : F) :
    mat (transv (gv ν) s) (.inl 0) (.inr 0) = s * ν ^ 2 ∧
      mat (transv (gv ν) s) (.inl 0) (.inr 1) = s * ν ∧
      mat (transv (gv ν) s) (.inl 1) (.inr 1) = s := by
  refine ⟨?_, ?_, ?_⟩ <;> rw [mat_apply_eq, transv_mulVec, form_apply] <;> simp
  ring

variable [CharP F 2]

theorem mem_qPoint_gv_iff {k : Sp4 F} (hk : k ∈ Q₁ F) (ν : F) :
    k ∈ qPoint (F ∙ gv ν) ↔ mat k (.inl 0) (.inr 0) = ν ^ 2 * mat k (.inl 1) (.inr 1) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hkv := mulVec_of_mem_Q₁ hk
  rw [mem_qPoint]
  constructor
  · rintro ⟨-, h⟩
    have hv : f₁ F + ν • f₂ F ∈ perp (F ∙ gv ν) := by
      rw [mem_perp_span, form_apply]
      simp
      linear_combination ν * h2
    obtain ⟨t, ht⟩ := Submodule.mem_span_singleton.1 (h _ hv)
    have e0 := congrFun ht (.inl 0)
    have e1 := congrFun ht (.inl 1)
    rw [hkv] at e0 e1
    simp at e0 e1
    linear_combination ν * e1 - e0
  · intro hb
    refine ⟨fun v hv => hk v (span_gv_le_ln₀ ν hv), fun v hv => ?_⟩
    rw [mem_perp_span, form_apply] at hv
    simp at hv
    refine Submodule.mem_span_singleton.2
      ⟨mat k (.inl 0) (.inr 1) * v (.inr 0) + mat k (.inl 1) (.inr 1) * v (.inr 1), ?_⟩
    rw [hkv]
    refine ext4 ?_ ?_ ?_ ?_ <;> simp
    linear_combination (-v (.inr 0)) * hb +
      (mat k (.inl 1) (.inr 1) * ν - mat k (.inl 0) (.inr 1)) * hv +
      (mat k (.inl 0) (.inr 1) * ν * v (.inr 0) -
        v (.inr 0) * mat k (.inl 1) (.inr 1) * ν ^ 2) * h2

omit [CharP F 2] in
theorem mem_xPoint_gv_iff {k : Sp4 F} (hk : k ∈ Q₁ F) (ν : F) :
    k ∈ xPoint (F ∙ gv ν) ↔ mat k (.inl 0) (.inr 0) = ν ^ 2 * mat k (.inl 1) (.inr 1) ∧
      mat k (.inl 0) (.inr 1) = ν * mat k (.inl 1) (.inr 1) := by
  rw [mem_xPoint_span (gv_ne_zero ν)]
  constructor
  · rintro ⟨s, rfl⟩
    obtain ⟨e0, e1, e2⟩ := entry_transv_gv ν s
    rw [e0, e1, e2]
    exact ⟨by ring, by ring⟩
  · rintro ⟨hb, hc⟩
    obtain ⟨e0, e1, e2⟩ := entry_transv_gv ν (mat k (.inl 1) (.inr 1))
    refine ⟨mat k (.inl 1) (.inr 1), eq_of_mem_Q₁ (transv_gv_mem_Q₁ _ _) hk ?_ ?_ ?_⟩
    · rw [e0, hb]; ring
    · rw [e1, hc]; ring
    · rw [e2]

theorem mem_qPoint_gv_of {k : Sp4 F} (hk : k ∈ Q₁ F) (hb : mat k (.inl 0) (.inr 0) = 0)
    (hd : mat k (.inl 1) (.inr 1) = 0) (ν : F) : k ∈ qPoint (F ∙ gv ν) :=
  (mem_qPoint_gv_iff hk ν).2 (by rw [hb, hd, mul_zero])

omit [CharP F 2] in
theorem eq_one_of_mem_xPoint_gv {k : Sp4 F} (hk : k ∈ Q₁ F) (hb : mat k (.inl 0) (.inr 0) = 0)
    (hd : mat k (.inl 1) (.inr 1) = 0) {ν : F} (hx : k ∈ xPoint (F ∙ gv ν)) : k = 1 := by
  have hc := ((mem_xPoint_gv_iff hk ν).1 hx).2
  rw [hd, mul_zero] at hc
  exact eq_of_mem_Q₁ hk (one_mem _) (by rw [hb, entry_one]) (by rw [hc, entry_one])
    (by rw [hd, entry_one])

omit [CharP F 2] in
theorem entry_mul_inv_of_mem_Q₁ {k k' : Sp4 F} (hk : k ∈ Q₁ F) (hk' : k' ∈ Q₁ F) (i j : Fin 2) :
    mat (k * k'⁻¹) (.inl i) (.inr j) = mat k (.inl i) (.inr j) - mat k' (.inl i) (.inr j) := by
  rw [entry_mul_of_mem_Q₁ hk (inv_mem hk'), entry_inv_of_mem_Q₁ hk']
  ring

theorem injective_bd_of_inf_le_xPoint {E : Subgroup (Sp4 F)} (hE : E ≤ Q₁ F) {ν : F}
    (hI : E ⊓ qPoint (F ∙ gv ν) ≤ xPoint (F ∙ gv ν)) :
    Function.Injective fun k : E =>
      (mat (k : Sp4 F) (.inl 0) (.inr 0), mat (k : Sp4 F) (.inl 1) (.inr 1)) := by
  intro x y hxy
  have h1 := congrArg Prod.fst hxy
  have h2 := congrArg Prod.snd hxy
  simp only at h1 h2
  have hkE : (x : Sp4 F) * (y : Sp4 F)⁻¹ ∈ E := mul_mem x.2 (inv_mem y.2)
  have hkQ := hE hkE
  have hb : mat ((x : Sp4 F) * (y : Sp4 F)⁻¹) (.inl 0) (.inr 0) = 0 := by
    rw [entry_mul_inv_of_mem_Q₁ (hE x.2) (hE y.2), h1, sub_self]
  have hd : mat ((x : Sp4 F) * (y : Sp4 F)⁻¹) (.inl 1) (.inr 1) = 0 := by
    rw [entry_mul_inv_of_mem_Q₁ (hE x.2) (hE y.2), h2, sub_self]
  have := eq_one_of_mem_xPoint_gv hkQ hb hd (hI ⟨hkE, mem_qPoint_gv_of hkQ hb hd ν⟩)
  exact Subtype.ext (mul_inv_eq_one.1 this)

theorem card_le_sq_of_inf_le_xPoint [Finite F] {E : Subgroup (Sp4 F)} (hE : E ≤ Q₁ F) {ν : F}
    (hI : E ⊓ qPoint (F ∙ gv ν) ≤ xPoint (F ∙ gv ν)) : Nat.card E ≤ Nat.card F ^ 2 := by
  have := Nat.card_le_card_of_injective _ (injective_bd_of_inf_le_xPoint hE hI)
  rwa [Nat.card_prod, ← sq] at this

theorem exists_transv_mem_of_inf_le_xPoint [Finite F] {E : Subgroup (Sp4 F)} (hE : E ≤ Q₁ F)
    {ν : F} (hI : E ⊓ qPoint (F ∙ gv ν) ≤ xPoint (F ∙ gv ν)) (hc : Nat.card F < Nat.card E) :
    ∃ s : F, s ≠ 0 ∧ transv (gv ν) s ∈ E := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  by_contra hne
  push Not at hne
  have hf : Function.Injective fun k : E =>
      mat (k : Sp4 F) (.inl 0) (.inr 0) + ν ^ 2 * mat (k : Sp4 F) (.inl 1) (.inr 1) := by
    intro x y hxy
    simp only at hxy
    have hkE : (x : Sp4 F) * (y : Sp4 F)⁻¹ ∈ E := mul_mem x.2 (inv_mem y.2)
    have hkQ := hE hkE
    have hkq : (x : Sp4 F) * (y : Sp4 F)⁻¹ ∈ qPoint (F ∙ gv ν) := by
      rw [mem_qPoint_gv_iff hkQ, entry_mul_inv_of_mem_Q₁ (hE x.2) (hE y.2),
        entry_mul_inv_of_mem_Q₁ (hE x.2) (hE y.2)]
      linear_combination hxy + (ν ^ 2 * mat (y : Sp4 F) (.inl 1) (.inr 1) -
        ν ^ 2 * mat (x : Sp4 F) (.inl 1) (.inr 1)) * h2
    obtain ⟨s, hs⟩ := (mem_xPoint_span (gv_ne_zero ν)).1 (hI ⟨hkE, hkq⟩)
    by_cases hs0 : s = 0
    · rw [hs0, transv_zero] at hs
      exact Subtype.ext (mul_inv_eq_one.1 hs.symm)
    · exact absurd (hs ▸ hkE) (hne s hs0)
  have := Nat.card_le_card_of_injective _ hf
  omega

theorem exists_not_inf_le_xPoint [Finite F] {A : Subgroup (Sp4 F)} (hA : A ≤ Q₁ F)
    (hAc : Nat.card F ^ 2 ≤ Nat.card A)
    (h51 : ∀ p₁ p₂ : Submodule F (V4 F), IsPoint p₁ → IsPoint p₂ → A ≠ xPoint p₁ ⊔ xPoint p₂) :
    ∃ ν : F, ¬ A ⊓ qPoint (F ∙ gv ν) ≤ xPoint (F ∙ gv ν) := by
  by_contra hall
  push Not at hall
  have hc2 := le_antisymm (card_le_sq_of_inf_le_xPoint hA (hall 0)) hAc
  have hbij := (injective_bd_of_inf_le_xPoint hA (hall 0)).bijective_of_nat_card_le
    (by rw [Nat.card_prod, hc2, sq])
  have hX : ∀ ν : F, xPoint (F ∙ gv ν) ≤ A := by
    intro ν g hg
    obtain ⟨s, rfl⟩ := (mem_xPoint_span (gv_ne_zero ν)).1 hg
    obtain ⟨⟨k, hkA⟩, hk⟩ := hbij.2 (s * ν ^ 2, s)
    simp only [Prod.mk.injEq] at hk
    have hkQ := hA hkA
    have hkq : k ∈ qPoint (F ∙ gv ν) := (mem_qPoint_gv_iff hkQ ν).2 (by rw [hk.1, hk.2]; ring)
    have hkx := (mem_xPoint_gv_iff hkQ ν).1 (hall ν ⟨hkA, hkq⟩)
    obtain ⟨e0, e1, e2⟩ := entry_transv_gv ν s
    have : k = transv (gv ν) s := eq_of_mem_Q₁ hkQ (transv_gv_mem_Q₁ ν s)
      (by rw [hk.1, e0]) (by rw [hkx.2, hk.2, e1]; ring) (by rw [hk.2, e2])
    rw [← this]
    exact hkA
  have hne : (F ∙ gv (0 : F)) ≠ F ∙ gv 1 := fun h => zero_ne_one (span_gv_inj h)
  have hcard := card_xPoint_sup (isPoint_gv 0) (isPoint_gv 1) hne (span_gv_le_perp 0 1)
  exact h51 _ _ (isPoint_gv 0) (isPoint_gv 1)
    (Subgroup.eq_of_le_of_card_ge (sup_le (hX 0) (hX 1)) (by rw [hc2]; exact hcard)).symm

theorem transv_mul_transv_gv {ν₁ ν₂ ν₃ : F} (h12 : ν₁ ≠ ν₂) (h13 : ν₁ ≠ ν₃) (h23 : ν₂ ≠ ν₃) :
    transv (gv ν₁) ((ν₂ + ν₃) ^ 2) * transv (gv ν₂) ((ν₁ + ν₃) ^ 2) ∈ qPoint (F ∙ gv ν₃) ∧
      transv (gv ν₁) ((ν₂ + ν₃) ^ 2) * transv (gv ν₂) ((ν₁ + ν₃) ^ 2) ∉
        xPoint (F ∙ gv ν₃) := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  have hQ₁ := transv_gv_mem_Q₁ ν₁ ((ν₂ + ν₃) ^ 2)
  have hQ₂ := transv_gv_mem_Q₁ ν₂ ((ν₁ + ν₃) ^ 2)
  have hQ := mul_mem hQ₁ hQ₂
  obtain ⟨a0, a1, a2⟩ := entry_transv_gv ν₁ ((ν₂ + ν₃) ^ 2)
  obtain ⟨b0, b1, b2⟩ := entry_transv_gv ν₂ ((ν₁ + ν₃) ^ 2)
  have hne : ∀ {x y : F}, x ≠ y → x + y ≠ 0 := fun {x y} hxy h =>
    hxy (by linear_combination h - y * h2)
  refine ⟨(mem_qPoint_gv_iff hQ ν₃).2 ?_, fun hx => ?_⟩
  · rw [entry_mul_of_mem_Q₁ hQ₁ hQ₂, entry_mul_of_mem_Q₁ hQ₁ hQ₂, a0, b0, a2, b2]
    linear_combination ((ν₁ + ν₃) * (ν₂ + ν₃) * (ν₁ * ν₂ - ν₃ ^ 2)) * h2
  · have hc := ((mem_xPoint_gv_iff hQ ν₃).1 hx).2
    rw [entry_mul_of_mem_Q₁ hQ₁ hQ₂, entry_mul_of_mem_Q₁ hQ₁ hQ₂, a1, b1, a2, b2] at hc
    have : (ν₁ + ν₃) * (ν₂ + ν₃) * (ν₁ + ν₂) = 0 := by
      linear_combination hc + (ν₃ * (ν₁ ^ 2 - ν₁ * ν₂ + ν₁ * ν₃ + ν₂ ^ 2 + ν₂ * ν₃ + ν₃ ^ 2)) * h2
    rcases mul_eq_zero.1 this with h | h
    · rcases mul_eq_zero.1 h with h | h
      · exact hne h13 h
      · exact hne h23 h
    · exact hne h12 h

theorem exists_lam_xPoint {c : Submodule F (V4 F)} (hc : IsPoint c) (hcl : c ≤ ln₀ F) {ν : F}
    (hcν : c ≠ F ∙ gv ν) (s : F) : ∃ y ∈ xPoint c, y ∈ Q₁ F ∧
      mat y (.inl 0) (.inr 0) + ν ^ 2 * mat y (.inl 1) (.inr 1) = s := by
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  rcases eq_pt₀_or_span_gv hc hcl with rfl | ⟨μ, rfl⟩
  · refine ⟨transv (e₁ F) s, transv_mem_X₂ s, transv_e₁_mem_Q₁ s, ?_⟩
    have h0 : mat (transv (e₁ F) s) (.inl 0) (.inr 0) = s := congrArg Prod.fst (q1c_transv_e₁ s)
    have h1 : mat (transv (e₁ F) s) (.inl 1) (.inr 1) = 0 :=
      congrArg (fun x => x.2.2) (q1c_transv_e₁ s)
    rw [h0, h1, mul_zero, add_zero]
  · have hμν : μ + ν ≠ 0 := fun h => hcν (by
      rw [show μ = ν by linear_combination h - ν * h2])
    refine ⟨transv (gv μ) (s / (μ + ν) ^ 2), transv_mem_xPoint _ _, transv_gv_mem_Q₁ _ _, ?_⟩
    obtain ⟨e0, -, e2⟩ := entry_transv_gv μ (s / (μ + ν) ^ 2)
    rw [e0, e2]
    field_simp
    linear_combination (-(s * μ * ν)) * h2

theorem covers_of_lam {Y : Subgroup (Sp4 F)} {ν : F}
    (hY : ∀ s : F, ∃ y ∈ Y, y ∈ Q₁ F ∧
      mat y (.inl 0) (.inr 0) + ν ^ 2 * mat y (.inl 1) (.inr 1) = s) :
    ∀ k ∈ Q₁ F, ∃ y ∈ Y, y ∈ Q₁ F ∧ y * k⁻¹ ∈ qPoint (F ∙ gv ν) := by
  intro k hk
  obtain ⟨y, hyY, hyQ, hy⟩ := hY (mat k (.inl 0) (.inr 0) + ν ^ 2 * mat k (.inl 1) (.inr 1))
  refine ⟨y, hyY, hyQ, (mem_qPoint_gv_iff (mul_mem hyQ (inv_mem hk)) ν).2 ?_⟩
  rw [entry_mul_inv_of_mem_Q₁ hyQ hk, entry_mul_inv_of_mem_Q₁ hyQ hk]
  have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
  linear_combination hy + (ν ^ 2 * mat k (.inl 1) (.inr 1) - ν ^ 2 * mat y (.inl 1) (.inr 1)) * h2

end CFSG.Quasithin.MS93.S5
