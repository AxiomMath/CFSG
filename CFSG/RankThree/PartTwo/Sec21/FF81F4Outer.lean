module

public import CFSG.LocalAnalysis.SeitzReduction.F4PilotEndFieldBasic
public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.RankThree.PartTwo.Sec21.FF79Vocab

public section

namespace CFSG.RankThree.PartTwo.Sec21.FF81.F4

open CFSG CFSG.RankThree.PartTwo.Sec21 CFSG.RankThree.PartTwo.Sec21.FF79
open CFSG.SeitzReduction.F4Pilot

section Model

variable {X : Type} [Group X] {Y : Subgroup X} {C : Type} [Group C] (e : ↥Y ≃* C)

noncomputable def indAut {τ : X} (hτ : τ ∈ Nor Y) : MulAut C :=
  normalizerMulAut e ⟨τ, hτ⟩

theorem indAut_apply {τ : X} (hτ : τ ∈ Nor Y) (w : C) :
    ((e.symm (indAut e hτ w) : ↥Y) : X) = τ * (e.symm w : X) * τ⁻¹ :=
  coe_symm_normalizerMulAut_apply e ⟨τ, hτ⟩ w

theorem indAut_mul {σ τ : X} (hσ : σ ∈ Nor Y) (hτ : τ ∈ Nor Y) (hστ : σ * τ ∈ Nor Y) :
    indAut e hστ = indAut e hσ * indAut e hτ :=
  map_mul (normalizerMulAut e) (⟨σ, hσ⟩ : ↥(Nor Y)) ⟨τ, hτ⟩

theorem indAut_of_mem {y : X} (hy : y ∈ Y) (hyN : y ∈ Nor Y) :
    indAut e hyN = MulAut.conj (e ⟨y, hy⟩) :=
  normalizerMulAut_of_mem e hy

theorem indAut_sq {τ : X} (hτ : τ ∈ Nor Y) (h2 : τ ^ 2 = 1) : indAut e hτ ^ 2 = 1 := by
  have h3 : normalizerMulAut e (⟨τ, hτ⟩ ^ 2 : ↥(Nor Y)) = indAut e hτ ^ 2 :=
    map_pow (normalizerMulAut e) (⟨τ, hτ⟩ : ↥(Nor Y)) 2
  rw [← h3]
  have h : (⟨τ, hτ⟩ ^ 2 : ↥(Nor Y)) = 1 := Subtype.ext h2
  exact (congrArg (normalizerMulAut e) h).trans (map_one _)

theorem indAut_not_inner_iff {τ : X} (hτ : τ ∈ Nor Y) :
    indAut e hτ ∉ (MulAut.conj : C →* MulAut C).range ↔
      ¬ ∃ y ∈ Y, ∀ x ∈ Y, τ * x * τ⁻¹ = y * x * y⁻¹ := by
  constructor
  · rintro hn ⟨y, hy, h⟩
    apply hn
    refine ⟨e ⟨y, hy⟩, ?_⟩
    refine MulEquiv.ext (fun w => ?_)
    apply e.symm.injective
    apply Subtype.ext
    have h1 := indAut_apply e hτ w
    have h2 := h (e.symm w : X) (e.symm w).2
    rw [MulAut.conj_apply]
    simp only [map_mul, map_inv, MulEquiv.symm_apply_apply, Subgroup.coe_mul, Subgroup.coe_inv]
    rw [h1, h2]
  · rintro hn ⟨c, hc⟩
    apply hn
    refine ⟨(e.symm c : X), (e.symm c).2, fun x hx => ?_⟩
    have h1 := indAut_apply e hτ (e ⟨x, hx⟩)
    have h2 : indAut e hτ (e ⟨x, hx⟩) = c * e ⟨x, hx⟩ * c⁻¹ := by
      rw [← hc]; rfl
    rw [h2] at h1
    simpa using h1.symm


theorem indAut_eq_one_iff {σ : X} (hσ : σ ∈ Nor Y) :
    indAut e hσ = 1 ↔ ∀ x ∈ Y, σ * x * σ⁻¹ = x := by
  constructor
  · intro h x hx
    have h1 := indAut_apply e hσ (e ⟨x, hx⟩)
    rw [h] at h1
    simpa using h1.symm
  · intro h
    refine MulEquiv.ext (fun w => ?_)
    apply e.symm.injective
    apply Subtype.ext
    rw [indAut_apply e hσ w]
    exact h _ (e.symm w).2

theorem mem_sup_zpowers_of_sq {τ : X} (hτ : τ ∈ Nor Y) (h2 : τ ^ 2 = 1) {g : X}
    (hg : g ∈ Y ⊔ Subgroup.zpowers τ) : g ∈ Y ∨ ∃ y ∈ Y, g = y * τ := by
  have hτi : τ⁻¹ = τ := by
    rw [inv_eq_iff_mul_eq_one, ← pow_two, h2]
  have hconj : ∀ y ∈ Y, τ * y * τ⁻¹ ∈ Y := fun y hy =>
    ((Subgroup.mem_normalizer_iff.1 hτ) y).1 hy
  rw [Subgroup.sup_eq_closure] at hg
  induction hg using Subgroup.closure_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact Or.inl hx
    · obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hx
      have h2z : τ ^ (2 : ℤ) = 1 := by rw [zpow_two, ← pow_two, h2]
      have hk : τ ^ k = 1 ∨ τ ^ k = τ := by
        rcases Int.emod_two_eq_zero_or_one k with hk | hk
        · left
          obtain ⟨m, rfl⟩ : 2 ∣ k := Int.dvd_of_emod_eq_zero hk
          rw [zpow_mul, h2z, one_zpow]
        · right
          obtain ⟨m, rfl⟩ : ∃ m, k = 2 * m + 1 := ⟨k / 2, by omega⟩
          rw [zpow_add, zpow_mul, h2z, one_zpow, one_mul, zpow_one]
      rcases hk with hk | hk
      · exact Or.inl (hk ▸ Y.one_mem)
      · exact Or.inr ⟨1, Y.one_mem, by rw [hk, one_mul]⟩
  | one => exact Or.inl Y.one_mem
  | mul a b _ _ ha hb =>
    rcases ha with ha | ⟨y₁, hy₁, rfl⟩ <;> rcases hb with hb | ⟨y₂, hy₂, rfl⟩
    · exact Or.inl (Y.mul_mem ha hb)
    · exact Or.inr ⟨a * y₂, Y.mul_mem ha hy₂, by rw [mul_assoc]⟩
    · refine Or.inr ⟨y₁ * (τ * b * τ⁻¹), Y.mul_mem hy₁ (hconj b hb), ?_⟩
      group
    · refine Or.inl ?_
      have : y₁ * τ * (y₂ * τ) = y₁ * (τ * y₂ * τ⁻¹) * τ ^ 2 := by
        rw [pow_two]; group
      rw [this, h2, mul_one]
      exact Y.mul_mem hy₁ (hconj y₂ hy₂)
  | inv a _ ha =>
    rcases ha with ha | ⟨y, hy, rfl⟩
    · exact Or.inl (Y.inv_mem ha)
    · refine Or.inr ⟨τ * y⁻¹ * τ⁻¹, hconj _ (Y.inv_mem hy), ?_⟩
      rw [mul_inv_rev, inv_mul_cancel_right, hτi]


section Outer

variable (hZ : ∀ z : C, (∀ w : C, z * w = w * z) → z = 1)

include hZ in
theorem eq_one_of_centralizes {τ : X} (hτ : τ ∈ Nor Y) (h2 : τ ^ 2 = 1)
    (hout : indAut e hτ ∉ (MulAut.conj : C →* MulAut C).range) {g : X}
    (hg : g ∈ Y ⊔ Subgroup.zpowers τ) (hc : ∀ x ∈ Y, g * x * g⁻¹ = x) : g = 1 := by
  rcases mem_sup_zpowers_of_sq hτ h2 hg with hgY | ⟨y, hy, rfl⟩
  · have hz : e ⟨g, hgY⟩ = 1 := by
      apply hZ
      intro w
      apply e.symm.injective
      apply Subtype.ext
      have h1 := hc (e.symm w : X) (e.symm w).2
      simp only [map_mul, MulEquiv.symm_apply_apply, Subgroup.coe_mul]
      calc g * (e.symm w : X) = g * (e.symm w : X) * g⁻¹ * g := by group
        _ = (e.symm w : X) * g := by rw [h1]
    have : (⟨g, hgY⟩ : ↥Y) = 1 := e.injective (hz.trans (map_one e).symm)
    exact congrArg Subtype.val this
  · exfalso
    apply (indAut_not_inner_iff e hτ).1 hout
    refine ⟨y⁻¹, Y.inv_mem hy, fun x hx => ?_⟩
    have h1 := hc x hx
    have h3 : τ * x * τ⁻¹ = y⁻¹ * x * y := by
      have h4 : τ * x * τ⁻¹ = y⁻¹ * (y * τ * x * (y * τ)⁻¹) * y := by group
      rw [h1] at h4
      exact h4
    rw [h3]; group


variable (hX : ∀ α β : MulAut C, α ^ 2 = 1 → β ^ 2 = 1 → α ∉ (MulAut.conj : C →* MulAut C).range →
    β ∉ (MulAut.conj : C →* MulAut C).range →
      ∃ h : C, β = MulAut.conj h * α * (MulAut.conj h)⁻¹)

include e hZ hX in
theorem exists_conj_of_outer {τ : X} (hτ : τ ∈ Nor Y) (h2 : τ ^ 2 = 1)
    (hout : ¬ ∃ y ∈ Y, ∀ x ∈ Y, τ * x * τ⁻¹ = y * x * y⁻¹) {σ : X}
    (hσ : σ ∈ Y ⊔ Subgroup.zpowers τ) (hσ2 : σ ^ 2 = 1) (hσY : σ ∉ Y) :
    ∃ c ∈ Y, c * τ * c⁻¹ = σ := by
  have hHN : Y ⊔ Subgroup.zpowers τ ≤ Nor Y :=
    sup_le Subgroup.le_normalizer (Subgroup.zpowers_le.2 hτ)
  have hσN : σ ∈ Nor Y := hHN hσ
  have hαo : indAut e hτ ∉ (MulAut.conj : C →* MulAut C).range :=
    (indAut_not_inner_iff e hτ).2 hout
  have hβo : indAut e hσN ∉ (MulAut.conj : C →* MulAut C).range := by
    rcases mem_sup_zpowers_of_sq hτ h2 hσ with h | ⟨y, hy, hyσ⟩
    · exact absurd h hσY
    · subst hyσ
      have hβ : indAut e hσN = MulAut.conj (e ⟨y, hy⟩) * indAut e hτ := by
        rw [indAut_mul e (Subgroup.le_normalizer hy) hτ hσN,
          indAut_of_mem e hy (Subgroup.le_normalizer hy)]
      rintro ⟨c, hc⟩
      apply hαo
      refine ⟨(e ⟨y, hy⟩)⁻¹ * c, ?_⟩
      calc MulAut.conj ((e ⟨y, hy⟩)⁻¹ * c) = (MulAut.conj (e ⟨y, hy⟩))⁻¹ * MulAut.conj c := by
            rw [map_mul, map_inv]
        _ = (MulAut.conj (e ⟨y, hy⟩))⁻¹ * indAut e hσN := by rw [hc]
        _ = (MulAut.conj (e ⟨y, hy⟩))⁻¹ * (MulAut.conj (e ⟨y, hy⟩) * indAut e hτ) := by rw [hβ]
        _ = indAut e hτ := inv_mul_cancel_left _ _
  obtain ⟨h, hh⟩ := hX _ _ (indAut_sq e hτ h2) (indAut_sq e hσN hσ2) hαo hβo
  set c : X := (e.symm h : X) with hcdef
  have hc : c ∈ Y := (e.symm h).2
  have hch : e ⟨c, hc⟩ = h := e.apply_symm_apply h
  have hcN : c ∈ Nor Y := Subgroup.le_normalizer hc
  have hciN : c⁻¹ ∈ Nor Y := Subgroup.le_normalizer (Y.inv_mem hc)
  have htN : c * τ * c⁻¹ ∈ Nor Y := mul_mem (mul_mem hcN hτ) hciN
  have hti : indAut e htN = MulAut.conj h * indAut e hτ * (MulAut.conj h)⁻¹ := by
    rw [indAut_mul e (mul_mem hcN hτ) hciN htN, indAut_mul e hcN hτ (mul_mem hcN hτ),
      indAut_of_mem e hc hcN, indAut_of_mem e (Y.inv_mem hc) hciN, hch]
    have : e ⟨c⁻¹, Y.inv_mem hc⟩ = h⁻¹ := by
      rw [← hch, ← map_inv]; rfl
    rw [this, map_inv]
  have hσt : indAut e hσN = indAut e htN := hh.trans hti.symm
  have hpt : ∀ x ∈ Y, σ * x * σ⁻¹ = (c * τ * c⁻¹) * x * (c * τ * c⁻¹)⁻¹ := by
    intro x hx
    have h1 := indAut_apply e hσN (e ⟨x, hx⟩)
    have h2' := indAut_apply e htN (e ⟨x, hx⟩)
    rw [hσt] at h1
    rw [h1] at h2'
    simp only [MulEquiv.symm_apply_apply] at h2'
    exact h2'
  have hgH : σ⁻¹ * (c * τ * c⁻¹) ∈ Y ⊔ Subgroup.zpowers τ := by
    refine mul_mem (inv_mem hσ) (mul_mem (mul_mem ?_ ?_) (inv_mem ?_))
    · exact Subgroup.mem_sup_left hc
    · exact Subgroup.mem_sup_right (Subgroup.mem_zpowers τ)
    · exact Subgroup.mem_sup_left hc
  have hg1 := eq_one_of_centralizes e hZ hτ h2 hαo hgH (fun x hx => by
    have := hpt x hx
    calc σ⁻¹ * (c * τ * c⁻¹) * x * (σ⁻¹ * (c * τ * c⁻¹))⁻¹
        = σ⁻¹ * ((c * τ * c⁻¹) * x * (c * τ * c⁻¹)⁻¹) * σ := by group
      _ = σ⁻¹ * (σ * x * σ⁻¹) * σ := by rw [this]
      _ = x := by group)
  exact ⟨c, hc, (inv_mul_eq_one.1 hg1).symm⟩

end Outer

end Model

end CFSG.RankThree.PartTwo.Sec21.FF81.F4
