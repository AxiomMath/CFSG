module

public import CFSG.Quasithin.Background.B2FactorizationBridge

public section

namespace CFSG.Quasithin.Vol2.Ch10.SecC.C10KH

open CFSG.Open CFSG.Quasithin

variable {Γ : Type} [Group Γ] {V : Subgroup Γ} (hV : IsElemAbelian 2 V)

@[expose] def intSub (V₁ : Subgroup Γ) : Subgroup (IntMod V hV) where
  carrier := {w | w.val ∈ V₁}
  mul_mem' {a b} ha hb := by
    change (a * b).val ∈ V₁
    rw [IntMod.val_mul]
    exact V₁.mul_mem ha hb
  one_mem' := by
    change (1 : IntMod V hV).val ∈ V₁
    rw [IntMod.val_one]
    exact V₁.one_mem
  inv_mem' {a} ha := by
    change (a⁻¹).val ∈ V₁
    rw [IntMod.val_inv]
    exact V₁.inv_mem ha

theorem mem_intSub {V₁ : Subgroup Γ} {w : IntMod V hV} : w ∈ intSub hV V₁ ↔ w.val ∈ V₁ :=
  Iff.rfl

@[expose] def TorusAut (Jst Lst : Subgroup (MulAut (IntMod V hV))) (V1 : Subgroup (IntMod V hV))
    (m : ℕ) : Prop :=
  ∃ φ ∈ Jst, (∀ w ∈ V1, φ w ∈ V1) ∧ (∃ w ∈ V1, φ w ≠ w) ∧
    (∀ ψ ∈ Lst, ∀ w ∈ V1, (φ * ψ * φ⁻¹ * ψ⁻¹) w = w) ∧ ∀ w ∈ V1, (φ ^ m) w = w

theorem mem_centralizer_of_fix {V₁ : Subgroup Γ} (hV₁V : V₁ ≤ V)
    (g : Subgroup.normalizer (V : Set Γ)) (h : ∀ w ∈ intSub hV V₁, convI hV g w = w) :
    (g : Γ) ∈ Subgroup.centralizer (V₁ : Set Γ) := by
  rw [Subgroup.mem_centralizer_iff]
  intro v hv
  have h1 := congrArg IntMod.val (h (IntMod.mk hV ⟨v, hV₁V hv⟩) hv)
  rw [convI_apply_val] at h1
  change (g : Γ) * v * (g : Γ)⁻¹ = v at h1
  calc v * (g : Γ) = ((g : Γ) * v * (g : Γ)⁻¹) * g := by rw [h1]
    _ = g * v := by group

theorem conclusion_of_torusAut [Finite Γ] {J L V₁ : Subgroup Γ}
    (hLN : L ≤ Subgroup.normalizer (V : Set Γ)) (hV₁V : V₁ ≤ V) {m : ℕ}
    (h : TorusAut hV (autI hV J) (autI hV L) (intSub hV V₁) m) :
    ∃ y ∈ J ⊓ Subgroup.normalizer (V₁ : Set Γ), y ∉ Subgroup.centralizer (V₁ : Set Γ) ∧
      (∀ l ∈ L, y * l * y⁻¹ * l⁻¹ ∈ Subgroup.centralizer (V₁ : Set Γ)) ∧
      y ^ m ∈ Subgroup.centralizer (V₁ : Set Γ) := by
  obtain ⟨φ, hφJ, h1, ⟨w₀, hw₀, hne⟩, h3, h4⟩ := h
  obtain ⟨g, hgJ, rfl⟩ := (mem_autI hV).1 hφJ
  have hmap : (intSub hV V₁).map (convI hV g).toMonoidHom = intSub hV V₁ := by
    refine Subgroup.eq_of_le_of_card_ge ?_ ?_
    · rintro _ ⟨w, hw, rfl⟩
      exact h1 w hw
    · exact (Subgroup.card_map_of_injective (f := (convI hV g).toMonoidHom)
        (MulEquiv.injective _)).ge
  refine ⟨g, ⟨hgJ, ?_⟩, fun hc => hne ?_, fun l hl => ?_, ?_⟩
  · show (g : Γ) ∈ Subgroup.normalizer (V₁ : Set Γ)
    rw [Subgroup.mem_normalizer_iff]
    intro v
    constructor
    · intro hv
      have h2 := h1 (IntMod.mk hV ⟨v, hV₁V hv⟩) hv
      rw [mem_intSub, convI_apply_val] at h2
      exact h2
    · intro hv
      have hvV : v ∈ V := by
        have hy : (g : Γ) * v * (g : Γ)⁻¹ ∈ V := hV₁V hv
        exact ((Subgroup.mem_normalizer_iff.mp g.2) v).mpr hy
      have hmem : IntMod.mk hV ⟨(g : Γ) * v * (g : Γ)⁻¹, hV₁V hv⟩ ∈ intSub hV V₁ := hv
      rw [← hmap] at hmem
      obtain ⟨w, hw, hw'⟩ := hmem
      have hw'' : w = IntMod.mk hV ⟨v, hvV⟩ := by
        apply (convI hV g).injective
        apply IntMod.val_injective
        have := congrArg IntMod.val hw'
        change (convI hV g w).val = (g : Γ) * v * (g : Γ)⁻¹ at this
        rw [this, convI_apply_val]
        rfl
      rw [hw''] at hw
      exact hw
  · have h2 := Subgroup.mem_centralizer_iff.mp hc w₀.val hw₀
    apply IntMod.val_injective
    rw [convI_apply_val, ← h2, mul_inv_cancel_right]
  · have hlN : l ∈ Subgroup.normalizer (V : Set Γ) := hLN hl
    set ψ := convI hV ⟨l, hlN⟩ with hψ
    have hψL : ψ ∈ autI hV L := convI_mem_autI hV hl hlN
    have hc : ψ * ψ⁻¹ = 1 := mul_inv_cancel ψ
    let k : Subgroup.normalizer (V : Set Γ) := g * ⟨l, hlN⟩ * g⁻¹ * ⟨l, hlN⟩⁻¹
    have hk : convI hV k = convI hV g * ψ * (convI hV g)⁻¹ * ψ⁻¹ := by
      simp only [k, map_mul, map_inv, hψ]
    have := mem_centralizer_of_fix hV hV₁V k fun w hw => by
      rw [hk]
      exact h3 ψ hψL w hw
    exact this
  · let k : Subgroup.normalizer (V : Set Γ) := g ^ m
    have := mem_centralizer_of_fix hV hV₁V k fun w hw => by
      change convI hV (g ^ m) w = w
      rw [map_pow]
      exact h4 w hw
    simpa [k] using this

end CFSG.Quasithin.Vol2.Ch10.SecC.C10KH
