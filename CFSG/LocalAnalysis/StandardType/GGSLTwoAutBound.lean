module

public import CFSG.LocalAnalysis.StandardType.GGKGForkLinNsA
public import CFSG.Adapters.StatedSLTwoField
public import CFSG.LocalAnalysis.StandardType.GGOneFiveDefs

public section

namespace CFSG.StandardType

open CFSG CFSG.Open CFSG.Assembly

theorem card_signs_four :
    Nat.card {ε : Fin 4 → ZMod 3 // ∀ i, ε i = 1 ∨ ε i = -1} = 16 := by
  rw [Nat.card_eq_fintype_card]
  decide

theorem card_automizer_le_384_of_slTwo {G : Type} [Group G] {m : ℕ}
    (hG : StatedClassicalModel G .PSL m 2 1) {Bs : Subgroup G} (hBsE : IsElemAbelian 3 Bs)
    (hcard : Nat.card Bs = 3 ^ 4)
    (hsc : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ 3 = 1 → g ∈ Bs)
    {A : Subgroup (MulAut ↥Bs)}
    (hA : ∀ φ ∈ A, ∃ g : G, ∀ b : ↥Bs, ((φ b : ↥Bs) : G) = g * b * g⁻¹) :
    Nat.card A ≤ 384 := by
  classical
  obtain ⟨e⟩ := CFSG.Open.StatedAPI.nonempty_mulEquiv_specialLinear_zmod_two_of_psl hG
  have hT : GGTorusSignedEltSC 3 (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) :=
    ggKGLn_signedEltSC_specialLinear Nat.prime_three (by norm_num) (by decide)
      (by rw [Nat.card_eq_fintype_card, ZMod.card])
  set E : Subgroup (Matrix.SpecialLinearGroup (Fin m) (ZMod 2)) := Bs.map e.toMonoidHom with hEdef
  have hE : IsElemAbelian 3 E := TableB.isElemAbelian_map hBsE _
  have hEcard : Nat.card E = 3 ^ 4 := by
    rw [← hcard]
    exact Subgroup.card_map_of_injective e.injective
  have hEsc : ∀ g : Matrix.SpecialLinearGroup (Fin m) (ZMod 2), (∀ x ∈ E, g * x = x * g) →
      g ^ 3 = 1 → g ∈ E := by
    intro g hg hg3
    have hc : e.symm g ∈ Subgroup.centralizer (Bs : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro b hb
      have h1 := hg (e b) ⟨b, hb, rfl⟩
      apply e.injective
      simp only [map_mul, MulEquiv.apply_symm_apply]
      exact h1.symm
    have h3 : (e.symm g) ^ 3 = 1 := by rw [← map_pow, hg3, map_one]
    exact ⟨e.symm g, hsc _ hc h3, by simp⟩
  obtain ⟨k, τ, hτ, hτE, -, -, hsign⟩ := hT E hE (by rw [hEcard]; norm_num) hEsc
  have hk : k = 4 := by
    have h1 : Nat.card τ.range = Nat.card (Fin k → Multiplicative (ZMod 3)) :=
      Nat.card_congr (MonoidHom.ofInjective hτ).toEquiv.symm
    rw [hτE, hEcard, Nat.card_fun, Nat.card_eq_fintype_card (α := Multiplicative (ZMod 3)),
      Fintype.card_multiplicative, ZMod.card, Nat.card_eq_fintype_card, Fintype.card_fin] at h1
    exact (Nat.pow_right_injective (by norm_num : 2 ≤ 3) h1).symm
  subst hk
  have hreal : ∀ φ : A, ∃ g : Matrix.SpecialLinearGroup (Fin m) (ZMod 2),
      (∀ x ∈ E, g * x * g⁻¹ ∈ E) ∧ ∀ b : ↥Bs, e (φ.1 b) = g * e b * g⁻¹ := by
    rintro ⟨φ, hφ⟩
    obtain ⟨g, hg⟩ := hA φ hφ
    refine ⟨e g, ?_, fun b => ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      refine ⟨((φ ⟨b, hb⟩ : ↥Bs) : G), (φ ⟨b, hb⟩).2, ?_⟩
      simp only [MulEquiv.coe_toMonoidHom, hg ⟨b, hb⟩, map_mul, map_inv]
    · rw [hg b]
      simp [map_mul, map_inv]
  choose g hgN hgφ using hreal
  have hs : ∀ φ : A, ∃ (π : Equiv.Perm (Fin 4)) (ε : Fin 4 → ZMod 3), (∀ i, ε i = 1 ∨ ε i = -1) ∧
      ∀ f f', g φ * τ f * (g φ)⁻¹ = τ f' →
        ∀ i, Multiplicative.toAdd (f' (π i)) = ε i * Multiplicative.toAdd (f i) :=
    fun φ => hsign (g φ) (hgN φ)
  choose π ε hε hπε using hs
  let F : A → Equiv.Perm (Fin 4) × {ε : Fin 4 → ZMod 3 // ∀ i, ε i = 1 ∨ ε i = -1} :=
    fun φ => (π φ, ⟨ε φ, hε φ⟩)
  have hFinj : Function.Injective F := by
    intro φ₁ φ₂ h
    simp only [F, Prod.mk.injEq, Subtype.mk.injEq] at h
    obtain ⟨hπ, hε'⟩ := h
    apply Subtype.ext
    ext b
    obtain ⟨f, hf⟩ : e b ∈ τ.range := by rw [hτE]; exact ⟨b, b.2, rfl⟩
    obtain ⟨f₁, hf₁⟩ : g φ₁ * τ f * (g φ₁)⁻¹ ∈ τ.range := by
      rw [hτE]; exact hgN φ₁ _ (hτE ▸ ⟨f, rfl⟩)
    obtain ⟨f₂, hf₂⟩ : g φ₂ * τ f * (g φ₂)⁻¹ ∈ τ.range := by
      rw [hτE]; exact hgN φ₂ _ (hτE ▸ ⟨f, rfl⟩)
    have h₁ := hπε φ₁ f f₁ hf₁.symm
    have h₂ := hπε φ₂ f f₂ hf₂.symm
    have hff : f₁ = f₂ := by
      funext j
      obtain ⟨i, rfl⟩ := (π φ₁).surjective j
      apply Multiplicative.toAdd.injective
      rw [h₁ i]
      conv_lhs => rw [hε']
      rw [hπ, ← h₂ i]
    have he₁ := hgφ φ₁ b
    have he₂ := hgφ φ₂ b
    rw [← hf] at he₁ he₂
    have : e (φ₁.1 b) = e (φ₂.1 b) := by rw [he₁, he₂, ← hf₁, ← hf₂, hff]
    exact e.injective this
  calc Nat.card A ≤ Nat.card (Equiv.Perm (Fin 4) ×
        {ε : Fin 4 → ZMod 3 // ∀ i, ε i = 1 ∨ ε i = -1}) := Nat.card_le_card_of_injective F hFinj
    _ = 384 := by
      rw [Nat.card_prod, card_signs_four, Nat.card_perm, Nat.card_eq_fintype_card,
        Fintype.card_fin]
      rfl

end CFSG.StandardType

end
