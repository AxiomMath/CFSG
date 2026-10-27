module

public import CFSG.LocalAnalysis.UniquenessCase.UC6AutKernels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6

open Subgroup CFSG.Open CFSG.ABGLocalTools

variable {S S' : Type} [Group S] [Group S'] {r : ℕ} {E : Subgroup S}

theorem AbsKC.of_mulEquiv (e : S ≃* S') (h : AbsKC S r E) : AbsKC S' r (E.map e.toMonoidHom) := by
  intro α' hord hfix
  obtain ⟨k, hk⟩ := hord
  set α : MulAut S := MulAut.congr e.symm α' with hα
  have hα_ord : orderOf α = r ^ k := by
    rw [hα, MulEquiv.orderOf_eq]
    exact hk
  have hα_apply : ∀ x : S, α x = e.symm (α' (e x)) := fun x => rfl
  obtain ⟨g, hgE, hg⟩ := h α ⟨k, hα_ord⟩ (fun x hx => by
    rw [hα_apply]
    have := hfix (e x) ⟨x, hx, rfl⟩
    rw [this]
    simp)
  refine ⟨e g, ⟨g, hgE, rfl⟩, ?_⟩
  ext y
  have h1 := congrArg (fun β : MulAut S => e (β (e.symm y))) hg
  simp only [hα_apply, MulAut.conj_apply, map_mul, map_inv, MulEquiv.apply_symm_apply] at h1
  simpa [MulAut.conj_apply] using h1

theorem congr_apply_uc6 (e : S ≃* S') (α : MulAut S) (y : S') :
    MulAut.congr e α y = e (α (e.symm y)) := rfl

theorem congr_symm_apply_uc6 (e : S ≃* S') (α' : MulAut S') (x : S) :
    (MulAut.congr e).symm α' x = e.symm (α' (e x)) := rfl

theorem congr_conj_uc6 (e : S ≃* S') (x : S) :
    MulAut.congr e (MulAut.conj x) = MulAut.conj (e x) := by
  ext y
  rw [congr_apply_uc6]
  simp [MulAut.conj_apply]

theorem AbsKN.of_mulEquiv {isL34 : Prop} (e : S ≃* S') (h : AbsKN S r E isL34) :
    AbsKN S' r (E.map e.toMonoidHom) isL34 := by
  intro X' hX'E hX'r
  set X : Subgroup (MulAut S) := X'.comap (MulAut.congr e).toMonoidHom with hX
  have hmemX : ∀ x : MulAut S, x ∈ X ↔ MulAut.congr e x ∈ X' := fun x => Iff.rfl
  have h1 : ∀ ε ∈ E, ∀ x ∈ X, MulAut.conj ε * x * (MulAut.conj ε)⁻¹ ∈ X := by
    intro ε hε x hx
    rw [hmemX] at hx ⊢
    have := hX'E (e ε) ⟨ε, hε, rfl⟩ _ hx
    simp only [map_mul, map_inv, congr_conj_uc6]
    exact this
  have h2 : ∀ x ∈ X, (∃ k : ℕ, orderOf x = r ^ k) → x = 1 := by
    intro x hx hord
    obtain ⟨k, hk⟩ := hord
    have := hX'r (MulAut.congr e x) hx ⟨k, by rw [MulEquiv.orderOf_eq]; exact hk⟩
    exact (MulAut.congr e).injective (by rw [this, map_one])
  obtain ⟨hcent, hdisj⟩ := h X h1 h2
  have hsymm : ∀ x' : MulAut S', (MulAut.congr e).symm x' ∈ X ↔ x' ∈ X' := by
    intro x'
    rw [hmemX, MulEquiv.apply_symm_apply]
  refine ⟨fun x' hx' ε' hε' => ?_, ?_⟩
  · obtain ⟨ε, hε, rfl⟩ := hε'
    have hxX : (MulAut.congr e).symm x' ∈ X := (hsymm x').2 hx'
    have h3 := hcent _ hxX ε hε
    show x' (e ε) = e ε
    have h4 : x' (e ε) = MulAut.congr e ((MulAut.congr e).symm x') (e ε) := by
      rw [MulEquiv.apply_symm_apply]
    rw [h4, congr_apply_uc6, MulEquiv.symm_apply_apply, h3]
  · rcases hdisj with hbot | hL34
    · left
      rw [eq_bot_iff]
      intro x' hx'
      have hxX : (MulAut.congr e).symm x' ∈ X := (hsymm x').2 hx'
      rw [hbot] at hxX
      have h5 := Subgroup.mem_bot.1 hxX
      rw [Subgroup.mem_bot]
      have h6 := congrArg (MulAut.congr e) h5
      rw [MulEquiv.apply_symm_apply, map_one] at h6
      exact h6
    · exact Or.inr hL34

theorem AbsKInv.of_mulEquiv (e : S ≃* S') (h : AbsKInv S E) : AbsKInv S' (E.map e.toMonoidHom) := by
  intro x' y' hx' hy' hxE hyE hx1 hy1
  have hord : ∀ z' : MulAut S', ∀ p : ℕ, (∃ k : ℕ, orderOf z' = p ^ k) →
      ∃ k : ℕ, orderOf ((MulAut.congr e).symm z') = p ^ k := by
    rintro z' p ⟨k, hk⟩
    exact ⟨k, by rw [MulEquiv.orderOf_eq]; exact hk⟩
  have hfix : ∀ z' : MulAut S', (∀ ε' ∈ E.map e.toMonoidHom, z' ε' = ε') →
      ∀ ε ∈ E, (MulAut.congr e).symm z' ε = ε := by
    intro z' hz' ε hε
    rw [congr_symm_apply_uc6, hz' (e ε) ⟨ε, hε, rfl⟩, MulEquiv.symm_apply_apply]
  have hne : ∀ z' : MulAut S', z' ≠ 1 → (MulAut.congr e).symm z' ≠ 1 := by
    intro z' hz' h1
    exact hz' ((MulAut.congr e).symm.injective (by rw [h1, map_one]))
  have := h _ _ (hord x' 2 hx') (hord y' 2 hy') (hfix x' hxE) (hfix y' hyE) (hne x' hx1) (hne y' hy1)
  exact (MulAut.congr e).symm.injective this

theorem eq_map_conj_of_isSylowOf [Finite S] [Fact r.Prime] {E₀ : Subgroup S}
    (h₀ : IsSylowOf r E₀ ⊤) (h : IsSylowOf r E ⊤) :
    ∃ k : S, E = E₀.map (MulAut.conj k).toMonoidHom := by
  obtain ⟨k, -, hk⟩ := h₀.exists_mem_conj h
  refine ⟨k, ?_⟩
  ext x
  constructor
  · intro hx
    exact ⟨k⁻¹ * x * k, (hk x).1 hx, by simp [MulAut.conj_apply, mul_assoc]⟩
  · rintro ⟨y, hy, rfl⟩
    refine (hk _).2 ?_
    simpa [MulAut.conj_apply, mul_assoc] using hy

theorem AbsKC.of_isSylowOf [Finite S] [Fact r.Prime] {E₀ : Subgroup S} (h₀ : IsSylowOf r E₀ ⊤)
    (h : IsSylowOf r E ⊤) (hK : AbsKC S r E₀) : AbsKC S r E := by
  obtain ⟨k, hk⟩ := eq_map_conj_of_isSylowOf h₀ h
  rw [hk]
  exact AbsKC.of_mulEquiv (MulAut.conj k) hK

theorem AbsKN.of_isSylowOf [Finite S] [Fact r.Prime] {isL34 : Prop} {E₀ : Subgroup S}
    (h₀ : IsSylowOf r E₀ ⊤) (h : IsSylowOf r E ⊤) (hK : AbsKN S r E₀ isL34) :
    AbsKN S r E isL34 := by
  obtain ⟨k, hk⟩ := eq_map_conj_of_isSylowOf h₀ h
  rw [hk]
  exact AbsKN.of_mulEquiv (MulAut.conj k) hK

theorem AbsKInv.of_isSylowOf [Finite S] [Fact r.Prime] {E₀ : Subgroup S} (h₀ : IsSylowOf r E₀ ⊤)
    (h : IsSylowOf r E ⊤) (hK : AbsKInv S E₀) : AbsKInv S E := by
  obtain ⟨k, hk⟩ := eq_map_conj_of_isSylowOf h₀ h
  rw [hk]
  exact AbsKInv.of_mulEquiv (MulAut.conj k) hK

theorem map_map_symm_uc6 (φ : S ≃* S') (E : Subgroup S) :
    (E.map φ.toMonoidHom).map φ.symm.toMonoidHom = E := by
  ext x
  constructor
  · rintro ⟨y, ⟨z, hz, rfl⟩, rfl⟩
    simpa using hz
  · intro hx
    exact ⟨φ x, ⟨x, hx, rfl⟩, by simp⟩

theorem AbsKC.of_iso_sylow {S₀ : Type} [Group S₀] [Finite S₀] [Fact r.Prime] (φ : S ≃* S₀)
    {E₀ : Subgroup S₀} (h₀ : IsSylowOf r E₀ ⊤) (hE : IsSylowOf r (E.map φ.toMonoidHom) ⊤)
    (hK : AbsKC S₀ r E₀) : AbsKC S r E := by
  have h2 := AbsKC.of_mulEquiv φ.symm (AbsKC.of_isSylowOf h₀ hE hK)
  rwa [map_map_symm_uc6] at h2

theorem AbsKN.of_iso_sylow {S₀ : Type} [Group S₀] [Finite S₀] [Fact r.Prime] {isL34 : Prop}
    (φ : S ≃* S₀) {E₀ : Subgroup S₀} (h₀ : IsSylowOf r E₀ ⊤)
    (hE : IsSylowOf r (E.map φ.toMonoidHom) ⊤) (hK : AbsKN S₀ r E₀ isL34) :
    AbsKN S r E isL34 := by
  have h2 := AbsKN.of_mulEquiv φ.symm (AbsKN.of_isSylowOf h₀ hE hK)
  rwa [map_map_symm_uc6] at h2

theorem AbsKInv.of_iso_sylow {S₀ : Type} [Group S₀] [Finite S₀] [Fact r.Prime] (φ : S ≃* S₀)
    {E₀ : Subgroup S₀} (h₀ : IsSylowOf r E₀ ⊤) (hE : IsSylowOf r (E.map φ.toMonoidHom) ⊤)
    (hK : AbsKInv S₀ E₀) : AbsKInv S E := by
  have h2 := AbsKInv.of_mulEquiv φ.symm (AbsKInv.of_isSylowOf h₀ hE hK)
  rwa [map_map_symm_uc6] at h2

end CFSG.LocalAnalysis.UniquenessCase.UC6
