module

public import CFSG.Quasithin.Background.ShultG53Layers
public import CFSG.Quasithin.Background.ShultG53IdentPack

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Quasithin.ShultG53

open CFSG.CharacterTheory.SteinbergBY CFSG.Quasithin.RonanG51 CFSG.Quasithin.H13.A6 Equiv

instance decMemG5 (σ : Perm (Fin 6)) : Decidable (σ ∈ g5G1) :=
  (inferInstance : Decidable (Perm.sign σ = 1 ∧ ((σ 4 = 4 ∧ σ 5 = 5) ∨ (σ 4 = 5 ∧ σ 5 = 4))))

instance decMemCA (σ : Perm (Fin 6)) : Decidable (σ ∈ cA6) :=
  (inferInstance : Decidable (σ * iota0 = iota0 * σ ∧ Perm.sign σ = 1))

theorem Hx0_iff : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 →
    (Matrix.mulVec (Rm 0 σ) (![1, 0, 1, 0] : V4) = ![1, 0, 1, 0] ↔ σ ∈ g5G1) :=
  IdentPack.Hx0_iff_code

theorem Hx1_iff : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 →
    (Matrix.mulVec (Rm 1 σ) (![1, 0, 0, 0] : V4) = ![1, 0, 0, 0] ↔ σ ∈ cA6) :=
  IdentPack.Hx1_iff_code

theorem Hl0_iff : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 →
    ((∀ y : V4, predLine4a y → predLine4a (Matrix.mulVec (Rm 0 σ) y)) ↔ σ ∈ cA6) :=
  IdentPack.Hl0_iff_code

theorem Hl1_iff : ∀ σ : Perm (Fin 6), Perm.sign σ = 1 →
    ((∀ y : V4, predLine4b y → predLine4b (Matrix.mulVec (Rm 1 σ) y)) ↔ σ ∈ g5G1) :=
  IdentPack.Hl1_iff_code

theorem nofix_g5G1 : ∀ m : V4, m ≠ 0 →
    ∃ σ : Perm (Fin 6), σ ∈ g5G1 ∧ Matrix.mulVec (Rm 1 σ) m ≠ m :=
  IdentPack.nofix_g5G1_code

theorem nofix_cA6 : ∀ m : V4, m ≠ 0 →
    ∃ σ : Perm (Fin 6), σ ∈ cA6 ∧ Matrix.mulVec (Rm 0 σ) m ≠ m :=
  IdentPack.nofix_cA6_code


theorem identify_module (V : Md ↥(alternatingGroup (Fin 6))) (hirr : V.IsIrred)
    (hcard : Nat.card V.carrier = 2 ^ 4) :
    ∃ (k : Fin 2) (e : V.carrier ≃+ V4),
      ∀ (g : ↥(alternatingGroup (Fin 6))) m, e (V.ρ g m) = ρk k g (e m) := by
  obtain ⟨hnt, hS⟩ := hirr
  haveI := hnt
  obtain ⟨i, f, hf⟩ := a6_complete V.ρ hS
  have hi : i = 1 ∨ i = 2 := by
    have h1 : Nat.card V.carrier = Nat.card (D i) := Nat.card_congr f.toEquiv
    rw [card_D, hcard] at h1
    have h2 := Nat.pow_right_injective (le_refl 2) h1
    revert h2
    fin_cases i <;> decide
  rcases hi with rfl | rfl
  · exact ⟨0, f, hf⟩
  · exact ⟨1, f, hf⟩

theorem no_point_of_conj {k : Fin 2} (V : Md ↥(alternatingGroup (Fin 6))) (e : V.carrier ≃+ V4)
    (he : ∀ (g : ↥(alternatingGroup (Fin 6))) m, e (V.ρ g m) = ρk k g (e m))
    (cA : ↥(alternatingGroup (Fin 6))) (G : Set ↥(alternatingGroup (Fin 6)))
    (P : Perm (Fin 6) → Prop)
    (hG : ∀ g : ↥(alternatingGroup (Fin 6)), g ∈ G ↔ P ((cA * g * cA⁻¹ : _) : Perm (Fin 6)))
    (hno : ∀ m : V4, m ≠ 0 → ∃ σ : Perm (Fin 6), P σ ∧ Perm.sign σ = 1 ∧
      Matrix.mulVec (Rm k σ) m ≠ m)
    (hpt : V.FixesPoint G) : False := by
  obtain ⟨v, hv, hfix⟩ := hpt
  have hev : e v ≠ 0 := fun h => hv (e.injective (h.trans (map_zero e).symm))
  have hm0 : ρk k cA (e v) ≠ 0 := by
    intro h
    apply hev
    have := congrArg (ρk k cA⁻¹) h
    rwa [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply,
      map_zero] at this
  obtain ⟨σ, hP, hs, hne⟩ := hno _ hm0
  let h : ↥(alternatingGroup (Fin 6)) := ⟨σ, Perm.mem_alternatingGroup.mpr hs⟩
  have hgG : cA⁻¹ * h * cA ∈ G := by
    rw [hG]
    have : cA * (cA⁻¹ * h * cA) * cA⁻¹ = h := by group
    rw [this]
    exact hP
  have h1 := hfix _ hgG
  have h2 : ρk k (cA⁻¹ * h * cA) (e v) = e v := by rw [← he, h1]
  apply hne
  have h3 : Matrix.mulVec (Rm k σ) (ρk k cA (e v)) = ρk k h (ρk k cA (e v)) :=
    (ρk_apply k h _).symm
  have h4 : ρk k h (ρk k cA (e v)) = ρk k cA (ρk k (cA⁻¹ * h * cA) (e v)) := by
    rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul]
    congr 2
    group
  rw [h3, h4, h2]

@[expose] def linePred : Fin 2 → V4 → Prop
  | 0 => predLine4a
  | 1 => predLine4b

theorem fin2_cases (k : Fin 2) : k = 0 ∨ k = 1 := by
  fin_cases k <;> simp

theorem identify (G₁ G₂ : Subgroup (Perm (Fin 6))) (c : Perm (Fin 6))
    (hc : c ∈ alternatingGroup (Fin 6))
    (hconj : ((∀ g, g ∈ G₁ ↔ c * g * c⁻¹ ∈ g5G1) ∧ (∀ g, g ∈ G₂ ↔ c * g * c⁻¹ ∈ cA6)) ∨
      ((∀ g, g ∈ G₂ ↔ c * g * c⁻¹ ∈ g5G1) ∧ (∀ g, g ∈ G₁ ↔ c * g * c⁻¹ ∈ cA6)))
    (V₁ V₂ : Md ↥(alternatingGroup (Fin 6)))
    (h₁ : V₁.IsIrred ∧ Nat.card V₁.carrier = 2 ^ 4 ∧ V₁.FixesPoint (inG G₁) ∧
      V₁.FixesLine (inG G₂))
    (h₂ : V₂.IsIrred ∧ Nat.card V₂.carrier = 2 ^ 4 ∧ V₂.FixesPoint (inG G₂) ∧
      V₂.FixesLine (inG G₁)) :
    ∃ (k : Fin 2) (cA : ↥(alternatingGroup (Fin 6))) (e₁ : V₁.carrier ≃+ V4)
      (e₂ : V₂.carrier ≃+ V4),
      (∀ (g : ↥(alternatingGroup (Fin 6))) m, e₁ (V₁.ρ g m) = ρk k g (e₁ m)) ∧
      (∀ (g : ↥(alternatingGroup (Fin 6))) m, e₂ (V₂.ρ g m) = ρk (1 - k) g (e₂ m)) ∧
      (∀ g : ↥(alternatingGroup (Fin 6)),
        g ∈ inG G₁ ↔ ρk k (cA * g * cA⁻¹) (x0 k) = x0 k) ∧
      (∀ g : ↥(alternatingGroup (Fin 6)), g ∈ inG G₂ ↔
        ∀ y : V4, linePred k y → linePred k (ρk k (cA * g * cA⁻¹) y)) := by
  obtain ⟨hirr₁, hcard₁, hpt₁, -⟩ := h₁
  obtain ⟨hirr₂, hcard₂, hpt₂, -⟩ := h₂
  obtain ⟨k₁, e₁, he₁⟩ := identify_module V₁ hirr₁ hcard₁
  obtain ⟨k₂, e₂, he₂⟩ := identify_module V₂ hirr₂ hcard₂
  let cA : ↥(alternatingGroup (Fin 6)) := ⟨c, hc⟩
  have hsign : ∀ g : ↥(alternatingGroup (Fin 6)),
      Perm.sign ((cA * g * cA⁻¹ : ↥(alternatingGroup (Fin 6))) : Perm (Fin 6)) = 1 := fun g =>
    Perm.mem_alternatingGroup.mp (cA * g * cA⁻¹).2
  rcases hconj with ⟨hG1, hG2⟩ | ⟨hG2, hG1⟩
  ·
    have hk1 : k₁ = 0 := by
      rcases fin2_cases k₁ with h | h
      · exact h
      · subst h
        exfalso
        exact no_point_of_conj V₁ e₁ he₁ cA (inG G₁) (fun σ => σ ∈ g5G1)
          (fun g => hG1 (g : Perm (Fin 6)))
          (fun m hm => by
            obtain ⟨σ, h1, h2⟩ := nofix_g5G1 m hm
            exact ⟨σ, h1, h1.1, h2⟩) hpt₁
    have hk2 : k₂ = 1 := by
      rcases fin2_cases k₂ with h | h
      · subst h
        exfalso
        exact no_point_of_conj V₂ e₂ he₂ cA (inG G₂) (fun σ => σ ∈ cA6)
          (fun g => hG2 (g : Perm (Fin 6)))
          (fun m hm => by
            obtain ⟨σ, h1, h2⟩ := nofix_cA6 m hm
            exact ⟨σ, h1, h1.2, h2⟩) hpt₂
      · exact h
    subst hk1
    subst hk2
    refine ⟨0, cA, e₁, e₂, he₁, he₂, fun g => ?_, fun g => ?_⟩
    · rw [ρk_apply]
      have h := Hx0_iff _ (hsign g)
      exact (hG1 (g : Perm (Fin 6))).trans h.symm
    · have h := Hl0_iff _ (hsign g)
      refine (hG2 (g : Perm (Fin 6))).trans (h.symm.trans ?_)
      simp only [ρk_apply]
      exact Iff.rfl
  ·
    have hk1 : k₁ = 1 := by
      rcases fin2_cases k₁ with h | h
      · subst h
        exfalso
        exact no_point_of_conj V₁ e₁ he₁ cA (inG G₁) (fun σ => σ ∈ cA6)
          (fun g => hG1 (g : Perm (Fin 6)))
          (fun m hm => by
            obtain ⟨σ, h1, h2⟩ := nofix_cA6 m hm
            exact ⟨σ, h1, h1.2, h2⟩) hpt₁
      · exact h
    have hk2 : k₂ = 0 := by
      rcases fin2_cases k₂ with h | h
      · exact h
      · subst h
        exfalso
        exact no_point_of_conj V₂ e₂ he₂ cA (inG G₂) (fun σ => σ ∈ g5G1)
          (fun g => hG2 (g : Perm (Fin 6)))
          (fun m hm => by
            obtain ⟨σ, h1, h2⟩ := nofix_g5G1 m hm
            exact ⟨σ, h1, h1.1, h2⟩) hpt₂
    subst hk1
    subst hk2
    refine ⟨1, cA, e₁, e₂, he₁, he₂, fun g => ?_, fun g => ?_⟩
    · rw [ρk_apply]
      have h := Hx1_iff _ (hsign g)
      exact (hG1 (g : Perm (Fin 6))).trans h.symm
    · have h := Hl1_iff _ (hsign g)
      refine (hG2 (g : Perm (Fin 6))).trans (h.symm.trans ?_)
      simp only [ρk_apply]
      exact Iff.rfl

end CFSG.Quasithin.ShultG53
