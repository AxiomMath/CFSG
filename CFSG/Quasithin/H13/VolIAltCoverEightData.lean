module

public import CFSG.Quasithin.H13.VolIAltCoverSevenCosets

public section

namespace CFSG.Quasithin.H13.VolI

open CFSG.Quasithin CFSG.Quasithin.G6 Subgroup Equiv

@[expose] def liftPerm : Perm (Fin 7) →* Perm (Fin 8) where
  toFun σ := Perm.decomposeFin.symm (0, σ)
  map_one' := by
    rw [Perm.decomposeFin_symm_of_one, swap_self]
    rfl
  map_mul' σ τ := by
    ext x
    induction x using Fin.cases with
    | zero => simp
    | succ i => simp

theorem sign_liftPerm (σ : Perm (Fin 7)) : Perm.sign (liftPerm σ) = Perm.sign σ := by
  show Perm.sign (Perm.decomposeFin.symm (0, σ)) = _
  simp

theorem liftPerm_surj {τ : Perm (Fin 8)} (hτ : τ 0 = 0) : ∃ σ, liftPerm σ = τ := by
  refine ⟨(Perm.decomposeFin τ).2, ?_⟩
  have h1 : (Perm.decomposeFin τ).1 = 0 := by
    have h := Perm.decomposeFin_symm_apply_zero (Perm.decomposeFin τ).1 (Perm.decomposeFin τ).2
    rw [Prod.mk.eta, Equiv.symm_apply_apply] at h
    rw [← h, hτ]
  show Perm.decomposeFin.symm (0, (Perm.decomposeFin τ).2) = τ
  rw [← h1, Prod.mk.eta, Equiv.symm_apply_apply]

@[expose] def liftAlt : ↥(alternatingGroup (Fin 7)) →* ↥(alternatingGroup (Fin 8)) :=
  (liftPerm.comp (alternatingGroup (Fin 7)).subtype).codRestrict _ fun σ => by
    rw [MonoidHom.comp_apply, Perm.mem_alternatingGroup, sign_liftPerm]
    exact Perm.mem_alternatingGroup.1 σ.2

theorem liftAlt_surj (τ : ↥(alternatingGroup (Fin 8))) (hτ : (τ : Perm (Fin 8)) 0 = 0) :
    ∃ σ, liftAlt σ = τ := by
  obtain ⟨σ, hσ⟩ := liftPerm_surj hτ
  have hσa : σ ∈ alternatingGroup (Fin 7) := by
    rw [Perm.mem_alternatingGroup, ← sign_liftPerm, hσ]
    exact Perm.mem_alternatingGroup.1 τ.2
  exact ⟨⟨σ, hσa⟩, Subtype.ext hσ⟩

theorem alt7_induction (P : ↥(alternatingGroup (Fin 7)) → Prop) (h1 : P 1)
    (hmul : ∀ a b, P a → P b → P (a * b)) (h₁ : P a7c012) (h₂ : P a7c234) (h₃ : P a7c456) :
    ∀ σ, P σ := by
  have hL : ∀ g, P g → ∀ a ∈ [1, g, g * g], P a := by
    intro g hg a ha
    simp only [List.mem_cons, List.not_mem_nil, or_false] at ha
    rcases ha with rfl | rfl | rfl
    · exact h1
    · exact hg
    · exact hmul _ _ hg hg
  have hA5 : ∀ σ : ↥(alternatingGroup (Fin 7)), (σ : Perm (Fin 7)) 5 = 5 →
      (σ : Perm (Fin 7)) 6 = 6 → P σ := by
    intro σ h5 h6
    obtain ⟨a, ha, b, hb, c, hc, d, hd, e, he, f, hf, rfl⟩ := alt7_words σ h5 h6
    exact hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hmul _ _ (hL _ h₁ a ha) (hL _ h₂ b hb))
      (hL _ h₁ c hc)) (hL _ h₂ d hd)) (hL _ h₁ e he)) (hL _ h₂ f hf)
  have hs : P a7s := hmul _ _ (hmul _ _ h₃ h₂) (hmul _ _ h₃ h₃)
  have hA6 : ∀ σ : ↥(alternatingGroup (Fin 7)), (σ : Perm (Fin 7)) 6 = 6 → P σ := by
    intro σ h6
    rcases alt7_cosets5 σ h6 with h5 | ⟨h, hh, hk5⟩
    · exact hA5 σ h5 h6
    · obtain ⟨hh5, hh6⟩ := a7reps5_fix h hh
      have hk6 : (((h * a7s)⁻¹ * σ : ↥(alternatingGroup (Fin 7))) : Perm (Fin 7)) 6 = 6 := by
        have hs6 : (((h * a7s : ↥(alternatingGroup (Fin 7)))) : Perm (Fin 7)) 6 = 6 := by
          rw [Subgroup.coe_mul, Perm.mul_apply, a7s_six, hh6]
        rw [Subgroup.coe_mul, Perm.mul_apply, h6, Subgroup.coe_inv, Perm.inv_eq_iff_eq, hs6]
      have e : σ = h * a7s * ((h * a7s)⁻¹ * σ) := by group
      rw [e]
      exact hmul _ _ (hmul _ _ (hA5 h hh5 hh6) hs) (hA5 _ hk5 hk6)
  intro σ
  rcases alt7_cosets6 σ with h6 | ⟨h, hh, hk6⟩
  · exact hA6 σ h6
  · have e : σ = h * a7c456 * ((h * a7c456)⁻¹ * σ) := by group
    rw [e]
    exact hmul _ _ (hmul _ _ (hA6 h (a7reps6_fix h hh)) h₃) (hA6 _ hk6)

@[expose] def a8c012 : ↥(alternatingGroup (Fin 8)) :=
  ⟨swap 0 1 * swap 1 2, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def a8c123 : ↥(alternatingGroup (Fin 8)) :=
  ⟨swap 1 2 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def a8c345 : ↥(alternatingGroup (Fin 8)) :=
  ⟨swap 3 4 * swap 4 5, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def a8c456 : ↥(alternatingGroup (Fin 8)) :=
  ⟨swap 4 5 * swap 5 6, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def a8c567 : ↥(alternatingGroup (Fin 8)) :=
  ⟨swap 5 6 * swap 6 7, by rw [Perm.mem_alternatingGroup]; decide⟩

@[expose] def a8h : ↥(alternatingGroup (Fin 8)) :=
  ⟨swap 0 7 * swap 1 2, by rw [Perm.mem_alternatingGroup]; decide⟩

theorem a8c123_pow : a8c123 ^ 3 = 1 := by decide

theorem a8c345_pow : a8c345 ^ 3 = 1 := by decide

theorem a8c567_pow : a8c567 ^ 3 = 1 := by decide

theorem a8h_mul_self : a8h * a8h = 1 := by decide

theorem liftAlt_a7c012 : liftAlt a7c012 = a8c123 := by decide

theorem liftAlt_a7c234 : liftAlt a7c234 = a8c345 := by decide

theorem liftAlt_a7c456 : liftAlt a7c456 = a8c567 := by decide

theorem a8_fix : (a8c123 : Perm (Fin 8)) 0 = 0 ∧ (a8c345 : Perm (Fin 8)) 0 = 0 ∧
    (a8c456 : Perm (Fin 8)) 0 = 0 ∧ (a8c123 : Perm (Fin 8)) 7 = 7 ∧
    (a8c345 : Perm (Fin 8)) 7 = 7 ∧ (a8c456 : Perm (Fin 8)) 7 = 7 ∧
    (a8c012 : Perm (Fin 8)) 7 = 7 := by
  decide

theorem a8h_zero : (a8h : Perm (Fin 8)) 0 = 7 := by decide

theorem a8h_seven : (a8h : Perm (Fin 8)) 7 = 0 := by decide

theorem a8c012_zero : (a8c012 : Perm (Fin 8)) 0 = 1 := by decide

@[expose] def rep8 : Fin 8 → ↥(alternatingGroup (Fin 8)) :=
  ![1, 1, ⟨swap 1 2 * swap 2 3, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 1 3 * swap 3 2, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 1 4 * swap 4 2, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 1 5 * swap 5 2, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 1 6 * swap 6 2, by rw [Perm.mem_alternatingGroup]; decide⟩,
    ⟨swap 1 7 * swap 7 2, by rw [Perm.mem_alternatingGroup]; decide⟩]

theorem rep8_spec : ∀ j : Fin 8, j ≠ 0 →
    (rep8 j : Perm (Fin 8)) 0 = 0 ∧ (rep8 j : Perm (Fin 8)) 1 = j := by
  decide

end CFSG.Quasithin.H13.VolI
