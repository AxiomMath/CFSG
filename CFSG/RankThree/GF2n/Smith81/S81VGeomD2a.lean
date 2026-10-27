module

public import CFSG.RankThree.GF2n.Smith81.S81VGeomD1

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {F : Type} [Field F] {σ : F ≃+* F}

@[expose] def recipeVec (σ : F ≃+* F) (u₁ w₁ u₂ w₂ : Fin 6 → F) (θ : F) : Fin 6 → F :=
  u₁ + θ • w₁ + u₂ + θ • w₂

@[expose] def recipeSet (σ : F ≃+* F) (p u₁ w₁ u₂ w₂ : Fin 6 → F) (θ : F) :
    Set (Submodule F (Fin 6 → F)) :=
  {Submodule.span F {p, u₁, u₂}, Submodule.span F {p, u₁, w₂}, Submodule.span F {p, w₁, u₂},
    Submodule.span F {p, w₁, w₂}, Submodule.span F {p, recipeVec σ u₁ w₁ u₂ w₂ θ, w₁ + w₂},
    Submodule.span F {p, recipeVec σ u₁ w₁ u₂ w₂ θ, u₁ + σ θ • w₂}}

structure Recipe (σ : F ≃+* F) (p u₁ w₁ u₂ w₂ : Fin 6 → F) (θ : F) : Prop where
  p0 : p ≠ 0
  pp : herm σ p p = 0
  pu₁ : herm σ p u₁ = 0
  pw₁ : herm σ p w₁ = 0
  pu₂ : herm σ p u₂ = 0
  pw₂ : herm σ p w₂ = 0
  u₁u₁ : herm σ u₁ u₁ = 0
  w₁w₁ : herm σ w₁ w₁ = 0
  u₂u₂ : herm σ u₂ u₂ = 0
  w₂w₂ : herm σ w₂ w₂ = 0
  u₁u₂ : herm σ u₁ u₂ = 0
  u₁w₂ : herm σ u₁ w₂ = 0
  w₁u₂ : herm σ w₁ u₂ = 0
  w₁w₂ : herm σ w₁ w₂ = 0
  u₁w₁ : herm σ u₁ w₁ = 1
  u₂w₂ : herm σ u₂ w₂ = 1
  θ0 : θ + σ θ ≠ 0

variable {p u₁ w₁ u₂ w₂ : Fin 6 → F} {θ : F}

private theorem recipe_rev (hσ : ∀ c, σ (σ c) = c) (h : Recipe σ p u₁ w₁ u₂ w₂ θ) :
    herm σ w₁ u₁ = 1 ∧ herm σ w₂ u₂ = 1 ∧ herm σ u₂ u₁ = 0 ∧ herm σ u₂ w₁ = 0 ∧
    herm σ w₂ u₁ = 0 ∧ herm σ w₂ w₁ = 0 ∧ herm σ w₁ p = 0 ∧ herm σ u₁ p = 0 ∧
    herm σ u₂ p = 0 ∧ herm σ w₂ p = 0 := by
  refine ⟨?_, ?_, herm_eq_zero_comm σ hσ h.u₁u₂, herm_eq_zero_comm σ hσ h.w₁u₂,
    herm_eq_zero_comm σ hσ h.u₁w₂, herm_eq_zero_comm σ hσ h.w₁w₂,
    herm_eq_zero_comm σ hσ h.pw₁, herm_eq_zero_comm σ hσ h.pu₁,
    herm_eq_zero_comm σ hσ h.pu₂, herm_eq_zero_comm σ hσ h.pw₂⟩
  · rw [herm_conj σ hσ, h.u₁w₁, map_one]
  · rw [herm_conj σ hσ, h.u₂w₂, map_one]

private theorem coeff5 (hli : LinearIndependent F ![p, u₁, w₁, u₂, w₂]) {a b c d e : F}
    (h : a • p + b • u₁ + c • w₁ + d • u₂ + e • w₂ = 0) :
    a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0 ∧ e = 0 := by
  have hc := Fintype.linearIndependent_iff.1 hli ![a, b, c, d, e]
    (by simpa [Fin.sum_univ_five] using h)
  exact ⟨by simpa using hc 0, by simpa using hc 1, by simpa using hc 2, by simpa using hc 3,
    by simpa using hc 4⟩

theorem Recipe.li5 (hσ : ∀ c, σ (σ c) = c) (h : Recipe σ p u₁ w₁ u₂ w₂ θ) :
    LinearIndependent F ![p, u₁, w₁, u₂, w₂] := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ := recipe_rev hσ h
  rw [Fintype.linearIndependent_iff]
  intro g hg
  rw [Fin.sum_univ_five] at hg
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hg
  have e1 : g 1 = 0 := by
    have := congrArg (herm σ w₁) hg
    simpa [r1, r7, h.w₁w₁, h.w₁u₂, h.w₁w₂] using this
  have e2 : g 2 = 0 := by
    have := congrArg (herm σ u₁) hg
    simpa [h.u₁w₁, r8, h.u₁u₁, h.u₁u₂, h.u₁w₂] using this
  have e3 : g 3 = 0 := by
    have := congrArg (herm σ w₂) hg
    simpa [r10, r5, r6, r2, h.w₂w₂] using this
  have e4 : g 4 = 0 := by
    have := congrArg (herm σ u₂) hg
    simpa [r9, r3, r4, h.u₂u₂, h.u₂w₂] using this
  have e0 : g 0 = 0 := by
    simp only [e1, e2, e3, e4, zero_smul, add_zero, zero_add] at hg
    exact (smul_eq_zero.mp hg).resolve_right h.p0
  intro i
  fin_cases i
  exacts [e0, e1, e2, e3, e4]

theorem Recipe.herm_c (hσ : ∀ c, σ (σ c) = c) [CharP F 2] (h : Recipe σ p u₁ w₁ u₂ w₂ θ) :
    herm σ (recipeVec σ u₁ w₁ u₂ w₂ θ) (recipeVec σ u₁ w₁ u₂ w₂ θ) = 0 ∧
    herm σ (recipeVec σ u₁ w₁ u₂ w₂ θ) (w₁ + w₂) = 0 ∧
    herm σ (recipeVec σ u₁ w₁ u₂ w₂ θ) (u₁ + σ θ • w₂) = 0 ∧
    herm σ p (recipeVec σ u₁ w₁ u₂ w₂ θ) = 0 := by
  obtain ⟨r1, r2, r3, r4, r5, r6, r7, r8, r9, r10⟩ := recipe_rev hσ h
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  unfold recipeVec
  refine ⟨?_, ?_, ?_, ?_⟩
  · simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, r1, r2, r3, r4,
      r5, r6, r7, r8, r9, r10, h.u₁u₁, h.u₁w₁, h.u₁u₂, h.u₁w₂, h.w₁w₁, h.w₁u₂, h.w₁w₂,
      h.u₂u₂, h.u₂w₂, h.w₂w₂]
    linear_combination (θ + σ θ) * two
  · simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, r1, r2, r3, r4,
      r5, r6, r7, r8, r9, r10, h.u₁u₁, h.u₁w₁, h.u₁u₂, h.u₁w₂, h.w₁w₁, h.w₁u₂, h.w₁w₂,
      h.u₂u₂, h.u₂w₂, h.w₂w₂]
    linear_combination two
  · simp only [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, r1, r2, r3, r4,
      r5, r6, r7, r8, r9, r10, h.u₁u₁, h.u₁w₁, h.u₁u₂, h.u₁w₂, h.w₁w₁, h.w₁u₂, h.w₁w₂,
      h.u₂u₂, h.u₂w₂, h.w₂w₂]
    linear_combination (σ θ) * two
  · simp [herm_add_right, herm_smul_right, h.pu₁, h.pw₁, h.pu₂, h.pw₂]

theorem Recipe.isPt_all [CharP F 2] (hσ : ∀ c, σ (σ c) = c) (h : Recipe σ p u₁ w₁ u₂ w₂ θ) :
    ∀ G ∈ recipeSet σ p u₁ w₁ u₂ w₂ θ, IsPt σ G := by
  intro G hG
  obtain ⟨hc1, hc2, hc3, hc4⟩ := Recipe.herm_c hσ h
  have hli := h.li5 hσ
  have hwz : herm σ (w₁ + w₂) (w₁ + w₂) = 0 := by
    simp [herm_add_left, herm_add_right, h.w₁w₁, h.w₁w₂, h.w₂w₂, herm_eq_zero_comm σ hσ h.w₁w₂]
  have hpz : herm σ p (w₁ + w₂) = 0 := by
    simp [herm_add_right, h.pw₁, h.pw₂]
  have hzz : herm σ (u₁ + σ θ • w₂) (u₁ + σ θ • w₂) = 0 := by
    simp [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, h.u₁u₁, h.u₁w₂,
      herm_eq_zero_comm σ hσ h.u₁w₂, h.w₂w₂]
  have hpz' : herm σ p (u₁ + σ θ • w₂) = 0 := by
    simp [herm_add_right, herm_smul_right, h.pu₁, h.pw₂]
  simp only [recipeSet, Set.mem_insert_iff, Set.mem_singleton_iff] at hG
  rcases hG with rfl | rfl | rfl | rfl | rfl | rfl
  · have hli' : LinearIndependent F ![p, u₁, u₂] := by
      have e : (![p, u₁, w₁, u₂, w₂] ∘ ![0, 1, 3] : Fin 3 → Fin 6 → F) = ![p, u₁, u₂] := by
        funext i
        fin_cases i <;> rfl
      have := hli.comp ![0, 1, 3] (by decide)
      rwa [e] at this
    exact isPt_span_triple hσ h.pp h.u₁u₁ h.u₂u₂ h.pu₁ h.pu₂ h.u₁u₂ hli'
  · have hli' : LinearIndependent F ![p, u₁, w₂] := by
      have e : (![p, u₁, w₁, u₂, w₂] ∘ ![0, 1, 4] : Fin 3 → Fin 6 → F) = ![p, u₁, w₂] := by
        funext i
        fin_cases i <;> rfl
      have := hli.comp ![0, 1, 4] (by decide)
      rwa [e] at this
    exact isPt_span_triple hσ h.pp h.u₁u₁ h.w₂w₂ h.pu₁ h.pw₂ h.u₁w₂ hli'
  · have hli' : LinearIndependent F ![p, w₁, u₂] := by
      have e : (![p, u₁, w₁, u₂, w₂] ∘ ![0, 2, 3] : Fin 3 → Fin 6 → F) = ![p, w₁, u₂] := by
        funext i
        fin_cases i <;> rfl
      have := hli.comp ![0, 2, 3] (by decide)
      rwa [e] at this
    exact isPt_span_triple hσ h.pp h.w₁w₁ h.u₂u₂ h.pw₁ h.pu₂ h.w₁u₂ hli'
  · have hli' : LinearIndependent F ![p, w₁, w₂] := by
      have e : (![p, u₁, w₁, u₂, w₂] ∘ ![0, 2, 4] : Fin 3 → Fin 6 → F) = ![p, w₁, w₂] := by
        funext i
        fin_cases i <;> rfl
      have := hli.comp ![0, 2, 4] (by decide)
      rwa [e] at this
    exact isPt_span_triple hσ h.pp h.w₁w₁ h.w₂w₂ h.pw₁ h.pw₂ h.w₁w₂ hli'
  · have hli' : LinearIndependent F ![p, recipeVec σ u₁ w₁ u₂ w₂ θ, w₁ + w₂] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_three] at hg
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hg
      have hg' : g 0 • p + g 1 • (u₁ + θ • w₁ + u₂ + θ • w₂) + g 2 • (w₁ + w₂) = 0 := by
        unfold recipeVec at hg
        exact hg
      obtain ⟨a0, a1, a2, -, -⟩ := coeff5 hli (a := g 0) (b := g 1) (c := g 1 * θ + g 2)
        (d := g 1) (e := g 1 * θ + g 2) (by linear_combination (norm := module) hg')
      have g2 : g 2 = 0 := by linear_combination a2 - θ * a1
      intro i
      fin_cases i
      exacts [a0, a1, g2]
    exact isPt_span_triple hσ h.pp hc1 hwz hc4 hpz hc2 hli'
  · have hli' : LinearIndependent F ![p, recipeVec σ u₁ w₁ u₂ w₂ θ, u₁ + σ θ • w₂] := by
      rw [Fintype.linearIndependent_iff]
      intro g hg
      rw [Fin.sum_univ_three] at hg
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hg
      have hg' : g 0 • p + g 1 • (u₁ + θ • w₁ + u₂ + θ • w₂) + g 2 • (u₁ + σ θ • w₂) = 0 := by
        unfold recipeVec at hg
        exact hg
      obtain ⟨a0, a1, -, a3, -⟩ := coeff5 hli (a := g 0) (b := g 1 + g 2) (c := g 1 * θ)
        (d := g 1) (e := g 1 * θ + g 2 * σ θ) (by linear_combination (norm := module) hg')
      have g2 : g 2 = 0 := by linear_combination a1 - a3
      intro i
      fin_cases i
      exacts [a0, a3, g2]
    exact isPt_span_triple hσ h.pp hc1 hzz hc4 hpz' hc3 hli'

end CFSG.RankThree.GF2n.Smith81.S81V
