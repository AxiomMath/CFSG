module

public import CFSG.RankThree.GF2n.Smith81.S81VGeomD2a
public import CFSG.RankThree.GF2n.Smith81.S81VGeomD3a
public import CFSG.RankThree.GF2n.Smith81.S81VGeomCD

public section

namespace CFSG.RankThree.GF2n.Smith81.S81V

open CFSG.ClassicalGroups.Unitary CFSG.RankThree.GF2n.Smith81.U6Cube Module

variable {F : Type} [Field F] {σ : F ≃+* F}
variable {p u₁ w₁ u₂ w₂ : Fin 6 → F} {θ : F}

private theorem herm_zero_on_span {w : Fin 6 → F} {S : Set (Fin 6 → F)}
    (hS : ∀ s ∈ S, herm σ w s = 0) : ∀ g ∈ Submodule.span F S, herm σ w g = 0 := by
  intro g hg
  induction hg using Submodule.span_induction with
  | mem s hs => exact hS s hs
  | zero => exact herm_zero_right σ w
  | add a b _ _ iha ihb => rw [herm_add_right, iha, ihb, add_zero]
  | smul c a _ iha => rw [herm_smul_right, iha, mul_zero]

private theorem herm_span3_zero {w x y z : Fin 6 → F} (hx : herm σ w x = 0)
    (hy : herm σ w y = 0) (hz : herm σ w z = 0) :
    ∀ g ∈ Submodule.span F {x, y, z}, herm σ w g = 0 := by
  apply herm_zero_on_span
  intro s hs
  simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hs
  rcases hs with rfl | rfl | rfl <;> assumption

theorem Recipe.closure [Finite F] [CharP F 2] (hσ : IsUnitaryInvolution σ)
    (h : Recipe σ p u₁ w₁ u₂ w₂ θ) :
    ∀ G, IsPt σ G → p ∈ G → GenPts σ (recipeSet σ p u₁ w₁ u₂ w₂ θ) G := by
  have hinv : ∀ x, σ (σ x) = x := hσ.invol
  have two : (2 : F) = 0 := CharTwo.two_eq_zero
  have v1 : herm σ w₁ u₁ = 1 := by rw [herm_conj σ hinv, h.u₁w₁, map_one]
  have v2 : herm σ w₂ u₂ = 1 := by rw [herm_conj σ hinv, h.u₂w₂, map_one]
  have v5 : herm σ w₂ u₁ = 0 := herm_eq_zero_comm σ hinv h.u₁w₂
  have v6 : herm σ w₂ w₁ = 0 := herm_eq_zero_comm σ hinv h.w₁w₂
  have v7 : herm σ u₁ p = 0 := herm_eq_zero_comm σ hinv h.pu₁
  have v9 : herm σ w₂ p = 0 := herm_eq_zero_comm σ hinv h.pw₂
  have hpts := Recipe.isPt_all hinv h
  have hli5 := h.li5 hinv
  obtain ⟨c, hc⟩ : ∃ c, c = recipeVec σ u₁ w₁ u₂ w₂ θ := ⟨_, rfl⟩
  obtain ⟨hc1, -, -, hc4⟩ := Recipe.herm_c hinv h
  rw [← hc] at hc1 hc4
  have e_uc : herm σ u₁ c = θ := by
    rw [hc]
    simp [recipeVec, herm_add_right, herm_smul_right, h.u₁u₁, h.u₁w₁, h.u₁u₂, h.u₁w₂]
  have e_wc : herm σ w₁ c = 1 := by
    rw [hc]
    simp [recipeVec, herm_add_right, herm_smul_right, v1, h.w₁w₁, h.w₁u₂, h.w₁w₂]
  have e_w2c : herm σ w₂ c = 1 := by
    rw [hc]
    simp [recipeVec, herm_add_right, herm_smul_right, v5, v6, v2, h.w₂w₂]
  have e_cu : herm σ c u₁ = σ θ := by rw [herm_conj σ hinv, e_uc]
  have e_cw : herm σ c w₁ = 1 := by rw [herm_conj σ hinv, e_wc, map_one]
  have hdet : (Matrix.of fun i j => herm σ (![u₁, w₁, c] i) (![u₁, w₁, c] j)).det ≠ 0 := by
    have e : (Matrix.of fun i j => herm σ (![u₁, w₁, c] i) (![u₁, w₁, c] j)).det = θ + σ θ := by
      rw [Matrix.det_fin_three]
      simp [h.u₁u₁, h.u₁w₁, e_uc, v1, h.w₁w₁, e_wc, e_cu, e_cw, hc1]
      ring
    rw [e]
    exact h.θ0
  have hU := nonDeg_span_of_gram hinv ![u₁, w₁, c] hdet
  have h3 := finrank_span_of_gram ![u₁, w₁, c] hdet
  have hind := linearIndependent_of_gram ![u₁, w₁, c] hdet
  have haU : u₁ ∈ Submodule.span F (Set.range ![u₁, w₁, c]) :=
    Submodule.subset_span (Set.mem_range_self 0)
  have hbU : w₁ ∈ Submodule.span F (Set.range ![u₁, w₁, c]) :=
    Submodule.subset_span (Set.mem_range_self 1)
  have hcU : c ∈ Submodule.span F (Set.range ![u₁, w₁, c]) :=
    Submodule.subset_span (Set.mem_range_self 2)
  have hUρ : ∀ u ∈ Submodule.span F (Set.range ![u₁, w₁, c]), herm σ p u = 0 := by
    apply herm_zero_on_span
    rintro _ ⟨i, rfl⟩
    fin_cases i
    · exact h.pu₁
    · exact h.pw₁
    · exact hc4
  have hpu1 : LinearIndependent F ![p, u₁] := by
    have e : (![p, u₁, w₁, u₂, w₂] ∘ ![0, 1] : Fin 2 → Fin 6 → F) = ![p, u₁] := by
      funext i
      fin_cases i <;> rfl
    have := hli5.comp ![0, 1] (by decide)
    rwa [e] at this
  have hpw1 : LinearIndependent F ![p, w₁] := by
    have e : (![p, u₁, w₁, u₂, w₂] ∘ ![0, 2] : Fin 2 → Fin 6 → F) = ![p, w₁] := by
      funext i
      fin_cases i <;> rfl
    have := hli5.comp ![0, 2] (by decide)
    rwa [e] at this
  have hpc : LinearIndependent F ![p, c] := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    rw [Fin.sum_univ_two] at hg
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hg
    have hg1 : g 1 = 0 := by
      have h' := congrArg (herm σ w₂) hg
      simpa [herm_add_right, herm_smul_right, v9, e_w2c] using h'
    rw [hg1, zero_smul, add_zero] at hg
    have hg0 : g 0 = 0 := (smul_eq_zero.mp hg).resolve_right h.p0
    intro i
    fin_cases i
    exacts [hg0, hg1]
  have m1 : Submodule.span F {p, u₁, u₂} ∈ recipeSet σ p u₁ w₁ u₂ w₂ θ := Set.mem_insert _ _
  have m2 : Submodule.span F {p, u₁, w₂} ∈ recipeSet σ p u₁ w₁ u₂ w₂ θ :=
    Set.mem_insert_of_mem _ (Set.mem_insert _ _)
  have m3 : Submodule.span F {p, w₁, u₂} ∈ recipeSet σ p u₁ w₁ u₂ w₂ θ :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))
  have m4 : Submodule.span F {p, w₁, w₂} ∈ recipeSet σ p u₁ w₁ u₂ w₂ θ :=
    Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert _ _)))
  have m5 : Submodule.span F {p, c, w₁ + w₂} ∈ recipeSet σ p u₁ w₁ u₂ w₂ θ := by
    rw [hc]
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
  have m6 : Submodule.span F {p, c, u₁ + σ θ • w₂} ∈ recipeSet σ p u₁ w₁ u₂ w₂ θ := by
    rw [hc]
    exact Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _
      (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_singleton _)))))
  have hne12 : Submodule.span F {p, u₁, u₂} ≠ Submodule.span F {p, u₁, w₂} := by
    intro heq
    have hu2 : u₂ ∈ Submodule.span F {p, u₁, w₂} := by
      rw [← heq]
      exact Submodule.subset_span (by simp)
    have h0 := herm_span3_zero v9 v5 h.w₂w₂ u₂ hu2
    rw [v2] at h0
    exact one_ne_zero h0
  have hne34 : Submodule.span F {p, w₁, u₂} ≠ Submodule.span F {p, w₁, w₂} := by
    intro heq
    have hu2 : u₂ ∈ Submodule.span F {p, w₁, w₂} := by
      rw [← heq]
      exact Submodule.subset_span (by simp)
    have h0 := herm_span3_zero v9 v6 h.w₂w₂ u₂ hu2
    rw [v2] at h0
    exact one_ne_zero h0
  have hzp : herm σ (u₁ + σ θ • w₂) p = 0 := by
    simp [herm_add_left, herm_smul_left, hinv, v7, v9]
  have hzc : herm σ (u₁ + σ θ • w₂) c = 0 := by
    rw [herm_add_left, herm_smul_left, hinv, e_uc, e_w2c]
    linear_combination θ * two
  have hzz : herm σ (u₁ + σ θ • w₂) (u₁ + σ θ • w₂) = 0 := by
    simp [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hinv, h.u₁u₁,
      h.u₁w₂, v5, h.w₂w₂]
  have hzw : herm σ (u₁ + σ θ • w₂) (w₁ + w₂) = 1 := by
    simp [herm_add_left, herm_add_right, herm_smul_left, herm_smul_right, hinv, h.u₁w₁,
      h.u₁w₂, v6, h.w₂w₂]
  have hne56 : Submodule.span F {p, c, w₁ + w₂} ≠ Submodule.span F {p, c, u₁ + σ θ • w₂} := by
    intro heq
    have hmem : w₁ + w₂ ∈ Submodule.span F {p, c, u₁ + σ θ • w₂} := by
      rw [← heq]
      exact Submodule.subset_span (by simp)
    have h0 := herm_span3_zero hzp hzc hzz (w₁ + w₂) hmem
    rw [hzw] at h0
    exact one_ne_zero h0
  have hGa := genPts_of_two_through hpu1 (hpts _ m1) (hpts _ m2) hne12
    (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
    (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
    (GenPts.base m1) (GenPts.base m2)
  have hGb := genPts_of_two_through hpw1 (hpts _ m3) (hpts _ m4) hne34
    (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
    (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
    (GenPts.base m3) (GenPts.base m4)
  have hGc := genPts_of_two_through hpc (hpts _ m5) (hpts _ m6) hne56
    (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
    (Submodule.subset_span (by simp)) (Submodule.subset_span (by simp))
    (GenPts.base m5) (GenPts.base m6)
  intro G hG hpG
  exact lemmaD hσ h.p0 h.pp hU h3 hUρ haU hbU hcU h.u₁u₁ h.w₁w₁ hc1 hind hGa hGb hGc G hG hpG

end CFSG.RankThree.GF2n.Smith81.S81V
