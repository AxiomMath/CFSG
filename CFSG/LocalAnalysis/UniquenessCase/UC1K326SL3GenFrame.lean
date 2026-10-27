module

public import CFSG.LocalAnalysis.UniquenessCase.UC1K326SL3GenMatrix

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326

open Matrix
open CFSG.RankThree.PartTwo.Sec15.KSL3Two (IsMonomialWith)

namespace SL3G

section Frame

variable {K : Type} [Field K]

private theorem cube_roots_pairwise {ε : Fin 3 → K} (h3 : ∀ i, ε i ^ 3 = 1)
    (hprod : ε 0 * ε 1 * ε 2 = 1) (hnc : ∃ i j, ε i ≠ ε j) :
    ε 0 ≠ ε 1 ∧ ε 0 ≠ ε 2 ∧ ε 1 ≠ ε 2 := by
  obtain ⟨i0, j0, hij0⟩ := hnc
  have hnot : ¬ (ε 0 = ε 1 ∧ ε 1 = ε 2) := by
    rintro ⟨h01, h12⟩
    apply hij0
    fin_cases i0 <;> fin_cases j0 <;> simp_all
  have hne0 : ∀ i, ε i ≠ 0 := by
    intro i h
    have := h3 i
    rw [h] at this
    simp at this
  have key : ∀ x y : K, x ≠ 0 → x ^ 3 = 1 → x * x * y = 1 → y = x := by
    intro x y hx hx3 hxy
    have : x * x * y = x * x * x :=
      calc x * x * y = 1 := hxy
        _ = x ^ 3 := hx3.symm
        _ = x * x * x := by ring
    exact mul_left_cancel₀ (mul_ne_zero hx hx) this
  refine ⟨?_, ?_, ?_⟩
  · intro h
    apply hnot
    refine ⟨h, ?_⟩
    have := key (ε 0) (ε 2) (hne0 0) (h3 0) (by rw [← h] at hprod; exact hprod)
    rw [this, h]
  · intro h
    apply hnot
    have := key (ε 0) (ε 1) (hne0 0) (h3 0) (by rw [← h] at hprod; linear_combination hprod)
    exact ⟨this.symm, by rw [this, h]⟩
  · intro h
    apply hnot
    have := key (ε 1) (ε 0) (hne0 1) (h3 1) (by rw [h] at hprod ⊢; linear_combination hprod)
    exact ⟨this, h⟩

private theorem cube_roots_distinct {ε : Fin 3 → K} (h3 : ∀ i, ε i ^ 3 = 1)
    (hprod : ε 0 * ε 1 * ε 2 = 1) (hnc : ∃ i j, ε i ≠ ε j) :
    Function.Injective ε ∧ ∃ j, ε j = 1 := by
  obtain ⟨h01, h02, h12⟩ := cube_roots_pairwise h3 hprod hnc
  have hinj : Function.Injective ε := by
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all
  refine ⟨hinj, ?_⟩
  by_contra hne
  push Not at hne
  have hroot : ∀ i, ε i ^ 2 + ε i + 1 = 0 := by
    intro i
    have h := h3 i
    have : (ε i - 1) * (ε i ^ 2 + ε i + 1) = 0 := by linear_combination h
    rcases mul_eq_zero.mp this with h0 | h0
    · exact absurd (sub_eq_zero.mp h0) (hne i)
    · exact h0
  have e1 : ε 0 + ε 1 + 1 = 0 := by
    have : (ε 0 - ε 1) * (ε 0 + ε 1 + 1) = 0 := by
      linear_combination hroot 0 - hroot 1
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) h01
    · exact h
  have e2 : ε 0 + ε 2 + 1 = 0 := by
    have : (ε 0 - ε 2) * (ε 0 + ε 2 + 1) = 0 := by
      linear_combination hroot 0 - hroot 2
    rcases mul_eq_zero.mp this with h | h
    · exact absurd (sub_eq_zero.mp h) h02
    · exact h
  exact h12 (by linear_combination e1 - e2)

private theorem diag_entries_conditions {u θ : GL (Fin 3) K} {M : Matrix (Fin 3) (Fin 3) K}
    {ε : Fin 3 → K} (hMd : M = diagonal ε)
    (hM : M = ((θ⁻¹ * u * θ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)) (hu3 : u ^ 3 = 1)
    (hdet : (u : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hnsc : ∀ c : K, (u : Matrix (Fin 3) (Fin 3) K) ≠ c • 1) :
    (∀ i, ε i ^ 3 = 1) ∧ ε 0 * ε 1 * ε 2 = 1 ∧ ∃ i j, ε i ≠ ε j := by
  have hcube : ∀ i, ε i ^ 3 = 1 := by
    intro i
    have h3 : (θ⁻¹ * u * θ) ^ 3 = 1 := by
      have := conj_pow (a := θ⁻¹) (b := u) (i := 3)
      rw [inv_inv] at this; rw [this, hu3]
      group
    have h3' := congrArg (fun g : GL (Fin 3) K => ((g : Matrix (Fin 3) (Fin 3) K))) h3
    simp only [Units.val_pow_eq_pow_val, Units.val_one] at h3'
    rw [← hM] at h3'; rw [hMd, Matrix.diagonal_pow] at h3'
    have := congrFun (congrFun h3' i) i
    simpa using this
  have hprod : ε 0 * ε 1 * ε 2 = 1 := by
    have hd : M.det = 1 := by
      rw [hM, Units.val_mul, Units.val_mul]
      rw [Matrix.det_units_conj']
      exact hdet
    rw [hMd, Matrix.det_diagonal, Fin.prod_univ_three] at hd
    exact hd
  have hnc : ∃ i j, ε i ≠ ε j := by
    by_contra hall
    push Not at hall
    have hMc : M = ε 0 • (1 : Matrix (Fin 3) (Fin 3) K) := by
      rw [hMd]
      ext i j
      by_cases hij : i = j
      · subst hij
        simp [hall i 0]
      · simp [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
    apply hnsc (ε 0)
    have e : (u : Matrix (Fin 3) (Fin 3) K) =
        ((θ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * M *
          ((θ⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [hM, ← Units.val_mul, ← Units.val_mul]
      congr 1
      group
    rw [e, hMc, Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_one, ← Units.val_mul,
      mul_inv_cancel, Units.val_one]
  exact ⟨hcube, hprod, hnc⟩

theorem diag_eigenvalues {u θ : GL (Fin 3) K}
    (hθ : ((θ⁻¹ * u * θ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag)
    (hu3 : u ^ 3 = 1) (hdet : (u : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hnsc : ∀ c : K, (u : Matrix (Fin 3) (Fin 3) K) ≠ c • 1) :
    ∃ ε : Fin 3 → K, ((θ⁻¹ * u * θ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ε ∧
      Function.Injective ε ∧ ∃ j, ε j = 1 := by
  set M : Matrix (Fin 3) (Fin 3) K := ((θ⁻¹ * u * θ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    with hM
  set ε : Fin 3 → K := M.diag with hε
  have hMd : M = diagonal ε := hθ.diagonal_diag.symm
  obtain ⟨hcube, hprod, hnc⟩ := diag_entries_conditions hMd hM hu3 hdet hnsc
  obtain ⟨hinj, hone⟩ := cube_roots_distinct hcube hprod hnc
  exact ⟨ε, hMd, hinj, hone⟩

theorem frame_of_diag (T Q : Subgroup (GL (Fin 3) K))
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) (hQn : ∀ s ∈ T, ∀ x ∈ Q, s * x * s⁻¹ ∈ Q)
    {u θ : GL (Fin 3) K} (hu : u ∈ Q) {ε : Fin 3 → K}
    (hθ : ((θ⁻¹ * u * θ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal ε)
    (hε : Function.Injective ε) (hε1 : ∃ j, ε j = 1) : IsFrame T Q u θ ε := by
  have hdiag : ∀ x ∈ Q, ((θ⁻¹ * x * θ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).IsDiag := by
    intro x hx
    refine TauCeti.isDiag_of_commute_diagonal hε ?_
    rw [← hθ]
    show ((θ⁻¹ * u * θ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((θ⁻¹ * x * θ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ((θ⁻¹ * x * θ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      ((θ⁻¹ * u * θ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
    rw [← Units.val_mul, ← Units.val_mul]
    congr 1
    calc θ⁻¹ * u * θ * (θ⁻¹ * x * θ) = θ⁻¹ * (u * x) * θ := by group
      _ = θ⁻¹ * (x * u) * θ := by rw [hQab u hu x hx]
      _ = θ⁻¹ * x * θ * (θ⁻¹ * u * θ) := by group
  refine ⟨hθ, hε, hε1, hdiag, ?_⟩
  intro s hs
  let H : Subgroup (GL (Fin 3) K) := Q.comap (MulAut.conj θ).toMonoidHom
  have hmemH : ∀ v : GL (Fin 3) K, v ∈ H ↔ θ * v * θ⁻¹ ∈ Q := fun v => Iff.rfl
  have hHdiag : ∀ v ∈ H, (v : Matrix (Fin 3) (Fin 3) K).IsDiag := by
    intro v hv
    have := hdiag _ ((hmemH v).mp hv)
    have e : θ⁻¹ * (θ * v * θ⁻¹) * θ = v := by group
    rwa [e] at this
  have hu' : θ⁻¹ * u * θ ∈ H := by
    rw [hmemH]
    have e : θ * (θ⁻¹ * u * θ) * θ⁻¹ = u := by group
    rwa [e]
  have hsep : ∀ i j : Fin 3, i ≠ j →
      ∃ v ∈ H, (v : Matrix (Fin 3) (Fin 3) K) i i ≠ (v : Matrix (Fin 3) (Fin 3) K) j j := by
    intro i j hij
    refine ⟨_, hu', ?_⟩
    rw [hθ, diagonal_apply_eq, diagonal_apply_eq]
    exact hε.ne hij
  have hG : ∀ v ∈ H, (θ⁻¹ * s * θ)⁻¹ * v * (θ⁻¹ * s * θ) ∈ H := by
    intro v hv
    rw [hmemH] at hv ⊢
    have e : θ * ((θ⁻¹ * s * θ)⁻¹ * v * (θ⁻¹ * s * θ)) * θ⁻¹ =
        s⁻¹ * (θ * v * θ⁻¹) * (s⁻¹)⁻¹ := by group
    rw [e]
    exact hQn s⁻¹ (inv_mem hs) _ hv
  exact CFSG.RankThree.PartTwo.Sec15.KSL3Two.exists_monomial_of_normalizes hHdiag hsep hG

theorem frame_exists {ω : K} (hω : IsPrimitiveRoot ω 3) (T Q : Subgroup (GL (Fin 3) K))
    (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x) (hQn : ∀ s ∈ T, ∀ x ∈ Q, s * x * s⁻¹ ∈ Q)
    {u : GL (Fin 3) K} (hu : u ∈ Q) (hu3 : u ^ 3 = 1)
    (hdet : (u : Matrix (Fin 3) (Fin 3) K).det = 1)
    (hnsc : ∀ c : K, (u : Matrix (Fin 3) (Fin 3) K) ≠ c • 1) :
    ∃ (θ : GL (Fin 3) K) (ε : Fin 3 → K), IsFrame T Q u θ ε := by
  haveI : NeZero ((3 : ℕ) : K) := hω.neZero'
  have hu3' : (u : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hu3, Units.val_one]
  obtain ⟨Q₀, hQ₀, α, β, hα, -⟩ :=
    CFSG.RankThree.PartTwo.Sec15.KSL3Two.exists_conj_diag (NeZero.ne ((3 : ℕ) : K)) hω hu3' hu3'
      (Commute.refl _)
  let θ : GL (Fin 3) K := hQ₀.unit
  have hθ : ((θ⁻¹ * u * θ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = diagonal α := by
    rw [Units.val_mul, Units.val_mul]
    have h1 : ((θ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = Q₀ := rfl
    rw [h1, Matrix.mul_assoc, hα, ← Matrix.mul_assoc, ← h1, ← Units.val_mul, inv_mul_cancel,
      Units.val_one, Matrix.one_mul]
  obtain ⟨ε, hε, hinj, hone⟩ := diag_eigenvalues (by rw [hθ]; exact isDiag_diagonal α) hu3 hdet hnsc
  exact ⟨θ, ε, frame_of_diag T Q hQab hQn hu hε hinj hone⟩

end Frame

end SL3G

end CFSG.LocalAnalysis.UniquenessCase.UC22.InS3.UC326
