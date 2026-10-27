module

public import CFSG.LocalAnalysis.StandardType.GGBstarLIDUnitFieldIso

public section

namespace CFSG.StandardType

namespace LIDUF

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.HardMathSupport.Foote.ModuleExclusions

variable {K : Type} [Field K] {d n : ℕ}

theorem exists_eigen_isotropic (h : UnitaryFieldData 2 n K) [Finite K]
    (hK : Nat.card K = (2 ^ n) ^ 2) (hn : 1 ≤ n) {p : ℕ} (hp : p.Prime) {φ : K ≃+* K}
    (hφ : orderOf φ = p) (hφb : ∀ x, φ (h.bar x) = h.bar (φ x))
    {B' : Matrix (Fin d) (Fin d) K} (hB' : adjM h.bar B' * B' = 1) {c₀ : K}
    (hc₀ : c₀ ^ (2 ^ n + 1) = 1) (hN : Ai φ B' p = c₀ • (1 : Matrix (Fin d) (Fin d) K))
    (W : Set (Fin d → K)) {i j : Fin d} (hij : i ≠ j) (hWij : ∀ σ ∈ W, σ i = σ j)
    (hcomm : ∀ σ ∈ W, B' * Matrix.diagonal σ = Matrix.diagonal σ * B') :
    ∃ v : Fin d → K, v ≠ 0 ∧ herm h.bar v v = 0 ∧
      (∀ σ ∈ W, Matrix.diagonal σ *ᵥ v = σ i • v) ∧
      ∃ μ : K, μ ^ (2 ^ n + 1) = 1 ∧ B' *ᵥ (fun k => φ (v k)) = μ • v := by
  classical
  have hφp : φ ^ p = 1 := by rw [← hφ]; exact pow_orderOf_eq_one φ
  have hp0 : 0 < p := hp.pos
  have hc₀0 : c₀ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hc₀
    exact zero_ne_one hc₀
  have hB'0 : B' ≠ 0 := by
    rintro rfl
    have := congrFun (congrFun hB' i) i
    simp [adjM] at this
  have hφc₀ : φ c₀ = c₀ := by
    have h1 : Ai φ B' (p + 1) = φ c₀ • B' := by
      have h0 : Ai φ B' (p + 1) = B' * (Ai φ B' p).map φ := rfl
      rw [h0, hN]
      ext k l
      simp [Matrix.mul_apply, Matrix.map_apply, Matrix.smul_apply, Matrix.one_apply,
        apply_ite φ, mul_ite, mul_comm]
    have h2 : Ai φ B' (p + 1) = c₀ • B' := by
      rw [Ai_succ_right, hN, hφp]
      ext k l
      simp [Matrix.mul_apply, Matrix.smul_apply, Matrix.one_apply, Matrix.map_apply]
    rw [h1] at h2
    by_contra hne
    have hdiff : φ c₀ - c₀ ≠ 0 := sub_ne_zero.mpr hne
    apply hB'0
    ext k l
    have := congrFun (congrFun h2 k) l
    simp only [Matrix.smul_apply, smul_eq_mul] at this
    have h3 : (φ c₀ - c₀) * B' k l = 0 := by linear_combination this
    simpa [hdiff] using h3
  obtain ⟨ρ, hρq, hρ⟩ := exists_unitary_normalizer hK hn hφ (τ := c₀⁻¹)
    (by rw [inv_pow, hc₀, inv_one]) (by rw [map_inv₀, hφc₀])
  have hρ0 : ρ ≠ 0 := by
    rintro rfl
    rw [zero_pow (by positivity)] at hρq
    exact zero_ne_one hρq
  set A : Matrix (Fin d) (Fin d) K := ρ • B' with hA
  have hAi : Ai φ A p = 1 := by
    rw [hA, Ai_smul, hρ, hN, smul_smul, inv_mul_cancel₀ hc₀0, one_smul]
  have hbρ : h.bar ρ * ρ = 1 := by rw [h.bar_apply, ← pow_succ]; exact hρq
  have hAu : adjM h.bar A * A = 1 := by
    rw [hA, adjM_smul, Matrix.smul_mul, Matrix.mul_smul, smul_smul, hB', hbρ, one_smul]
  obtain ⟨G, hGdet, hG⟩ := speiser φ A p hφ hp0 hAi
  have hGfix : ∀ k a, ∑ l, A k l * φ (G l a) = G k a := fun k a => by
    have := congrFun (congrFun hG k) a
    simpa [Matrix.mul_apply, Matrix.map_apply] using this
  set cls : Fin d → Prop := fun k => ∀ σ ∈ W, σ k = σ i with hcls
  have hclsi : cls i := fun σ _ => rfl
  have hclsj : cls j := fun σ hσ => (hWij σ hσ).symm
  have hblk : ∀ k l, B' k l ≠ 0 → (cls k ↔ cls l) := by
    intro k l hkl
    have hσkl : ∀ σ ∈ W, σ k = σ l := by
      intro σ hσ
      have h1 := congrFun (congrFun (hcomm σ hσ) k) l
      simp only [Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
      exact (mul_left_cancel₀ hkl (h1.trans (mul_comm _ _))).symm
    constructor
    · intro hk σ hσ
      rw [← hσkl σ hσ]
      exact hk σ hσ
    · intro hl σ hσ
      rw [hσkl σ hσ]
      exact hl σ hσ
  have hAkl : ∀ k l, B' k l = 0 → A k l = 0 := fun k l h0 => by simp [hA, h0]
  set y : Fin d → Fin d → K := fun a k => if cls k then G k a else 0 with hy
  have hyfix : ∀ a, semF (φ : K →+* K) A (y a) = y a := by
    intro a
    funext k
    simp only [semF, Matrix.mulVec, dotProduct, hy]
    by_cases hk : cls k
    · rw [if_pos hk, ← hGfix k a]
      refine Finset.sum_congr rfl fun l _ => ?_
      by_cases hl : cls l
      · simp [hl]
      · have : B' k l = 0 := by
          by_contra hne
          exact hl ((hblk k l hne).1 hk)
        simp [hl, hAkl k l this]
    · rw [if_neg hk]
      refine Finset.sum_eq_zero fun l _ => ?_
      by_cases hl : cls l
      · have : B' k l = 0 := by
          by_contra hne
          exact hk ((hblk k l hne).2 hl)
        simp [hAkl k l this]
      · simp [hl]
  obtain ⟨a, ha⟩ : ∃ a, G i a ≠ 0 := by
    by_contra hcon
    push Not at hcon
    exact hGdet (Matrix.det_eq_zero_of_row_eq_zero i hcon)
  obtain ⟨b, hb⟩ : ∃ b, G i a * G j b ≠ G j a * G i b := by
    by_contra hcon
    push Not at hcon
    apply hGdet
    rw [← Matrix.exists_vecMul_eq_zero_iff]
    refine ⟨Pi.single j (G i a) - Pi.single i (G j a), ?_, ?_⟩
    · intro h0
      have := congrFun h0 j
      simp [Pi.single_apply, hij.symm] at this
      exact ha this
    · funext c
      simp only [Matrix.vecMul, dotProduct, Pi.sub_apply, sub_mul, Finset.sum_sub_distrib,
        Pi.single_apply, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true,
        Pi.zero_apply]
      rw [hcon c]
      ring
  have hyi : ∀ c, y c i = G i c := fun c => by simp [hy, hclsi]
  have hyj : ∀ c, y c j = G j c := fun c => by simp [hy, hclsj]
  obtain ⟨v, hv0, hvF, hviso, s, t, hvst⟩ := exists_fixed_isotropic h hK hn hp hφ hφb hAu
    (hyfix a) (hyfix b) (i := i) (j := j) (by rw [hyi, hyj, hyj, hyi]; exact hb)
  have hvsupp : ∀ k, ¬ cls k → v k = 0 := fun k hk => by
    rw [hvst]
    simp [hy, hk]
  refine ⟨v, hv0, hviso, ?_, ρ⁻¹, ?_, ?_⟩
  · intro σ hσ
    funext k
    simp only [Matrix.mulVec_diagonal, Pi.smul_apply, smul_eq_mul]
    by_cases hk : cls k
    · rw [hk σ hσ]
    · rw [hvsupp k hk]
      simp
  · rw [inv_pow, hρq, inv_one]
  · have h1 : A *ᵥ (fun k => φ (v k)) = v := hvF
    have h2 : ρ • (B' *ᵥ (fun k => φ (v k))) = v := by
      have h3 := h1
      rw [hA, Matrix.smul_mulVec] at h3
      exact h3
    calc B' *ᵥ (fun k => φ (v k)) = ρ⁻¹ • (ρ • (B' *ᵥ (fun k => φ (v k)))) := by
          rw [smul_smul, inv_mul_cancel₀ hρ0, one_smul]
      _ = ρ⁻¹ • v := by rw [h2]

end LIDUF

end CFSG.StandardType

end
