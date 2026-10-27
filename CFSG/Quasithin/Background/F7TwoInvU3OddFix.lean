module

public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSemilinearInvolution
public import CFSG.GH74.GLS.Stage2.Bender.Thm1.P67U3Coord

public section

namespace CFSG.Quasithin.F7Two.U3Odd

open Matrix CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher CFSG.GH74.GLS.Stage2.Bender.Thm1
open scoped Pointwise

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K)

@[expose] def u3oVecE : HypIndex 1 1 → K := Pi.single (.inl 0) 1

@[expose] def u3oVecF : HypIndex 1 1 → K := Pi.single (.inr (.inr 0)) 1

theorem hypForm_u3oVecE_left (v : HypIndex 1 1 → K) :
    hypForm h 1 1 u3oVecE v = v (.inr (.inr 0)) :=
  hypForm_single_inl h 0 v

theorem hypForm_u3oVecE_u3oVecE : hypForm h 1 1 (u3oVecE : HypIndex 1 1 → K) u3oVecE = 0 := by
  rw [hypForm_u3oVecE_left]
  simp [u3oVecE]

theorem hypForm_u3oVecE_u3oVecF : hypForm h 1 1 (u3oVecE : HypIndex 1 1 → K) u3oVecF = 1 := by
  rw [hypForm_u3oVecE_left]
  simp [u3oVecF]

theorem hypForm_u3oVecF_u3oVecF : hypForm h 1 1 (u3oVecF : HypIndex 1 1 → K) u3oVecF = 0 := by
  simp [hypForm_apply, Fintype.sum_sum_type, u3oVecF]

variable {h}

theorem mulVec_u3oVecE_apply (M : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (i : HypIndex 1 1) :
    (M *ᵥ u3oVecE) i = M i (.inl 0) := by
  rw [u3oVecE, mulVec_single_one, col_apply]

theorem mulVec_u3oVecF_apply (M : Matrix (HypIndex 1 1) (HypIndex 1 1) K) (i : HypIndex 1 1) :
    (M *ᵥ u3oVecF) i = M i (.inr (.inr 0)) := by
  rw [u3oVecF, mulVec_single_one, col_apply]

theorem diagonal_of_isometry_stable {D : Matrix (HypIndex 1 1) (HypIndex 1 1) K}
    (hD : (D.map h.bar)ᵀ * hypGram 1 1 K * D = hypGram 1 1 K) {κ₁ κ₃ : K}
    (he : D *ᵥ u3oVecE = κ₁ • u3oVecE) (hf : D *ᵥ u3oVecF = κ₃ • u3oVecF) :
    ∃ d, D = diagonal d := by
  have hDe : ∀ i, D i (.inl 0) = κ₁ * (u3oVecE : HypIndex 1 1 → K) i := fun i => by
    have := congrFun he i
    rwa [mulVec_u3oVecE_apply, Pi.smul_apply, smul_eq_mul] at this
  have hDf : ∀ i, D i (.inr (.inr 0)) = κ₃ * (u3oVecF : HypIndex 1 1 → K) i := fun i => by
    have := congrFun hf i
    rwa [mulVec_u3oVecF_apply, Pi.smul_apply, smul_eq_mul] at this
  have hee : D (.inl 0) (.inl 0) = κ₁ := by simpa [u3oVecE] using hDe (.inl 0)
  have hze : D (.inr (.inl 0)) (.inl 0) = 0 := by simpa [u3oVecE] using hDe (.inr (.inl 0))
  have hfe : D (.inr (.inr 0)) (.inl 0) = 0 := by simpa [u3oVecE] using hDe (.inr (.inr 0))
  have hef : D (.inl 0) (.inr (.inr 0)) = 0 := by simpa [u3oVecF] using hDf (.inl 0)
  have hzf : D (.inr (.inl 0)) (.inr (.inr 0)) = 0 := by simpa [u3oVecF] using hDf (.inr (.inl 0))
  have hff : D (.inr (.inr 0)) (.inr (.inr 0)) = κ₃ := by simpa [u3oVecF] using hDf (.inr (.inr 0))
  have h1 := congrFun (congrFun hD (.inl 0)) (.inr (.inr 0))
  have h2 := congrFun (congrFun hD (.inl 0)) (.inr (.inl 0))
  have h3 := congrFun (congrFun hD (.inr (.inr 0))) (.inr (.inl 0))
  simp [Matrix.mul_apply, Fintype.sum_sum_type, hee, hze, hfe, hef, hzf, hff] at h1 h2 h3
  have hκ₁ : κ₁ ≠ 0 := fun h0 => by rw [h0, map_zero, zero_mul] at h1; exact zero_ne_one h1
  have hκ₃ : κ₃ ≠ 0 := fun h0 => by rw [h0, mul_zero] at h1; exact zero_ne_one h1
  have hfz : D (.inr (.inr 0)) (.inr (.inl 0)) = 0 := h2.resolve_left hκ₁
  have hez : D (.inl 0) (.inr (.inl 0)) = 0 := h3.resolve_left hκ₃
  refine ⟨fun i => D i i, ?_⟩
  refine u3_hyp3_matrix_ext ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ ?_ <;>
    simp [hee, hze, hfe, hef, hzf, hff, hfz, hez]

theorem conj_mulVec_of_stable {A P : GL (HypIndex 1 1) K} (σ : K ≃+* K)
    {x a : HypIndex 1 1 → K} (hx : (fun i => σ (x i)) = x) {s l : K} (hs : s ≠ 0)
    (hPx : (P : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ x = s • a)
    (hAa : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ (fun i => σ (a i)) = l • a) :
    ((P⁻¹ * A * glAut σ P : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ x =
      (σ s * l * s⁻¹) • x := by
  have h1 : ((P : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map σ) *ᵥ x =
      σ s • (fun i => σ (a i)) := by
    funext i
    have hx' : ∀ j, σ (x j) = x j := fun j => congrFun hx j
    have h2 : (((P : Matrix (HypIndex 1 1) (HypIndex 1 1) K).map σ) *ᵥ x) i =
        σ (((P : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ x) i) := by
      simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, map_sum, map_mul]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hx' j]
    rw [h2, hPx]
    simp
  have hPxinv : ((P⁻¹ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
      ((P : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ x) = x := by
    rw [mulVec_mulVec, ← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec]
  have hPa : ((P⁻¹ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ a =
      s⁻¹ • x := by
    calc ((P⁻¹ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ a
        = ((P⁻¹ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
            (s⁻¹ • s • a) := by rw [smul_smul, inv_mul_cancel₀ hs, one_smul]
      _ = s⁻¹ • (((P⁻¹ : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
            (s • a)) := by rw [mulVec_smul]
      _ = s⁻¹ • x := by rw [← hPx, hPxinv]
  rw [Units.val_mul, Units.val_mul, ← mulVec_mulVec, ← mulVec_mulVec, coe_glAut, h1, mulVec_smul,
    hAa, smul_smul, mulVec_smul, hPa, smul_smul]

theorem u3oVecE_ne_zero : (u3oVecE : HypIndex 1 1 → K) ≠ 0 := fun h0 => by
  have := congrFun h0 (.inl 0)
  simp [u3oVecE] at this

theorem u3oVecF_ne_zero : (u3oVecF : HypIndex 1 1 → K) ≠ 0 := fun h0 => by
  have := congrFun h0 (.inr (.inr 0))
  simp [u3oVecF] at this

theorem ne_zero_of_mulVec_eq {P : GL (HypIndex 1 1) K} {x a : HypIndex 1 1 → K} {s : K}
    (hx : x ≠ 0) (hPx : (P : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ x = s • a) : s ≠ 0 := by
  rintro rfl
  rw [zero_smul] at hPx
  apply hx
  have h1 := congrArg (fun v => ((P⁻¹ : GL (HypIndex 1 1) K) :
    Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ v) hPx
  simp only [mulVec_mulVec, mulVec_zero] at h1
  rw [← Units.val_mul, inv_mul_cancel, Units.val_one, one_mulVec] at h1
  exact h1

theorem exists_hypSU_diag_of_stable_pair {A : GL (HypIndex 1 1) K} (hA : A ∈ hypUnitary h 1 1)
    (σ : K ≃+* K) {a b : HypIndex 1 1 → K} (haa : hypForm h 1 1 a a = 0)
    (hbb : hypForm h 1 1 b b = 0) (hab : hypForm h 1 1 a b = 1) {l₁ l₃ : K}
    (hla : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ (fun i => σ (a i)) = l₁ • a)
    (hlb : (A : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ (fun i => σ (b i)) = l₃ • b) :
    ∃ (P : hypSU h 1 1) (d : HypIndex 1 1 → K),
      (((P : GL (HypIndex 1 1) K)⁻¹ * A * glAut σ (P : GL (HypIndex 1 1) K) :
        GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) = diagonal d := by
  obtain ⟨g, hg, hga, hgb⟩ := exists_sesqSpecialUnitary_of_hyperbolic h (hypForm_isSymm h)
    (hypForm_separatingLeft h) (hypForm_u3oVecE_u3oVecE (h := h))
    (hypForm_u3oVecF_u3oVecF (h := h)) (hypForm_u3oVecE_u3oVecF (h := h)) haa hbb hab
  obtain ⟨P, hP⟩ := exists_hypSU_of_mem h hg
  have hPe : P • (u3oVecE : HypIndex 1 1 → K) ∈ K ∙ a := by
    have h1 : P • (u3oVecE : HypIndex 1 1 → K) ∈ P • (K ∙ (u3oVecE : HypIndex 1 1 → K)) :=
      Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.mem_span_singleton_self _)
    rw [hP, hga] at h1
    exact h1
  have hPf : P • (u3oVecF : HypIndex 1 1 → K) ∈ K ∙ b := by
    have h1 : P • (u3oVecF : HypIndex 1 1 → K) ∈ P • (K ∙ (u3oVecF : HypIndex 1 1 → K)) :=
      Submodule.smul_mem_pointwise_smul _ _ _ (Submodule.mem_span_singleton_self _)
    rw [hP, hgb] at h1
    exact h1
  obtain ⟨s, hs⟩ := Submodule.mem_span_singleton.mp hPe
  obtain ⟨s', hs'⟩ := Submodule.mem_span_singleton.mp hPf
  have hPE : ((P : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
      u3oVecE = s • a := hs.symm
  have hPF : ((P : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K) *ᵥ
      u3oVecF = s' • b := hs'.symm
  have hxE : (fun i => σ ((u3oVecE : HypIndex 1 1 → K) i)) = u3oVecE := by
    funext i
    by_cases hi : i = .inl 0 <;> simp [u3oVecE, hi]
  have hxF : (fun i => σ ((u3oVecF : HypIndex 1 1 → K) i)) = u3oVecF := by
    funext i
    by_cases hi : i = .inr (.inr 0) <;> simp [u3oVecF, hi]
  have he := conj_mulVec_of_stable (A := A) (P := (P : GL (HypIndex 1 1) K)) σ hxE
    (ne_zero_of_mulVec_eq u3oVecE_ne_zero hPE) hPE hla
  have hf := conj_mulVec_of_stable (A := A) (P := (P : GL (HypIndex 1 1) K)) σ hxF
    (ne_zero_of_mulVec_eq u3oVecF_ne_zero hPF) hPF hlb
  have hPU : (P : GL (HypIndex 1 1) K) ∈ hypUnitary h 1 1 :=
    mem_hypUnitary.mpr (mem_gramSU.mp P.2).1
  have hσP : glAut σ (P : GL (HypIndex 1 1) K) ∈ hypUnitary h 1 1 := by
    rw [mem_hypUnitary, coe_glAut]
    have := map_similitude h (r := 1) (ε := 1)
      (A := ((P : GL (HypIndex 1 1) K) : Matrix (HypIndex 1 1) (HypIndex 1 1) K)) (μ := 1)
      (by rw [one_smul]; exact (mem_gramSU.mp P.2).1) σ
    rwa [map_one, one_smul] at this
  have hD := mem_hypUnitary.mp (mul_mem (mul_mem (inv_mem hPU) hA) hσP)
  obtain ⟨d, hd⟩ := diagonal_of_isometry_stable hD he hf
  exact ⟨P, d, hd⟩

end CFSG.Quasithin.F7Two.U3Odd
