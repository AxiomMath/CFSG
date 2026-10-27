module

public import CFSG.RankThree.PartOne.AUTSL.Interface
public import CFSG.RankThree.PartOne.AUTSL.FieldExt

public section

namespace CFSG.RankThree.PartOne.AUTSL

section Ring

variable {R : Type*} [Ring R]

theorem conj_rel_zero (σ : R →+* R) (P Pi C Ci G : R) (hPiP : Pi * P = 1) (hCiC : Ci * C = 1) :
    P * (C * σ G * Ci) * Pi * (P * C * σ Pi) = (P * C * σ Pi) * σ (P * G * Pi) := by
  have h1 : σ Pi * σ P = 1 := by rw [← map_mul, hPiP, map_one]
  calc P * (C * σ G * Ci) * Pi * (P * C * σ Pi)
      = P * C * σ G * (Ci * (Pi * P) * C) * σ Pi := by noncomm_ring
    _ = P * C * σ G * σ Pi := by rw [hPiP, mul_one, hCiC, mul_one]
    _ = (P * C * σ Pi) * σ (P * G * Pi) := by
        rw [map_mul, map_mul]
        calc P * C * σ G * σ Pi = P * C * (σ Pi * σ P) * σ G * σ Pi := by rw [h1, mul_one]
          _ = _ := by noncomm_ring

theorem conj_rel_one (σ : R →+* R) (P Pi C Ci Pt Pit Yinv Ht : R) (hPiP : Pi * P = 1)
    (hCiC : Ci * C = 1) (hPt : Pit * Pt = 1) (hH : Ht = Pt * Yinv * Pit) :
    P * (C * σ Ht * Ci) * Pi * (P * C * σ Pt) = (P * C * σ Pt) * σ Yinv := by
  have h1 : σ Pit * σ Pt = 1 := by rw [← map_mul, hPt, map_one]
  rw [hH, map_mul, map_mul]
  calc P * (C * (σ Pt * σ Yinv * σ Pit) * Ci) * Pi * (P * C * σ Pt)
      = P * C * σ Pt * σ Yinv * σ Pit * (Ci * (Pi * P) * C) * σ Pt := by noncomm_ring
    _ = P * C * σ Pt * σ Yinv * (σ Pit * σ Pt) := by
        rw [hPiP, mul_one, hCiC, mul_one]
        noncomm_ring
    _ = (P * C * σ Pt) * σ Yinv := by rw [h1, mul_one]

end Ring

section Relation

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

variable {K K' : Type*} [Field K] [Finite K] [CharP K 2] [Field K'] [CharP K' 2] [Algebra K K']
  {n : ℕ}

theorem exists_semilinear_relation (hn : 3 ≤ n) (β : MulAut (SpecialLinearGroup (Fin n) K))
    (P : GL (Fin n) K') :
    ∃ (j : ℕ) (A₃ : Matrix (Fin n) (Fin n) K'), IsUnit A₃ ∧
      ((∀ (g : SpecialLinearGroup (Fin n) K) (d : Fin n → K'),
          (P : Matrix (Fin n) (Fin n) K') *
            (g : Matrix (Fin n) (Fin n) K).map (algebraMap K K') *
            ((P⁻¹ : GL (Fin n) K') : Matrix (Fin n) (Fin n) K') = Matrix.diagonal d →
          (P : Matrix (Fin n) (Fin n) K') *
            (β g : Matrix (Fin n) (Fin n) K).map (algebraMap K K') *
            ((P⁻¹ : GL (Fin n) K') : Matrix (Fin n) (Fin n) K') * A₃ =
            A₃ * Matrix.diagonal (fun i => d i ^ 2 ^ j)) ∨
       (∀ (g : SpecialLinearGroup (Fin n) K) (d : Fin n → K'),
          (P : Matrix (Fin n) (Fin n) K') *
            (g : Matrix (Fin n) (Fin n) K).map (algebraMap K K') *
            ((P⁻¹ : GL (Fin n) K') : Matrix (Fin n) (Fin n) K') = Matrix.diagonal d →
          (P : Matrix (Fin n) (Fin n) K') *
            (β g : Matrix (Fin n) (Fin n) K).map (algebraMap K K') *
            ((P⁻¹ : GL (Fin n) K') : Matrix (Fin n) (Fin n) K') * A₃ =
            A₃ * Matrix.diagonal (fun i => (d i)⁻¹ ^ 2 ^ j))) := by
  obtain ⟨A, σ, hA⟩ := exists_matrix_form_of_mulAut_sl hn β
  obtain ⟨j, hj⟩ := exists_ringEquiv_eq_pow_two σ
  have : ExpChar K' 2 := ExpChar.prime Nat.prime_two
  let ι : K →+* K' := algebraMap K K'
  let σ' : K' →+* K' := iterateFrobenius K' 2 j
  have hσ' : ∀ x, σ' x = x ^ 2 ^ j := iterateFrobenius_def 2 j
  have hσσ' : ∀ x : K, σ' (ι x) = ι (σ x) := fun x => by
    rw [hσ', hj x, map_pow]
  let ιM : Matrix (Fin n) (Fin n) K →+* Matrix (Fin n) (Fin n) K' := ι.mapMatrix
  let σM : Matrix (Fin n) (Fin n) K' →+* Matrix (Fin n) (Fin n) K' := σ'.mapMatrix
  have hιM : ∀ M : Matrix (Fin n) (Fin n) K, ιM M = M.map (algebraMap K K') := fun M => rfl
  have hσM : ∀ M : Matrix (Fin n) (Fin n) K', σM M = M.map σ' := fun M => rfl
  have hcomm : ∀ M : Matrix (Fin n) (Fin n) K, ιM (M.map σ) = σM (ιM M) := fun M => by
    ext i k
    exact (hσσ' _).symm
  set Pm : Matrix (Fin n) (Fin n) K' := (P : Matrix (Fin n) (Fin n) K') with hPm
  set Pi : Matrix (Fin n) (Fin n) K' := ((P⁻¹ : GL (Fin n) K') : Matrix (Fin n) (Fin n) K')
    with hPi
  have hPPi : Pm * Pi = 1 := Units.mul_inv P
  have hPiP : Pi * Pm = 1 := Units.inv_mul P
  set C : Matrix (Fin n) (Fin n) K' := ιM (A : Matrix (Fin n) (Fin n) K) with hC
  set Ci : Matrix (Fin n) (Fin n) K' := ιM ((A⁻¹ : GL (Fin n) K) : Matrix (Fin n) (Fin n) K)
    with hCi
  have hCiC : Ci * C = 1 := by
    rw [hC, hCi, ← map_mul, Units.inv_mul, map_one]
  have hCCi : C * Ci = 1 := by
    rw [hC, hCi, ← map_mul, Units.mul_inv, map_one]
  have hCunit : IsUnit C := ⟨⟨C, Ci, hCCi, hCiC⟩, rfl⟩
  rcases hA with hA | hA
  ·
    refine ⟨j, Pm * C * σM Pi, ?_, Or.inl fun g d hd => ?_⟩
    · have hPu : IsUnit Pm := P.isUnit
      have hPiu : IsUnit (σM Pi) := by
        refine ⟨⟨σM Pi, σM Pm, ?_, ?_⟩, rfl⟩
        · rw [← map_mul, hPiP, map_one]
        · rw [← map_mul, hPPi, map_one]
      exact (hPu.mul hCunit).mul hPiu
    · have hβ : ιM (β g : Matrix (Fin n) (Fin n) K) =
          C * σM (ιM (g : Matrix (Fin n) (Fin n) K)) * Ci := by
        rw [hA g, map_mul, map_mul, hcomm]
      have hd' : Matrix.diagonal (fun i => d i ^ 2 ^ j) =
          σM (Pm * ιM (g : Matrix (Fin n) (Fin n) K) * Pi) := by
        have : Pm * ιM (g : Matrix (Fin n) (Fin n) K) * Pi = Matrix.diagonal d := hd
        rw [this, hσM, Matrix.diagonal_map (map_zero σ')]
        simp only [hσ']
      show Pm * ιM (β g : Matrix (Fin n) (Fin n) K) * Pi * (Pm * C * σM Pi) = _
      rw [hβ, hd']
      exact conj_rel_zero σM Pm Pi C Ci _ hPiP hCiC
  ·
    set Pt : Matrix (Fin n) (Fin n) K' := Pm.transpose with hPt
    set Pit : Matrix (Fin n) (Fin n) K' := Pi.transpose with hPit
    have hPtPit : Pit * Pt = 1 := by
      rw [hPt, hPit, ← Matrix.transpose_mul, hPPi, Matrix.transpose_one]
    have hPitPt : Pt * Pit = 1 := by
      rw [hPt, hPit, ← Matrix.transpose_mul, hPiP, Matrix.transpose_one]
    refine ⟨j, Pm * C * σM Pt, ?_, Or.inr fun g d hd => ?_⟩
    · have hPu : IsUnit Pm := P.isUnit
      have hPtu : IsUnit (σM Pt) := by
        refine ⟨⟨σM Pt, σM Pit, ?_, ?_⟩, rfl⟩
        · rw [← map_mul, hPitPt, map_one]
        · rw [← map_mul, hPtPit, map_one]
      exact (hPu.mul hCunit).mul hPtu
    · set G : Matrix (Fin n) (Fin n) K := (g : Matrix (Fin n) (Fin n) K) with hG
      set H : Matrix (Fin n) (Fin n) K := ((g⁻¹ : SpecialLinearGroup (Fin n) K) :
        Matrix (Fin n) (Fin n) K) with hH
      have hGH : G * H = 1 := by
        rw [hG, hH, ← Matrix.SpecialLinearGroup.coe_mul, mul_inv_cancel,
          Matrix.SpecialLinearGroup.coe_one]
      have hβ : ιM (β g : Matrix (Fin n) (Fin n) K) = C * σM (ιM H).transpose * Ci := by
        rw [hA g, map_mul, map_mul, hcomm]
        congr 3
      have hY : Pm * ιM G * Pi = Matrix.diagonal d := hd
      have hYY : Matrix.diagonal d * (Pm * ιM H * Pi) = 1 := by
        rw [← hY]
        calc Pm * ιM G * Pi * (Pm * ιM H * Pi)
            = Pm * ιM G * (Pi * Pm) * ιM H * Pi := by noncomm_ring
          _ = Pm * ιM (G * H) * Pi := by rw [hPiP, mul_one, map_mul]; noncomm_ring
          _ = 1 := by rw [hGH, map_one, mul_one, hPPi]
      have hYinv : Pm * ιM H * Pi = Matrix.diagonal (fun i => (d i)⁻¹) := by
        have hdiag1 : ∀ i, d i * (Pm * ιM H * Pi) i i = 1 := fun i => by
          have := congrFun (congrFun hYY i) i
          rwa [Matrix.diagonal_mul, Matrix.one_apply_eq] at this
        have hoff : ∀ i k, i ≠ k → d i * (Pm * ιM H * Pi) i k = 0 := fun i k hik => by
          have := congrFun (congrFun hYY i) k
          rwa [Matrix.diagonal_mul, Matrix.one_apply_ne hik] at this
        have hd0 : ∀ i, d i ≠ 0 := fun i h0 => by
          have := hdiag1 i
          rw [h0, zero_mul] at this
          exact zero_ne_one this
        ext i k
        by_cases hik : i = k
        · subst hik
          rw [Matrix.diagonal_apply_eq]
          exact eq_inv_of_mul_eq_one_right (hdiag1 i)
        · rw [Matrix.diagonal_apply_ne _ hik]
          exact (mul_eq_zero.1 (hoff i k hik)).resolve_left (hd0 i)
      have hHt : (ιM H).transpose = Pt * Matrix.diagonal (fun i => (d i)⁻¹) * Pit := by
        have h1 : ιM H = Pi * (Pm * ιM H * Pi) * Pm := by
          calc ιM H = (Pi * Pm) * ιM H * (Pi * Pm) := by rw [hPiP, one_mul, mul_one]
            _ = _ := by noncomm_ring
        conv_lhs => rw [h1, hYinv]
        rw [Matrix.transpose_mul, Matrix.transpose_mul, Matrix.diagonal_transpose]
        simp only [hPt, hPit, Matrix.mul_assoc]
      have hdiag : Matrix.diagonal (fun i => (d i)⁻¹ ^ 2 ^ j) =
          σM (Matrix.diagonal (fun i => (d i)⁻¹)) := by
        rw [hσM, Matrix.diagonal_map (map_zero σ')]
        simp only [hσ']
      rw [hdiag]
      show Pm * ιM (β g : Matrix (Fin n) (Fin n) K) * Pi * (Pm * C * σM Pt) = _
      rw [hβ]
      exact conj_rel_one σM Pm Pi C Ci Pt Pit _ _ hPiP hCiC hPtPit hHt

end Relation

end CFSG.RankThree.PartOne.AUTSL
