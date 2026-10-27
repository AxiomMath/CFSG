module

public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofSeitz
public import CFSG.RankThree.PartTwo.Sec19.Item19Res6ProofUnitaryMat
public import CFSG.RankThree.PartTwo.Sec19.Item19Res5ProofFaithField
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofTransport

public section

namespace CFSG.RankThree.PartTwo.Sec19

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo

namespace Item19Res6Proof

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open CFSG.RankThree.PartTwo.KFacts
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (glAut coe_glAut)

variable {p f : ℕ} {K : Type} [Field K]

theorem shift_mem_unitarySU (h : UnitaryFieldData p f K) :
    ∃ C : unitarySU p f K 3, ((C : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![0, 0, 1; 1, 0, 0; 0, 1, 0] := by
  set C : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0] with hC
  have hCt : Cᵀ * C = 1 := by
    rw [hC]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hdet : C.det = 1 := by
    rw [hC]
    simp [Matrix.det_fin_three]
  have hdet0 : C.det ≠ 0 := by rw [hdet]; exact one_ne_zero
  refine ⟨⟨GeneralLinearGroup.mkOfDetNeZero C hdet0, ?_⟩, rfl⟩
  refine (mem_unitarySU_iff h).mpr ⟨hdet, ?_⟩
  change (C.map h.bar)ᵀ * C = 1
  have hmap : C.map h.bar = C := by
    rw [hC]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  rw [hmap, hCt]

theorem exists_unitary_twisted_basis (h : UnitaryFieldData p f K) (hQ : p ^ f % 3 = 2)
    {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1) {s' : GL (Fin 3) K} (hs'U : s' ∈ unitaryIsom3 h)
    (hS3 : (s' : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1) {c : K} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hSσ : (s' : Matrix (Fin 3) (Fin 3) K).map σ = c • (s' : Matrix (Fin 3) (Fin 3) K)) :
    ∃ (P : GL (Fin 3) K) (D : Fin 3 → K), P ∈ unitaryIsom3 h ∧
      (s' : Matrix (Fin 3) (Fin 3) K) * P = (P : Matrix (Fin 3) (Fin 3) K) * diagonal D ∧
      (P : Matrix (Fin 3) (Fin 3) K).map σ =
        (P : Matrix (Fin 3) (Fin 3) K) * !![0, 0, 1; 1, 0, 0; 0, 1, 0] ∧
      D 1 = c⁻¹ * D 0 ∧ D 2 = c⁻¹ * D 1 ∧ D 0 = c⁻¹ * D 2 := by
  classical
  have hσσσ : ∀ x, σ (σ (σ x)) = x := fun x => by
    have := congrArg (fun τ : K ≃+* K => τ x) hσ3
    simpa [pow_succ] using this
  obtain ⟨P, D, hSP, hPσ, hD1, hD2, hD0⟩ := Item19Res5Proof.exists_semilinear_basis hσ3
    (g := 1) (by simp) hS3 hc3 hc1 (by rw [Units.val_one, Matrix.one_mul, Matrix.mul_one, hSσ])
  rw [Units.val_one, Matrix.one_mul] at hPσ
  have hc0 : c ≠ 0 := by rintro rfl; norm_num at hc3
  have hpow : ∀ n : ℕ, (s' : Matrix (Fin 3) (Fin 3) K) ^ n * (P : Matrix (Fin 3) (Fin 3) K) =
      (P : Matrix (Fin 3) (Fin 3) K) * diagonal D ^ n := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, Matrix.mul_assoc, hSP, ← Matrix.mul_assoc, ih, Matrix.mul_assoc, ← pow_succ]
  have hD3 : ∀ i, D i ^ 3 = 1 := by
    intro i
    have h1 := hpow 3
    rw [hS3, Matrix.one_mul, diagonal_pow] at h1
    have h2 : diagonal (D ^ 3) = 1 := by
      have hP' := Units.inv_mul P
      calc diagonal (D ^ 3) = ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
            ((P : Matrix (Fin 3) (Fin 3) K) * diagonal (D ^ 3)) := by
            rw [← Matrix.mul_assoc, hP', Matrix.one_mul]
        _ = 1 := by rw [← h1, hP']
    have := congrFun (congrFun h2 i) i
    simpa using this
  have hDN : ∀ i, h.norm (D i) = 1 := fun i =>
    norm_eq_one_of_pow_three h hQ (by simp [UnitaryFieldData.norm]) (hD3 i)
  have hD0' : D 0 ≠ 0 := by
    intro h0
    have := hD3 0
    rw [h0] at this
    norm_num at this
  have hcp : IsPrimitiveRoot c⁻¹ 3 := (Item19Res5Proof.isPrimitiveRoot_of_pow_three hc3 hc1).inv
  have hDform : ∀ i : Fin 3, D i = c⁻¹ ^ (i : ℕ) * D 0 := by
    intro i
    fin_cases i
    · simp
    · simpa using hD1
    · show D 2 = c⁻¹ ^ 2 * D 0
      rw [hD2, hD1, sq, mul_assoc]
  have hDne : ∀ i j, i ≠ j → D i ≠ D j := by
    intro i j hij hDij
    rw [hDform i, hDform j] at hDij
    exact hij (Fin.ext (hcp.pow_inj i.2 j.2 (mul_right_cancel₀ hD0' hDij)))
  have hG : ∀ i j, i ≠ j → gram h (P : Matrix (Fin 3) (Fin 3) K) i j = 0 := fun i j hij =>
    gram_eq_zero_of_eigen h hs'U hSP (bar_mul_ne_one_of_ne h (hDN i) (hDne i j hij))
  have hcol : ∀ i, σ ((P : Matrix (Fin 3) (Fin 3) K) i 0) = (P : Matrix (Fin 3) (Fin 3) K) i 1 ∧
      σ ((P : Matrix (Fin 3) (Fin 3) K) i 1) = (P : Matrix (Fin 3) (Fin 3) K) i 2 := by
    intro i
    have e0 := congrFun (congrFun hPσ i) 0
    have e1 := congrFun (congrFun hPσ i) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three] at e0 e1
    exact ⟨e0, e1⟩
  have hGσ : ∀ a b : Fin 3, (∀ i, σ ((P : Matrix (Fin 3) (Fin 3) K) i a) =
      (P : Matrix (Fin 3) (Fin 3) K) i b) →
        gram h (P : Matrix (Fin 3) (Fin 3) K) b b =
          σ (gram h (P : Matrix (Fin 3) (Fin 3) K) a a) := by
    intro a b hab
    simp only [gram, Matrix.mul_apply, Matrix.transpose_apply, Matrix.map_apply, map_sum,
      map_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [← hab l, CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.map_bar_comm h σ]
  have hG11 := hGσ 0 1 fun i => (hcol i).1
  have hG22 := hGσ 1 2 fun i => (hcol i).2
  have hGdiag : gram h (P : Matrix (Fin 3) (Fin 3) K) =
      diagonal (fun i => gram h (P : Matrix (Fin 3) (Fin 3) K) i i) := by
    refine Matrix.ext fun i j => ?_
    by_cases hij : i = j
    · subst hij
      simp
    · rw [diagonal_apply_ne _ hij]
      exact hG i j hij
  have hdetP : (P : Matrix (Fin 3) (Fin 3) K).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 P.isUnit).ne_zero
  have hdetG : (gram h (P : Matrix (Fin 3) (Fin 3) K)).det ≠ 0 := by
    rw [gram, det_mul, det_transpose]
    refine mul_ne_zero ?_ hdetP
    rw [← RingHom.mapMatrix_apply, ← RingHom.map_det]
    exact (map_ne_zero h.bar).2 hdetP
  have hG00 : gram h (P : Matrix (Fin 3) (Fin 3) K) 0 0 ≠ 0 := by
    intro h0
    apply hdetG
    rw [hGdiag, det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ 0) h0
  obtain ⟨ρ, hρ⟩ := UnitaryHigher.exists_norm_eq h
    (c := (gram h (P : Matrix (Fin 3) (Fin 3) K) 0 0)⁻¹)
    (by rw [map_inv₀, bar_gram_apply_self])
  have hρ0 : ρ ≠ 0 := by
    intro h0
    rw [h0, UnitaryFieldData.norm, zero_mul] at hρ
    exact inv_ne_zero hG00 hρ.symm
  have hr0 : ∀ i, (![ρ, σ ρ, σ (σ ρ)] : Fin 3 → K) i ≠ 0 := by
    intro i
    fin_cases i
    · exact hρ0
    · show σ ρ ≠ 0
      rw [map_ne_zero]
      exact hρ0
    · show σ (σ ρ) ≠ 0
      rw [map_ne_zero, map_ne_zero]
      exact hρ0
  have hdetP' : ((P : Matrix (Fin 3) (Fin 3) K) * diagonal ![ρ, σ ρ, σ (σ ρ)]).det ≠ 0 := by
    rw [det_mul, det_diagonal]
    exact mul_ne_zero hdetP (Finset.prod_ne_zero_iff.2 fun i _ => hr0 i)
  refine ⟨GeneralLinearGroup.mkOfDetNeZero _ hdetP', D, ?_, ?_, ?_, hD1, hD2, hD0⟩
  · change gram h ((P : Matrix (Fin 3) (Fin 3) K) * diagonal ![ρ, σ ρ, σ (σ ρ)]) = 1
    rw [gram_mul, map_bar_diagonal_transpose h, hGdiag, diagonal_mul_diagonal,
      diagonal_mul_diagonal, ← diagonal_one]
    congr 1
    funext i
    have hN0 : h.bar ρ * gram h (P : Matrix (Fin 3) (Fin 3) K) 0 0 * ρ = 1 := by
      rw [show h.bar ρ * gram h (P : Matrix (Fin 3) (Fin 3) K) 0 0 * ρ =
        (ρ * h.bar ρ) * gram h (P : Matrix (Fin 3) (Fin 3) K) 0 0 by ring]
      have : ρ * h.bar ρ = (gram h (P : Matrix (Fin 3) (Fin 3) K) 0 0)⁻¹ := hρ
      rw [this, inv_mul_cancel₀ hG00]
    fin_cases i
    · exact hN0
    · show h.bar (σ ρ) * gram h (P : Matrix (Fin 3) (Fin 3) K) 1 1 * σ ρ = 1
      rw [hG11, ← CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.map_bar_comm h σ, ← map_mul,
        ← map_mul, hN0, map_one]
    · show h.bar (σ (σ ρ)) * gram h (P : Matrix (Fin 3) (Fin 3) K) 2 2 * σ (σ ρ) = 1
      rw [hG22, hG11, ← CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.map_bar_comm h σ,
        ← CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher.map_bar_comm h σ, ← map_mul,
        ← map_mul, ← map_mul, ← map_mul, hN0, map_one, map_one]
  · change (s' : Matrix (Fin 3) (Fin 3) K) * ((P : Matrix (Fin 3) (Fin 3) K) *
      diagonal ![ρ, σ ρ, σ (σ ρ)]) = ((P : Matrix (Fin 3) (Fin 3) K) *
        diagonal ![ρ, σ ρ, σ (σ ρ)]) * diagonal D
    rw [← Matrix.mul_assoc, hSP, Matrix.mul_assoc, Matrix.mul_assoc,
      Item19Res5Proof.diagonal_mul_comm]
  · change ((P : Matrix (Fin 3) (Fin 3) K) * diagonal ![ρ, σ ρ, σ (σ ρ)]).map σ =
      ((P : Matrix (Fin 3) (Fin 3) K) * diagonal ![ρ, σ ρ, σ (σ ρ)]) *
        !![0, 0, 1; 1, 0, 0; 0, 1, 0]
    have hrσ : (diagonal ![ρ, σ ρ, σ (σ ρ)]).map σ = diagonal ![σ ρ, σ (σ ρ), ρ] := by
      rw [diagonal_map (map_zero σ)]
      congr 1
      funext i
      fin_cases i <;> simp [hσσσ]
    rw [Matrix.map_mul, hPσ, hrσ, Matrix.mul_assoc,
      cyc_mul_diagonal (1 : K) 1 1 (σ ρ) (σ (σ ρ)) ρ, ← Matrix.mul_assoc]

theorem exists_twisted_shift (h : UnitaryFieldData p f K) (hQ : p ^ f % 3 = 2)
    {σ : K ≃+* K} (hσ3 : σ ^ 3 = 1) {s' : GL (Fin 3) K} (hs'U : s' ∈ unitaryIsom3 h)
    (hS3 : (s' : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1) {c : K} (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1)
    (hSσ : (s' : Matrix (Fin 3) (Fin 3) K).map σ = c • (s' : Matrix (Fin 3) (Fin 3) K)) :
    ∃ t : unitarySU p f K 3,
      (∀ i j, σ (((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) =
        ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) i j) ∧
      (s' : Matrix (Fin 3) (Fin 3) K) * ((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        c⁻¹ • (((t : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (s' : Matrix (Fin 3) (Fin 3) K)) := by
  classical
  obtain ⟨P, D, hPU, hSP, hPσ, hD1, hD2, hD0⟩ :=
    exists_unitary_twisted_basis h hQ hσ3 hs'U hS3 hc3 hc1 hSσ
  obtain ⟨C, hC⟩ := shift_mem_unitarySU h
  set Cm : Matrix (Fin 3) (Fin 3) K := !![0, 0, 1; 1, 0, 0; 0, 1, 0] with hCm
  have hPP : ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
      (P : Matrix (Fin 3) (Fin 3) K) = 1 := Units.inv_mul P
  have hPP' : (P : Matrix (Fin 3) (Fin 3) K) *
      ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := Units.mul_inv P
  have hCC : Cm * (Cm * Cm) = 1 := by
    rw [hCm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_three]
  have hCσ : Cm.map σ = Cm := by
    rw [hCm]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  have hCC3 : Cm * Cm * Cm = 1 := by rw [Matrix.mul_assoc]; exact hCC
  have hCC' : ∀ X : Matrix (Fin 3) (Fin 3) K, Cm * (Cm * (Cm * X)) = X := by
    intro X
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hCC3, Matrix.one_mul]
  have hPiσ : ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ =
      (Cm * Cm) * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have h1 : ((P : Matrix (Fin 3) (Fin 3) K) * Cm) *
        (((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ) = 1 := by
      rw [← hPσ, ← Matrix.map_mul, hPP', Matrix.map_one _ (map_zero σ) (map_one σ)]
    have hX : (Cm * Cm) * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        ((P : Matrix (Fin 3) (Fin 3) K) * Cm) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K),
        hPP, Matrix.one_mul, hCC3]
    calc ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ
        = ((Cm * Cm) * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          ((P : Matrix (Fin 3) (Fin 3) K) * Cm)) *
            (((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ) := by
          rw [hX, Matrix.one_mul]
      _ = (Cm * Cm) * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
          (((P : Matrix (Fin 3) (Fin 3) K) * Cm) *
            (((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ)) := by
          rw [Matrix.mul_assoc]
      _ = (Cm * Cm) * ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
          rw [h1, Matrix.mul_one]
  refine ⟨⟨P * C * P⁻¹, conj_mem_unitarySU hPU C.2⟩, ?_, ?_⟩
  · intro i j
    have h1 : (((P * C * P⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K).map σ =
        ((P * C * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      rw [Units.val_mul, Units.val_mul, hC, Matrix.map_mul, Matrix.map_mul, hPσ, hCσ, hPiσ]
      simp only [Matrix.mul_assoc]
      rw [hCC']
    exact congrFun (congrFun h1 i) j
  ·
    have hDC : diagonal D * Cm = c⁻¹ • (Cm * diagonal D) := by
      ext i j
      rw [Matrix.smul_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
      fin_cases i <;> fin_cases j <;> simp [hCm]
      all_goals first | exact hD0 | exact hD1 | exact hD2
    have hcancel : ∀ A B : Matrix (Fin 3) (Fin 3) K,
        A * (P : Matrix (Fin 3) (Fin 3) K) = B * (P : Matrix (Fin 3) (Fin 3) K) → A = B := by
      intro A B hAB
      calc A = A * (P : Matrix (Fin 3) (Fin 3) K) *
            ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
            rw [Matrix.mul_assoc, hPP', Matrix.mul_one]
        _ = B := by rw [hAB, Matrix.mul_assoc, hPP', Matrix.mul_one]
    have htm : (((⟨P * C * P⁻¹, conj_mem_unitarySU hPU C.2⟩ : unitarySU p f K 3) :
        GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = (P : Matrix (Fin 3) (Fin 3) K) * Cm *
          ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
      change ((P * (C : GL (Fin 3) K) * P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = _
      rw [Units.val_mul, Units.val_mul, hC]
    have htP : (P : Matrix (Fin 3) (Fin 3) K) * Cm *
        ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K) =
          (P : Matrix (Fin 3) (Fin 3) K) * Cm := by
      rw [Matrix.mul_assoc, hPP, Matrix.mul_one]
    rw [htm]
    apply hcancel
    set T : Matrix (Fin 3) (Fin 3) K := (P : Matrix (Fin 3) (Fin 3) K) * Cm *
      ((P⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) with hT
    calc (s' : Matrix (Fin 3) (Fin 3) K) * T * (P : Matrix (Fin 3) (Fin 3) K)
        = (s' : Matrix (Fin 3) (Fin 3) K) * (T * (P : Matrix (Fin 3) (Fin 3) K)) := by
          rw [Matrix.mul_assoc]
      _ = (s' : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K) * Cm := by
          rw [htP, Matrix.mul_assoc]
      _ = (P : Matrix (Fin 3) (Fin 3) K) * (diagonal D * Cm) := by
          rw [hSP, Matrix.mul_assoc]
      _ = c⁻¹ • ((P : Matrix (Fin 3) (Fin 3) K) * Cm * diagonal D) := by
          rw [hDC, Matrix.mul_smul, Matrix.mul_assoc]
      _ = c⁻¹ • (T * ((s' : Matrix (Fin 3) (Fin 3) K) * (P : Matrix (Fin 3) (Fin 3) K))) := by
          rw [hSP, ← Matrix.mul_assoc, htP]
      _ = c⁻¹ • (T * (s' : Matrix (Fin 3) (Fin 3) K)) * (P : Matrix (Fin 3) (Fin 3) K) := by
          rw [Matrix.smul_mul, Matrix.mul_assoc T]

theorem exists_fixed_central_of_field (h : UnitaryFieldData p f K) (hQ : p ^ f % 3 = 2)
    (hq : 2 < p ^ f) {φ : MulAut (unitarySU p f K 3)} (hφ3 : φ ^ 3 = 1)
    (hφ : φ ∉ (suConj h).range) {s : unitarySU p f K 3} (hs3 : s ^ 3 = 1)
    (hcomm : MulAut.conj s * φ = φ * MulAut.conj s) (hφs : φ s ≠ s) :
    ∃ t : unitarySU p f K 3, φ t = t ∧ s * t * s⁻¹ * t⁻¹ ∈ Subgroup.center (unitarySU p f K 3) ∧
      s * t * s⁻¹ * t⁻¹ ≠ 1 := by
  classical
  have := h.finite
  obtain ⟨σ, hσ, H, hφH⟩ := eq_conj_suField_of_not_mem hq hφ3 hφ
  have hσ3 : σ ^ 3 = 1 := by rw [← hσ]; exact pow_orderOf_eq_one σ
  have hcen : s⁻¹ * φ s ∈ Subgroup.center (unitarySU p f K 3) := by
    rw [Subgroup.mem_center_iff]
    intro y
    have h1 := congrArg (fun χ : MulAut (unitarySU p f K 3) => χ (φ.symm y)) hcomm
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv,
      MulEquiv.apply_symm_apply] at h1
    calc y * (s⁻¹ * φ s) = s⁻¹ * (s * y * s⁻¹) * φ s := by group
      _ = s⁻¹ * (φ s * y * (φ s)⁻¹) * φ s := by rw [h1]
      _ = s⁻¹ * φ s * y := by group
  have hcen' := hcen
  rw [center_unitarySU_three (h := h) hq] at hcen'
  obtain ⟨c, hcN, hc3, hcs⟩ := hcen'
  have hcK3 : ((c : Kˣ) : K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hc3, Units.val_one]
  have hc1 : ((c : Kˣ) : K) ≠ 1 := by
    intro h1
    apply hφs
    have hc1' : c = 1 := Units.ext h1
    have h2 : s⁻¹ * φ s = 1 := Subtype.ext (by rw [hcs, Subgroup.coe_one, hc1', map_one])
    calc φ s = s * (s⁻¹ * φ s) := by group
      _ = s := by rw [h2, mul_one]
  obtain ⟨s', hs'⟩ : ∃ s' : unitarySU p f K 3, s' = (suConj h H)⁻¹ s := ⟨_, rfl⟩
  have hfs' : suField h σ s' = s' * (suConj h H⁻¹ (s⁻¹ * φ s)) := by
    have h1 : suField h σ = (suConj h H)⁻¹ * φ * suConj h H := by rw [hφH]; group
    have h2 : suConj h H s' = s := by rw [hs', MulAut.inv_apply, MulEquiv.apply_symm_apply]
    rw [h1, MulAut.mul_apply, MulAut.mul_apply, h2, map_inv, hs', ← map_mul]
    congr 1
    group
  have hzfix : ((suConj h H⁻¹ (s⁻¹ * φ s) : unitarySU p f K 3) : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) c := by
    rw [coe_suConj, hcs, (commute_scalar c _).eq, mul_assoc, ← Subgroup.coe_mul,
      mul_inv_cancel, Subgroup.coe_one, mul_one]
  have hSσ : ((s' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).map σ =
      (c : K) • ((s' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
    have h1 := congrArg (fun x : unitarySU p f K 3 => ((x : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K)) hfs'
    simp only [coe_suField, coe_glAut, Subgroup.coe_mul, Units.val_mul, hzfix,
      GeneralLinearGroup.coe_scalar] at h1
    rw [h1, Matrix.scalar_apply, ← Matrix.smul_eq_mul_diagonal]
  have hS3 : ((s' : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) ^ 3 = 1 := by
    rw [← Units.val_pow_eq_pow_val, ← Subgroup.coe_pow, hs', ← map_pow, hs3, map_one,
      Subgroup.coe_one, Units.val_one]
  obtain ⟨t₀, ht₀σ, hst⟩ := exists_twisted_shift h hQ hσ3 (unitarySU_le_unitaryIsom3 s'.2) hS3
    hcK3 hc1 hSσ
  have hz₀ : ((s' * t₀ * s'⁻¹ * t₀⁻¹ : unitarySU p f K 3) : GL (Fin 3) K) =
      GeneralLinearGroup.scalar (Fin 3) c⁻¹ := by
    apply Units.ext
    have e1 : ((s' * t₀ : unitarySU p f K 3) : GL (Fin 3) K) =
        GeneralLinearGroup.scalar (Fin 3) c⁻¹ * ((t₀ * s' : unitarySU p f K 3) : GL (Fin 3) K) := by
      apply Units.ext
      rw [Units.val_mul, GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        ← Matrix.smul_eq_diagonal_mul, Subgroup.coe_mul, Subgroup.coe_mul, Units.val_mul,
        Units.val_mul, Units.val_inv_eq_inv_val]
      exact hst
    have e2 : (s' * t₀ * s'⁻¹ * t₀⁻¹ : unitarySU p f K 3) = (s' * t₀) * (t₀ * s')⁻¹ := by group
    rw [e2, Subgroup.coe_mul, Subgroup.coe_inv, e1, mul_inv_cancel_right]
  have hsH : s = suConj h H s' := by rw [hs', MulAut.inv_apply, MulEquiv.apply_symm_apply]
  have hcm : s * suConj h H t₀ * s⁻¹ * (suConj h H t₀)⁻¹ = suConj h H (s' * t₀ * s'⁻¹ * t₀⁻¹) := by
    rw [hsH, map_mul, map_mul, map_mul, map_inv, map_inv]
  have hzc : suConj h H (s' * t₀ * s'⁻¹ * t₀⁻¹) = s' * t₀ * s'⁻¹ * t₀⁻¹ := by
    apply Subtype.ext
    rw [coe_suConj, hz₀, (commute_scalar c⁻¹ _).eq, mul_assoc, ← Subgroup.coe_mul,
      mul_inv_cancel, Subgroup.coe_one, mul_one]
  refine ⟨suConj h H t₀, ?_, ?_, ?_⟩
  · rw [hφH]
    exact conj_suField_fix H σ t₀ ht₀σ
  · rw [hcm, hzc, center_unitarySU_three (h := h) hq]
    refine ⟨c⁻¹, ?_, by rw [inv_pow, hc3, inv_one], hz₀⟩
    rw [Units.val_inv_eq_inv_val, CFSG.ClassicalGroups.UnitaryFlag.norm_inv_eq h, hcN, inv_one]
  · rw [hcm, hzc]
    intro h1
    have h2 := congrArg (fun x : unitarySU p f K 3 => ((x : GL (Fin 3) K) :
      Matrix (Fin 3) (Fin 3) K) 0 0) h1
    simp only [hz₀, Subgroup.coe_one, Units.val_one, GeneralLinearGroup.coe_scalar,
      Matrix.scalar_apply, Matrix.diagonal_apply_eq, Matrix.one_apply_eq] at h2
    apply hc1
    rw [Units.val_inv_eq_inv_val] at h2
    exact inv_eq_one.mp h2

end Item19Res6Proof

open Item19Res5Proof Item19Res6Proof CFSG.LocalAnalysis.RankThreeTheoremC.SL3CoverGen
  CFSG.RankThree.PartTwo.KFacts in
theorem seitz199OuterUnitaryEight_of_seitzThree (hS : SeitzThreeLThreePi) :
    Seitz199OuterUnitaryEight := by
  intro p f K _ h h8 D hD3 hD9 hinn hnfix hdiag
  classical
  have := h.finite
  have hQ : p ^ f % 3 = 2 := by rw [h8]
  have hq : 2 < p ^ f := by rw [h8]; norm_num
  have : Fact p.Prime := ⟨h.prime⟩
  have hcard : Nat.card K = (p ^ f) ^ 2 := by rw [h.card, ← pow_mul, mul_comm]
  have hnq : ((3 : ℕ), p ^ f) ≠ (3, 2) := by
    intro h3
    simp only [Prod.mk.injEq, true_and] at h3
    omega
  have hX : CFSG.IsQuasisimple (CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3) :=
    (CFSG.LieType.Universal.Unitary.isQuasisimple_statedSU_of_card hcard le_rfl hnq).1
  obtain ⟨hgen, hZ3⟩ := SeitzScopeProof.kGenTwoMod_and_card_center_su_scope hS hX h hQ hq
    (MulEquiv.refl _)
  have hD := Item19ResProof.isElemAbelian_of_pow_three hD3 hD9
  obtain ⟨e, he, s, hs3, hsD, hes⟩ := hnfix
  obtain ⟨φ, hφD, hφ⟩ := Set.not_subset.1 hdiag
  have hφ1 : φ ≠ 1 := fun h1 => hφ ⟨1, by rw [map_one, h1]⟩
  have hcomm : MulAut.conj s * φ = φ * MulAut.conj s :=
    congrArg Subtype.val (hD.1.is_comm.comm ⟨_, hsD⟩ ⟨φ, hφD⟩)
  have hφs : φ s ≠ s := by
    intro hfix
    have hc1 : MulAut.conj s ≠ 1 := by
      intro h1
      apply hes
      have hsZ : s ∈ Subgroup.center (CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3) := by
        rw [Subgroup.mem_center_iff]
        intro y
        have := congrArg (fun χ : MulAut (CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3) =>
          χ y) h1
        simp only [MulAut.conj_apply, MulAut.one_apply] at this
        calc y * s = s * y * s⁻¹ * s := by rw [this]
          _ = s * y := by group
      exact apply_eq_of_mem_center h hq (hD3 e he) hsZ
    have hnot : φ ∉ Subgroup.zpowers (MulAut.conj s) := by
      rintro ⟨n, hn⟩
      apply hφ
      rw [← hn]
      show MulAut.conj s ^ n ∈ (suConj h).range
      rw [conj_eq_suConj (h := h) s, ← map_zpow]
      exact ⟨_, rfl⟩
    have hle : D ≤ MulAction.stabilizer
        (MulAut (CFSG.ClassicalGroups.UnitaryFlag.unitarySU p f K 3)) s :=
      le_of_card_nine hD9 hsD hφD (hD.2 _ hsD) hc1 hnot
        (by rw [MulAction.mem_stabilizer_iff, MulAut.smul_def, MulAut.conj_apply]; group)
        (by rw [MulAction.mem_stabilizer_iff, MulAut.smul_def]; exact hfix)
    have h1 := hle he
    rw [MulAction.mem_stabilizer_iff, MulAut.smul_def] at h1
    exact hes h1
  obtain ⟨t, htφ, htc, ht1⟩ := exists_fixed_central_of_field h hQ hq (hD3 φ hφD) hφ hs3 hcomm hφs
  have ht : t ∈ Subgroup.closure (fixSet D) := Subgroup.subset_closure ⟨φ, hφD, hφ1, htφ⟩
  exact closure_fixSet_of_cover hgen hZ3 hD hD9 he hsD hes ht htc ht1

open Item19Res6Proof in
theorem seitz199OuterUnitary_of_seitzThree_diag
    (hS : SeitzThreeLThreePi) (hA : Seitz199OuterUnitaryDiag) : Seitz199OuterUnitary :=
  seitz199OuterUnitary_of_diag_eight hA (seitz199OuterUnitaryEight_of_seitzThree hS)

end CFSG.RankThree.PartTwo.Sec19
