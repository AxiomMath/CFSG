module

public import CFSG.RankThree.PartTwo.Sec14.Item142L3Res3ProofHom
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LieType.SeitzGeneration.OutdiagHeis
public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs

public section

namespace CFSG.RankThree.PartTwo.Sec14.L3PGLU27

open Matrix CFSG.RankThree.PartTwo.Sec4 CFSG.LocalAnalysis.ComponentInitial
open CFSG.LieType.SeitzGeneration (heisC homMat blockOneGL)
open CFSG.ClassicalGroups.UnitaryFlag (unitarySU)

variable {K : Type} [Field K]

@[expose] def fourierMat (τ : K) : Matrix (Fin 3) (Fin 3) K :=
  !![1, 1, 1; 1, τ, τ ^ 2; 1, τ ^ 2, τ]

section Fourier

variable {τ : K} (hτ : τ ^ 3 = 1) (hτ1 : τ ≠ 1)

include hτ hτ1 in
theorem one_add_tau_add_sq : 1 + τ + τ ^ 2 = 0 := by
  have h : (τ - 1) * (1 + τ + τ ^ 2) = 0 := by linear_combination hτ
  rcases mul_eq_zero.mp h with h0 | h0
  · exact absurd (sub_eq_zero.mp h0) hτ1
  · exact h0

include hτ in
theorem fourier_mul_cyc :
    fourierMat τ * ((cycThree : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      τ ^ 2 • (((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) * fourierMat τ) := by
  rw [coe_cycThree, coe_diagTau]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourierMat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination hτ | linear_combination (-1 : K) * hτ |
      linear_combination τ * hτ | linear_combination (-τ) * hτ |
      linear_combination τ ^ 2 * hτ | linear_combination (-τ ^ 2) * hτ |
      linear_combination (τ ^ 3 + 1) * hτ | linear_combination (-(τ ^ 3 + 1)) * hτ

include hτ in
theorem fourier_mul_diagTau :
    fourierMat τ * ((diagTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      τ • ((((cycThree : GL (Fin 3) K)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) *
        fourierMat τ) := by
  rw [coe_diagTau]
  change _ = τ • (!![0, 1, 0; 0, 0, 1; 1, 0, 0] * fourierMat τ)
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourierMat, Matrix.mul_apply, Fin.sum_univ_three] <;>
    first | ring1 | linear_combination hτ | linear_combination (-1 : K) * hτ |
      linear_combination τ * hτ

variable {p f : ℕ} (h : UnitaryFieldData p f K) (hq3 : 3 ∣ p ^ f + 1)

include hτ hq3 in
theorem bar_tau : h.bar τ = τ ^ 2 :=
  CFSG.LieType.SeitzGeneration.bar_eq_sq_of_cube h hq3 hτ

include hτ hτ1 hq3 in
theorem fourier_mul_star :
    fourierMat τ * ((fourierMat τ).map h.bar)ᵀ = (3 : K) • (1 : Matrix (Fin 3) (Fin 3) K) := by
  have hb := bar_tau hτ h hq3
  have h0 := one_add_tau_add_sq hτ hτ1
  have hb2 : h.bar (τ ^ 2) = τ := by
    rw [map_pow, hb, ← pow_mul]
    calc τ ^ (2 * 2) = τ ^ 3 * τ := by ring
      _ = τ := by rw [hτ, one_mul]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [fourierMat, Matrix.mul_apply, Fin.sum_univ_three, hb, hb2] <;>
    first | ring1 | linear_combination h0 | linear_combination (-1 : K) * h0 |
      linear_combination (2 : K) * hτ | linear_combination (-2 : K) * hτ |
      linear_combination h0 + τ * hτ

variable {ε : K} (hε : h.bar ε * ε = 3) (h3 : (3 : K) ≠ 0)

include hε in
theorem inv_mul_bar_inv : ε⁻¹ * (h.bar ε)⁻¹ = 3⁻¹ := by
  rw [← mul_inv, mul_comm, hε]

include hτ hτ1 hq3 hε h3 in
theorem fourier_unit_mul :
    (ε⁻¹ • fourierMat τ) * ((h.bar ε)⁻¹ • ((fourierMat τ).map h.bar)ᵀ) = 1 := by
  rw [Matrix.smul_mul, Matrix.mul_smul, fourier_mul_star hτ hτ1 h hq3, smul_smul, smul_smul,
    inv_mul_bar_inv h hε, inv_mul_cancel₀ h3, one_smul]

include hτ hτ1 hq3 hε h3 in
theorem fourier_unit_mul' :
    ((h.bar ε)⁻¹ • ((fourierMat τ).map h.bar)ᵀ) * (ε⁻¹ • fourierMat τ) = 1 :=
  mul_eq_one_comm.mp (fourier_unit_mul hτ hτ1 h hq3 hε h3)

@[expose] noncomputable def fourierGL : GL (Fin 3) K :=
  ⟨ε⁻¹ • fourierMat τ, (h.bar ε)⁻¹ • ((fourierMat τ).map h.bar)ᵀ,
    fourier_unit_mul hτ hτ1 h hq3 hε h3, fourier_unit_mul' hτ hτ1 h hq3 hε h3⟩

theorem coe_fourierGL :
    ((fourierGL hτ hτ1 h hq3 hε h3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      ε⁻¹ • fourierMat τ :=
  rfl

theorem coe_fourierGL_inv :
    (((fourierGL hτ hτ1 h hq3 hε h3)⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      (h.bar ε)⁻¹ • ((fourierMat τ).map h.bar)ᵀ :=
  rfl

theorem fourierGL_unitary :
    ((((fourierGL hτ hτ1 h hq3 hε h3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)).map h.bar)ᵀ *
      ((fourierGL hτ hτ1 h hq3 hε h3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) = 1 := by
  rw [coe_fourierGL]
  have e : ((ε⁻¹ • fourierMat τ).map h.bar)ᵀ = (h.bar ε)⁻¹ • ((fourierMat τ).map h.bar)ᵀ := by
    ext i j
    simp [Matrix.map_apply, map_inv₀]
  rw [e]
  exact fourier_unit_mul' hτ hτ1 h hq3 hε h3

include hτ hτ1 hq3 hε in
theorem fourier_conj_mulVec (x : K) :
    (!![0, 1, 0; 0, 0, 1; 1, 0, 0] * ((ε⁻¹ • fourierMat τ) * diagonal ![x, 1, 1] *
      ((h.bar ε)⁻¹ • ((fourierMat τ).map h.bar)ᵀ))) *ᵥ ![0, 0, 1] =
      ![(x - 1) / 3, (x + 2) / 3, (x - 1) / 3] := by
  have hb := bar_tau hτ h hq3
  have h0 := one_add_tau_add_sq hτ hτ1
  have hb2 : h.bar (τ ^ 2) = τ := by
    rw [map_pow, hb, ← pow_mul]
    calc τ ^ (2 * 2) = τ ^ 3 * τ := by ring
      _ = τ := by rw [hτ, one_mul]
  have hs := inv_mul_bar_inv h hε
  have hs' : (h.bar ε)⁻¹ * ε⁻¹ = 3⁻¹ := by rw [mul_comm]; exact hs
  have e : (!![0, 1, 0; 0, 0, 1; 1, 0, 0] * ((ε⁻¹ • fourierMat τ) * diagonal ![x, 1, 1] *
      ((h.bar ε)⁻¹ • ((fourierMat τ).map h.bar)ᵀ))) *ᵥ ![0, 0, 1] =
      (3 : K)⁻¹ • ((!![0, 1, 0; 0, 0, 1; 1, 0, 0] * (fourierMat τ * diagonal ![x, 1, 1] *
        ((fourierMat τ).map h.bar)ᵀ)) *ᵥ ![0, 0, 1]) := by
    simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.smul_mulVec, hs']
  rw [e, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
  have e1 : ((fourierMat τ).map h.bar)ᵀ *ᵥ ![0, 0, 1] = ![1, τ, τ ^ 2] := by
    ext i
    fin_cases i <;> simp [fourierMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three, hb, hb2]
  have e2 : diagonal ![x, 1, 1] *ᵥ ![1, τ, τ ^ 2] = ![x, τ, τ ^ 2] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec_diagonal]
  have e3 : fourierMat τ *ᵥ ![x, τ, τ ^ 2] = ![x - 1, x - 1, x + 2] := by
    ext i
    fin_cases i <;> simp [fourierMat, Matrix.mulVec, dotProduct, Fin.sum_univ_three] <;>
      first | linear_combination h0 | linear_combination h0 + τ * hτ | linear_combination 2 * hτ
  have e4 : !![0, 1, 0; 0, 0, 1; 1, 0, 0] *ᵥ ![x - 1, x - 1, x + 2] = ![x - 1, x + 2, x - 1] := by
    ext i
    fin_cases i <;> simp [Matrix.mulVec, dotProduct, Fin.sum_univ_three]
  rw [e1, e2, e3, e4]
  ext i
  fin_cases i <;> simp [div_eq_inv_mul]

end Fourier

theorem exists_good_of_card [DecidableEq K] (S : Finset K) (hS : 5 ≤ S.card) (a b : K) :
    ∃ x ∈ S, x ≠ a ∧ x ≠ b ∧ x ^ 2 + 7 * x + 1 ≠ 0 := by
  classical
  set P : Polynomial K := Polynomial.C 1 * Polynomial.X ^ 2 + Polynomial.C 7 * Polynomial.X +
    Polynomial.C 1 with hP
  have hdeg : P.natDegree = 2 := Polynomial.natDegree_quadratic one_ne_zero
  have hP0 : P ≠ 0 := by
    intro h0
    rw [h0, Polynomial.natDegree_zero] at hdeg
    omega
  set B : Finset K := ({a, b} : Finset K) ∪ P.roots.toFinset with hB
  have hBc : B.card ≤ 4 := by
    calc B.card ≤ ({a, b} : Finset K).card + P.roots.toFinset.card := Finset.card_union_le _ _
      _ ≤ 2 + 2 := by
        gcongr
        · exact Finset.card_le_two
        · exact (Multiset.toFinset_card_le _).trans ((Polynomial.card_roots' P).trans hdeg.le)
  obtain ⟨x, hxS, hxB⟩ := Finset.exists_mem_notMem_of_card_lt_card (by omega : B.card < S.card)
  refine ⟨x, hxS, fun h => hxB ?_, fun h => hxB ?_, fun h => hxB ?_⟩
  · rw [hB, Finset.mem_union]
    left
    simp [h]
  · rw [hB, Finset.mem_union]
    left
    simp [h]
  · rw [hB, Finset.mem_union, Multiset.mem_toFinset, Polynomial.mem_roots hP0]
    right
    simp [hP, Polynomial.IsRoot, h]

theorem block_mem_of_generic_column {p f : ℕ}
    (h : UnitaryFieldData p f K) (hq4 : 4 ≤ p ^ f) {a : K} (haq : a ^ (p ^ f + 1) = 1)
    (ha3 : 3 ≤ orderOf a) (h6 : 6 ≤ orderOf (a⁻¹ ^ 2 / a))
    (hsf : SubfieldFree p f (orderOf (a⁻¹ ^ 2 / a))) (Q : Subgroup (GL (Fin 3) K))
    (hH1 : ∃ g ∈ Q, (g : Matrix (Fin 3) (Fin 3) K) = homMat h a (a⁻¹ ^ 2 - a) ![1, 0, 0])
    (hH3 : ∃ g ∈ Q, (g : Matrix (Fin 3) (Fin 3) K) = homMat h a (a⁻¹ ^ 2 - a) ![0, 0, 1])
    {z : GL (Fin 3) K} (hzQ : z ∈ Q)
    (hzU : ((z : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (z : Matrix (Fin 3) (Fin 3) K) = 1)
    (hw0 : ((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 0 ≠ 0)
    (hw1 : ((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 1 ≠ 0)
    (hw2 : ((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 2 ≠ 0)
    (hn2 : h.bar (((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 2) *
        ((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 2 ≠ 1) :
    ∀ g : GL (Fin 2) K, g ∈ unitarySU p f K 2 → blockOneGL g ∈ Q := by
  have hzP : (z : Matrix (Fin 3) (Fin 3) K) * ((z : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ = 1 :=
    mul_eq_one_comm.2 hzU
  have hwN : h.bar (((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 0) *
      ((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 0 +
      h.bar (((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 1) *
      ((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 1 +
      h.bar (((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 2) *
      ((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) 2 = 1 := by
    have := congrFun (congrFun hzU 2) 2
    simpa [Matrix.mul_apply, Fin.sum_univ_three, Matrix.mulVec, dotProduct] using this
  obtain ⟨g₃, hg₃Q, hg₃m⟩ := hH3
  have hconj : (((z * g₃ * z⁻¹ : GL (Fin 3) K)) : Matrix (Fin 3) (Fin 3) K) =
      homMat h a (a⁻¹ ^ 2 - a) ((z : Matrix (Fin 3) (Fin 3) K) *ᵥ ![0, 0, 1]) := by
    have hzinv : ((z⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
        ((z : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ := by
      calc ((z⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K)
          = ((z : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ * (z : Matrix (Fin 3) (Fin 3) K) *
              ((z⁻¹ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) := by
            rw [hzU, Matrix.one_mul]
        _ = ((z : Matrix (Fin 3) (Fin 3) K).map h.bar)ᵀ := by
            rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one,
              Matrix.mul_one]
    rw [Units.val_mul, Units.val_mul, hzinv, hg₃m]
    exact CFSG.LieType.SeitzGeneration.conj_homMat h _ hzP
  exact su2_block_mem_of_generic_prim h hq4 haq ha3 h6 hsf Q hH1 ⟨g₃, hg₃Q, hg₃m⟩ hwN hw0 hw1
    hw2 (by intro h0; apply hn2; linear_combination hwN - h0)
    ⟨z * g₃ * z⁻¹, Q.mul_mem (Q.mul_mem hzQ hg₃Q) (Q.inv_mem hzQ), hconj⟩

end CFSG.RankThree.PartTwo.Sec14.L3PGLU27
