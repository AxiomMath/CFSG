module

public import CFSG.RankThree.PartTwo.Sec4.LThreePiDefs
public import CFSG.RankThree.PartTwo.Sec4.Ronan148BHessDefs

public section

namespace CFSG.RankThree.PartTwo.Sec4.Ronan148L

open Matrix CFSG.LocalAnalysis.ComponentInitial
open CFSG.RankThree.PartTwo.Sec4.Ronan148B

variable {K : Type} [Field K] {p f : ℕ}

theorem hessTMat_transpose (i : Fin 3) : (hessTMat i : Matrix (Fin 3) (Fin 3) K)ᵀ = hessTMat i := by
  unfold hessTMat
  exact diagonal_transpose _

theorem hessTMat_map_bar (h : UnitaryFieldData p f K) (i : Fin 3) :
    (hessTMat i : Matrix (Fin 3) (Fin 3) K).map h.bar = hessTMat i := by
  ext a b
  simp only [Matrix.map_apply, hessTMat, Matrix.diagonal_apply]
  split_ifs <;> simp

theorem hessT_mem_slPi {π : Bool} (hπ : π = false → UnitaryFieldData p f K) (i : Fin 3) :
    hessT i ∈ slPi π 3 (p ^ f) K := by
  have hdet : ((hessT i : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [coe_hessT, hessTMat, det_diagonal, Fin.prod_univ_three]
    fin_cases i <;> simp
  rw [mem_slPi_iff hπ]
  refine ⟨?_, hdet⟩
  cases π
  · have h := hπ rfl
    rw [mem_glPi_false h, coe_hessT, hessTMat_map_bar h, hessTMat_transpose]
    exact hessTMat_mul_self i
  · exact mem_glPi_true _ _

theorem hessT_mul_self (i : Fin 3) : (hessT i : GL (Fin 3) K) * hessT i = 1 :=
  Units.ext (hessTMat_mul_self i)

theorem hessT_zero_mul_one : (hessT 0 : GL (Fin 3) K) * hessT 1 = hessT 2 := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_hessT, coe_hessT, coe_hessT, hessTMat, hessTMat, hessTMat,
    diagonal_mul_diagonal]
  congr 1
  funext j
  fin_cases j <;> simp

theorem hessT_one_mul_zero : (hessT 1 : GL (Fin 3) K) * hessT 0 = hessT 2 := by
  refine Units.ext ?_
  rw [Units.val_mul, coe_hessT, coe_hessT, coe_hessT, hessTMat, hessTMat, hessTMat,
    diagonal_mul_diagonal]
  congr 1
  funext j
  fin_cases j <;> simp

theorem hessT_mul_diagTau {τ : K} (hτ : τ ^ 3 = 1) (i : Fin 3) :
    (hessT i : GL (Fin 3) K) * diagTau hτ = diagTau hτ * hessT i := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_hessT, coe_diagTau]
  ext a b
  fin_cases i <;> fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hessTMat, Matrix.diagonal_apply]

theorem cycThree_mul_hessT_zero :
    (cycThree : GL (Fin 3) K) * hessT 0 = hessT 1 * cycThree := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_hessT, coe_hessT, coe_cycThree]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hessTMat, Matrix.diagonal_apply]

theorem cycThree_mul_hessT_one :
    (cycThree : GL (Fin 3) K) * hessT 1 = hessT 2 * cycThree := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_hessT, coe_hessT, coe_cycThree]
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, hessTMat, Matrix.diagonal_apply]

theorem mk_hessT_zero_ne_one (h2 : (2 : K) ≠ 0) :
    ProjGenLinGroup.mk (hessT 0 : GL (Fin 3) K) ≠ 1 := by
  intro h
  rw [ProjGenLinGroup.mk_eq_one, GeneralLinearGroup.center_eq_range_scalar] at h
  obtain ⟨u, hu⟩ := h
  have h00 : (u : K) = 1 := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 0 0) hu
    simpa [GeneralLinearGroup.coe_scalar, coe_hessT, hessTMat, Matrix.scalar_apply] using this
  have h11 : (u : K) = -1 := by
    have := congrArg (fun g : GL (Fin 3) K => (g : Matrix (Fin 3) (Fin 3) K) 1 1) hu
    simpa [GeneralLinearGroup.coe_scalar, coe_hessT, hessTMat, Matrix.scalar_apply] using this
  exact h2 (by linear_combination h11 - h00)

theorem pow_eq_sq_of_modThree {q : ℕ} (hq : ModThree false q) {τ : K} (hτ : τ ^ 3 = 1) :
    τ ^ q = τ ^ 2 := by
  have h1 := pow_succ_eq_one_of_modThree hq hτ
  calc τ ^ q = τ ^ q * τ ^ 3 := by rw [hτ, mul_one]
    _ = τ ^ (q + 1) * τ ^ 2 := by ring
    _ = τ ^ 2 := by rw [h1, one_mul]

theorem hessPhiMat_map_bar (h : UnitaryFieldData p f K) (hq : ModThree false (p ^ f)) {ω : K}
    (hω : ω ^ 2 + ω + 1 = 0) :
    (hessPhiMat ω).map h.bar = hessPhiInvMat ω := by
  have hbar : h.bar ω = ω ^ 2 := by
    rw [h.bar_apply]
    exact pow_eq_sq_of_modThree hq (pow_three_eq_one_of_hess hω)
  ext i j
  simp only [Matrix.map_apply, hessPhiMat, hessPhiInvMat, map_div₀, map_pow, map_add, map_mul,
    map_one, map_ofNat, hbar, ← pow_mul]

theorem hessPhiInvMat_transpose (ω : K) : (hessPhiInvMat ω)ᵀ = hessPhiInvMat ω := by
  ext i j
  simp only [Matrix.transpose_apply, hessPhiInvMat, mul_comm (j : ℕ)]

theorem hessPhi_mem_slPi {π : Bool} (hπ : π = false → UnitaryFieldData p f K)
    (hq : π = false → ModThree false (p ^ f)) {ω : K} (hω : ω ^ 2 + ω + 1 = 0)
    (h3 : (3 : K) ≠ 0) : hessPhi hω h3 ∈ slPi π 3 (p ^ f) K := by
  have h1 := one_add_two_mul_ne_zero hω h3
  have hdet : ((hessPhi hω h3 : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K).det = 1 := by
    rw [coe_hessPhi, det_fin_three]
    simp only [hessPhiMat, Fin.val_zero, Fin.val_one, Fin.val_two, mul_zero, zero_mul, mul_one,
      one_mul, pow_zero, pow_one]
    field_simp
    grind
  rw [mem_slPi_iff hπ]
  refine ⟨?_, hdet⟩
  cases π
  · have h := hπ rfl
    rw [mem_glPi_false h, coe_hessPhi, hessPhiMat_map_bar h (hq rfl) hω, hessPhiInvMat_transpose]
    exact hessPhiInvMat_mul hω h3
  · exact mem_glPi_true _ _

theorem hessPhi_mul_diagTau {τ : K} (hτ : τ ^ 3 = 1) (hω : τ ^ 2 + τ + 1 = 0) (h3 : (3 : K) ≠ 0)
    (hτ0 : τ ≠ 0) :
    hessPhi hω h3 * diagTau hτ =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 τ hτ0) * (cycThree⁻¹ * hessPhi hω h3) := by
  have h1 := one_add_two_mul_ne_zero hω h3
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_hessPhi, coe_diagTau,
    GeneralLinearGroup.coe_scalar, Units.val_mk0]
  change hessPhiMat τ * _ = Matrix.scalar (Fin 3) τ * (!![0, 1, 0; 0, 0, 1; 1, 0, 0] * _)
  ext a b
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, Matrix.diagonal_apply]
  fin_cases a <;> fin_cases b <;> simp [hessPhiMat] <;> field_simp <;> grind

theorem hessPhi_mul_cycThree {τ : K} (hτ : τ ^ 3 = 1) (hω : τ ^ 2 + τ + 1 = 0) (h3 : (3 : K) ≠ 0)
    (hτ0 : τ ≠ 0) :
    hessPhi hω h3 * cycThree =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (τ ^ 2) (pow_ne_zero 2 hτ0)) *
        (diagTau hτ * hessPhi hω h3) := by
  have h1 := one_add_two_mul_ne_zero hω h3
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, Units.val_mul, coe_hessPhi, coe_diagTau, coe_cycThree,
    GeneralLinearGroup.coe_scalar, Units.val_mk0]
  ext a b
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, Matrix.diagonal_apply]
  fin_cases a <;> fin_cases b <;> simp [hessPhiMat] <;> field_simp <;> grind

@[expose] def diagOneOneTau {τ : K} (hτ : τ ^ 3 = 1) : GL (Fin 3) K :=
  ⟨!![1, 0, 0; 0, 1, 0; 0, 0, τ], !![1, 0, 0; 0, 1, 0; 0, 0, τ ^ 2],
    by
      have h : τ * τ ^ 2 = 1 := by rw [← pow_succ']; exact hτ
      ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, h],
    by
      have h : τ ^ 2 * τ = 1 := by rw [← pow_succ]; exact hτ
      ext i j; fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, h]⟩

theorem coe_diagOneOneTau {τ : K} (hτ : τ ^ 3 = 1) :
    ((diagOneOneTau hτ : GL (Fin 3) K) : Matrix (Fin 3) (Fin 3) K) =
      !![1, 0, 0; 0, 1, 0; 0, 0, τ] :=
  rfl

theorem diagOneOneTau_mem_glPi {π : Bool} (hπ : π = false → UnitaryFieldData p f K)
    (hq : π = false → ModThree false (p ^ f)) {τ : K} (hτ : τ ^ 3 = 1) :
    diagOneOneTau hτ ∈ glPi π 3 (p ^ f) K := by
  cases π
  · have h := hπ rfl
    have hbar : h.bar τ * τ = 1 := by
      rw [h.bar_apply, pow_eq_sq_of_modThree (hq rfl) hτ, ← pow_succ]
      exact hτ
    rw [mem_glPi_false h, coe_diagOneOneTau]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [mul_apply, Fin.sum_univ_three, transpose_apply, hbar]
  · exact mem_glPi_true _ _

theorem diagOneOneTau_mul_diagTau {τ : K} (hτ : τ ^ 3 = 1) :
    diagOneOneTau hτ * diagTau hτ = diagTau hτ * diagOneOneTau hτ := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, coe_diagOneOneTau, coe_diagTau]
  ext a b
  fin_cases a <;> fin_cases b <;> simp [Matrix.mul_apply, Fin.sum_univ_three, mul_comm]

theorem diagOneOneTau_mul_cycThree {τ : K} (hτ : τ ^ 3 = 1) (hτ0 : τ ≠ 0) :
    diagOneOneTau hτ * cycThree =
      GeneralLinearGroup.scalar (Fin 3) (Units.mk0 (τ ^ 2) (pow_ne_zero 2 hτ0)) *
        (cycThree * diagTau hτ * diagOneOneTau hτ) := by
  refine Units.ext ?_
  rw [Units.val_mul, Units.val_mul, Units.val_mul, Units.val_mul, coe_diagOneOneTau, coe_diagTau,
    coe_cycThree, GeneralLinearGroup.coe_scalar, Units.val_mk0]
  ext a b
  simp only [Matrix.mul_apply, Fin.sum_univ_three, Matrix.scalar_apply, Matrix.diagonal_apply]
  fin_cases a <;> fin_cases b <;> simp <;> grind

theorem mk_conj_eq_of_mul_eq_scalar_mul {A B C : GL (Fin 3) K} {u : Kˣ}
    (h : A * B = GeneralLinearGroup.scalar (Fin 3) u * (C * A)) :
    ProjGenLinGroup.mk A * ProjGenLinGroup.mk B * (ProjGenLinGroup.mk A)⁻¹ =
      ProjGenLinGroup.mk C := by
  rw [← map_mul, ← map_inv, ← map_mul, h, mul_assoc, mul_assoc, mul_inv_cancel, mul_one, map_mul,
    ProjGenLinGroup.mk_scalar, one_mul]

theorem mk_hessPhi_conj_diagTau {τ : K} (hτ : τ ^ 3 = 1) (hω : τ ^ 2 + τ + 1 = 0)
    (h3 : (3 : K) ≠ 0) :
    ProjGenLinGroup.mk (hessPhi hω h3) * ProjGenLinGroup.mk (diagTau hτ) *
        (ProjGenLinGroup.mk (hessPhi hω h3))⁻¹ =
      (ProjGenLinGroup.mk (cycThree : GL (Fin 3) K))⁻¹ := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have h := mk_conj_eq_of_mul_eq_scalar_mul (hessPhi_mul_diagTau hτ hω h3 hτ0)
  rw [map_inv] at h
  exact h

theorem mk_hessPhi_conj_cycThree {τ : K} (hτ : τ ^ 3 = 1) (hω : τ ^ 2 + τ + 1 = 0)
    (h3 : (3 : K) ≠ 0) :
    ProjGenLinGroup.mk (hessPhi hω h3) * ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) *
        (ProjGenLinGroup.mk (hessPhi hω h3))⁻¹ =
      ProjGenLinGroup.mk (diagTau hτ) := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  exact mk_conj_eq_of_mul_eq_scalar_mul (hessPhi_mul_cycThree hτ hω h3 hτ0)

theorem mk_diagOneOneTau_conj_cycThree {τ : K} (hτ : τ ^ 3 = 1) :
    ProjGenLinGroup.mk (diagOneOneTau hτ) * ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) *
        (ProjGenLinGroup.mk (diagOneOneTau hτ))⁻¹ =
      ProjGenLinGroup.mk (cycThree : GL (Fin 3) K) * ProjGenLinGroup.mk (diagTau hτ) := by
  have hτ0 : τ ≠ 0 := by
    rintro rfl
    norm_num at hτ
  have h := mk_conj_eq_of_mul_eq_scalar_mul (diagOneOneTau_mul_cycThree hτ hτ0)
  rw [map_mul] at h
  exact h

end CFSG.RankThree.PartTwo.Sec4.Ronan148L
