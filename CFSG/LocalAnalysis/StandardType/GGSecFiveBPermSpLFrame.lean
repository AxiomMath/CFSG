module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveBPermSpFrameDefs
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthCoordBlock
import CFSG.LocalAnalysis.StandardType.GGLinearSemisimpleBasic
import CFSG.LocalAnalysis.StandardType.GGSixLSixFiveKnownComp
import CFSG.ClassicalInvolution.WeakCT.Amalgam
import CFSG.LocalAnalysis.SeitzReduction.LinearPilotOrthTorus

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.LieType.Universal
open CFSG.ClassicalInvolution.WeakCT (blockSL2)
open scoped MatrixGroups

variable {G : Type} [Group G]

private theorem diagGL_mul_inv_eq_of_conjSL_map_eq {m : ℕ} {F : Type} [Field F]
    {G : Type} [Group G] (σ : SL(m + 1, F) →* G)
    (hker : σ.ker ≤ Subgroup.center SL(m + 1, F))
    {d e : Fin (m + 1) → Fˣ}
    (h : ∀ u, σ (InnerDiagA.conjSL (InnerDiagA.diagGL d) u) =
      σ (InnerDiagA.conjSL (InnerDiagA.diagGL e) u)) :
    ∀ i j, d i * (d j)⁻¹ = e i * (e j)⁻¹ := by
  intro i j
  by_cases hij : i = j
  · subst hij
    simp
  · have hmem : InnerDiagA.conjSL (InnerDiagA.diagGL d)
        (Matrix.SpecialLinearGroup.transvection hij (1 : F)) *
      (InnerDiagA.conjSL (InnerDiagA.diagGL e)
        (Matrix.SpecialLinearGroup.transvection hij (1 : F)))⁻¹ ∈ σ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_inv, h]
      exact mul_inv_cancel _
    have hcen := hker hmem
    have ht : InnerDiagA.conjSL (InnerDiagA.diagGL d)
        (Matrix.SpecialLinearGroup.transvection hij (1 : F)) *
      (InnerDiagA.conjSL (InnerDiagA.diagGL e)
        (Matrix.SpecialLinearGroup.transvection hij (1 : F)))⁻¹
        = Matrix.SpecialLinearGroup.transvection hij
            ((d i : F) * (((d j)⁻¹ : Fˣ) : F) - (e i : F) * (((e j)⁻¹ : Fˣ) : F)) := by
      rw [InnerDiagA.conjSL_diagGL_transvection, InnerDiagA.conjSL_diagGL_transvection,
        Matrix.SpecialLinearGroup.transvection_inv, ← Matrix.SpecialLinearGroup.transvection_add]
      congr 1
      ring
    rw [ht] at hcen
    have hz := InnerDiagA.eq_zero_of_transvection_mem_center hij hcen
    apply Units.ext
    have hz' : (d i : F) * (((d j)⁻¹ : Fˣ) : F) = (e i : F) * (((e j)⁻¹ : Fˣ) : F) :=
      sub_eq_zero.mp hz
    simpa [Units.val_mul] using hz'

private theorem two_eigenvalue {F : Type} [Field F] {N : ℕ} (hN : 2 ≤ N) {c : Fin N} {ζ : Fˣ}
    (_hζ1 : (ζ : F) ≠ 1) (hζ2 : ((ζ⁻¹ : Fˣ) : F) ≠ (ζ : F))
    {u : Matrix (Fin N) (Fin N) F} (hu : u.det ≠ 0) {r : F}
    (h : Matrix.diagonal (fun i => if i = c then (ζ : F) else 1) * u *
      (Matrix.diagonal (fun i => if i = c then (ζ : F) else 1))⁻¹ = r • u) :
    r = 1 := by
  classical
  have hN1 : 1 < Fintype.card (Fin N) := by rw [Fintype.card_fin]; omega
  set D : Matrix (Fin N) (Fin N) F :=
    Matrix.diagonal (fun i => if i = c then (ζ : F) else 1) with hD
  have hDinv : D⁻¹ = Matrix.diagonal (fun i => if i = c then ((ζ⁻¹ : Fˣ) : F) else 1) := by
    apply Matrix.inv_eq_right_inv
    rw [hD, Matrix.diagonal_mul_diagonal]
    ext i j
    by_cases hij : i = j
    · subst hij
      by_cases hi : i = c
      · rw [Matrix.diagonal_apply_eq]
        simp [hi]
      · rw [Matrix.diagonal_apply_eq]
        simp [hi]
    · rw [Matrix.diagonal_apply_ne _ hij, Matrix.one_apply_ne hij]
  have hentry : ∀ i j, (D * u * D⁻¹) i j = (if i = c then (ζ : F) else 1) * u i j *
      (if j = c then ((ζ⁻¹ : Fˣ) : F) else 1) := by
    intro i j
    rw [hD, hDinv, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hEq : ∀ i j, (if i = c then (ζ : F) else 1) * u i j *
      (if j = c then ((ζ⁻¹ : Fˣ) : F) else 1) = r * u i j := by
    intro i j
    have := congrFun (congrFun h i) j
    simpa [hentry i j, Matrix.smul_apply, smul_eq_mul] using this
  obtain ⟨i, hi⟩ := Fintype.exists_ne_of_one_lt_card hN1 c
  obtain ⟨j, hj⟩ : ∃ j, u i j ≠ 0 := by
    by_contra h'
    exact hu (Matrix.det_eq_zero_of_row_eq_zero i fun j => by
      by_contra hx
      exact h' ⟨j, hx⟩)
  have hA : r = 1 ∨ r = ((ζ⁻¹ : Fˣ) : F) := by
    have h1 := hEq i j
    rw [if_neg hi] at h1
    by_cases hjc : j = c
    · right
      simp only [if_pos hjc] at h1
      rw [one_mul, mul_comm r (u i j)] at h1
      exact (mul_left_cancel₀ hj h1).symm
    · left
      simp only [if_neg hjc, mul_one, one_mul] at h1
      rw [mul_comm r (u i j)] at h1
      exact (mul_left_cancel₀ hj (by rw [mul_one]; exact h1)).symm
  obtain ⟨j', hj'⟩ := Fintype.exists_ne_of_one_lt_card hN1 c
  obtain ⟨i', hi'⟩ : ∃ i', u i' j' ≠ 0 := by
    by_contra h'
    exact hu (Matrix.det_eq_zero_of_column_eq_zero j' fun i => by
      by_contra hx
      exact h' ⟨i, hx⟩)
  have hB : r = 1 ∨ r = (ζ : F) := by
    have h1 := hEq i' j'
    simp only [if_neg hj', mul_one] at h1
    rw [mul_comm r (u i' j')] at h1
    by_cases hic : i' = c
    · right
      rw [if_pos hic, mul_comm (ζ : F) (u i' j')] at h1
      exact (mul_left_cancel₀ hi' h1).symm
    · left
      simp only [if_neg hic, one_mul] at h1
      exact (mul_left_cancel₀ hi' (by rw [mul_one]; exact h1)).symm
  by_contra hr
  have hA' : r = ((ζ⁻¹ : Fˣ) : F) := by rcases hA with h | h; exact absurd h hr; exact h
  have hB' : r = (ζ : F) := by rcases hB with h | h; exact absurd h hr; exact h
  exact hζ2 (hA'.symm.trans hB')


private theorem inv_mul_comm_of_mul_comm {n : ℕ} {F : Type} [Field F]
    {A P : Matrix (Fin n) (Fin n) F} (h : A * P = P * A) (hA : A.det ≠ 0) :
    A⁻¹ * P = P * A⁻¹ := by
  have hAA : A * A⁻¹ = 1 := Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hA)
  have hA'A : A⁻¹ * A = 1 := Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hA)
  calc A⁻¹ * P = A⁻¹ * P * (A * A⁻¹) := by rw [hAA, Matrix.mul_one]
    _ = A⁻¹ * (P * A) * A⁻¹ := by noncomm_ring
    _ = A⁻¹ * (A * P) * A⁻¹ := by rw [h]
    _ = (A⁻¹ * A) * P * A⁻¹ := by noncomm_ring
    _ = P * A⁻¹ := by rw [hA'A, Matrix.one_mul]

private theorem conjSL_diagGL_eq_self_of_isDiag {m : ℕ} {F : Type} [Field F]
    {d : Fin (m + 1) → Fˣ} {M : SL(m + 1, F)}
    (hM : (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F).IsDiag) :
    InnerDiagA.conjSL (InnerDiagA.diagGL d) M = M := by
  apply Subtype.ext
  ext i j
  rw [LinSemisimple.conjSL_diagGL_apply]
  by_cases hij : i = j
  · subst hij
    rw [mul_comm ((d i : F)) (M i i), mul_assoc, Units.mul_inv, mul_one]
  · rw [hM hij, mul_zero, zero_mul]

private theorem mul_conj_eq_conjSL_of_matrix_diagonal {m : ℕ} {F : Type} [Field F]
    {e : Fin (m + 1) → Fˣ} {M : SL(m + 1, F)}
    (hM : (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F) = Matrix.diagonal fun i => (e i : F))
    (hdet : Matrix.GeneralLinearGroup.det (InnerDiagA.diagGL e) = 1) (u : SL(m + 1, F)) :
    M * u * M⁻¹ = InnerDiagA.conjSL (InnerDiagA.diagGL e) u := by
  apply (InnerDiagA.slEquiv m F).injective
  rw [InnerDiagA.slEquiv_conjSL, map_mul, map_mul, map_inv]
  have hMsl : InnerDiagA.slEquiv m F M = ⟨InnerDiagA.diagGL e, hdet⟩ := by
    apply Subtype.ext
    apply Units.ext
    rw [InnerDiagA.coe_slEquiv, hM, InnerDiagA.coe_diagGL]
  rw [hMsl]
  apply Subtype.ext
  simp [MulAut.conjNormal_apply]

private theorem commutator_mem_blockSpecialLinear {n : ℕ} {F : Type} [Field F]
    {I : Finset (Fin n)} {M N : SL(n, F)}
    (hM : M ∈ CFSG.SeitzReduction.LinearPilot.blockDiagSL I)
    (hN : N ∈ CFSG.SeitzReduction.LinearPilot.blockDiagSL I)
    (hMd : ∀ i j, i ∉ I → j ∉ I → i ≠ j → (M : Matrix (Fin n) (Fin n) F) i j = 0)
    (hNd : ∀ i j, i ∉ I → j ∉ I → i ≠ j → (N : Matrix (Fin n) (Fin n) F) i j = 0) :
    M * N * M⁻¹ * N⁻¹ ∈ CFSG.SeitzReduction.LinearPilot.blockSpecialLinear I := by
  classical
  set P := CFSG.SeitzReduction.LinearPilot.blockComplProj (K := F) I with hP
  have hPval : P = Matrix.diagonal (fun i => if i ∈ I then (0 : F) else 1) := rfl
  have hPP : P * P = P := CFSG.SeitzReduction.LinearPilot.blockComplProj_mul_self I
  have hMP : (M : Matrix (Fin n) (Fin n) F) * P = P * (M : Matrix (Fin n) (Fin n) F) :=
    CFSG.SeitzReduction.LinearPilot.mem_blockDiagSL_iff_mul.mp hM
  have hNP : (N : Matrix (Fin n) (Fin n) F) * P = P * (N : Matrix (Fin n) (Fin n) F) :=
    CFSG.SeitzReduction.LinearPilot.mem_blockDiagSL_iff_mul.mp hN
  have hMmem := CFSG.SeitzReduction.LinearPilot.mem_blockDiagSL.mp hM
  have hNmem := CFSG.SeitzReduction.LinearPilot.mem_blockDiagSL.mp hN
  have hMPdiag : ((M : Matrix (Fin n) (Fin n) F) * P).IsDiag := by
    intro i j hij
    rw [hPval, Matrix.mul_diagonal]
    by_cases hj : j ∈ I
    · simp [hj]
    · by_cases hi : i ∈ I
      · rw [hMmem i j (by tauto)]
        simp [hj]
      · rw [hMd i j hi hj hij, zero_mul]
  have hNPdiag : ((N : Matrix (Fin n) (Fin n) F) * P).IsDiag := by
    intro i j hij
    rw [hPval, Matrix.mul_diagonal]
    by_cases hj : j ∈ I
    · simp [hj]
    · by_cases hi : i ∈ I
      · rw [hNmem i j (by tauto)]
        simp [hj]
      · rw [hNd i j hi hj hij, zero_mul]
  have hdiagComm : ((M : Matrix (Fin n) (Fin n) F) * P) * ((N : Matrix (Fin n) (Fin n) F) * P) =
      ((N : Matrix (Fin n) (Fin n) F) * P) * ((M : Matrix (Fin n) (Fin n) F) * P) := by
    rw [← hMPdiag.diagonal_diag, ← hNPdiag.diagonal_diag,
      Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext i
    exact mul_comm _ _
  have hMdet : (M : Matrix (Fin n) (Fin n) F).det ≠ 0 := by
    rw [M.2]; exact one_ne_zero
  have hNdet : (N : Matrix (Fin n) (Fin n) F).det ≠ 0 := by
    rw [N.2]; exact one_ne_zero
  have hMinvP : ((M : Matrix (Fin n) (Fin n) F))⁻¹ * P =
      P * ((M : Matrix (Fin n) (Fin n) F))⁻¹ :=
    inv_mul_comm_of_mul_comm hMP hMdet
  have hNinvP : ((N : Matrix (Fin n) (Fin n) F))⁻¹ * P =
      P * ((N : Matrix (Fin n) (Fin n) F))⁻¹ :=
    inv_mul_comm_of_mul_comm hNP hNdet
  have hMconj : (M : Matrix (Fin n) (Fin n) F) * P * ((M : Matrix (Fin n) (Fin n) F))⁻¹ = P := by
    rw [hMP, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hMdet),
      Matrix.mul_one]
  have hNconj : (N : Matrix (Fin n) (Fin n) F) * P * ((N : Matrix (Fin n) (Fin n) F))⁻¹ = P := by
    rw [hNP, Matrix.mul_assoc, Matrix.mul_nonsing_inv _ (isUnit_iff_ne_zero.mpr hNdet),
      Matrix.mul_one]
  have e1 : ((M : Matrix (Fin n) (Fin n) F) * P) * ((N : Matrix (Fin n) (Fin n) F) * P) *
      (((M : Matrix (Fin n) (Fin n) F))⁻¹ * P) * (((N : Matrix (Fin n) (Fin n) F))⁻¹ * P) =
      (M : Matrix (Fin n) (Fin n) F) * (N : Matrix (Fin n) (Fin n) F) *
        ((M : Matrix (Fin n) (Fin n) F))⁻¹ * ((N : Matrix (Fin n) (Fin n) F))⁻¹ * P := by
    set A := (M : Matrix (Fin n) (Fin n) F)
    set B := (N : Matrix (Fin n) (Fin n) F)
    set A' := A⁻¹
    set B' := B⁻¹
    have hA' : A' * P = P * A' := hMinvP
    have hB' : B' * P = P * B' := hNinvP
    have hAP := hMP
    have hBP := hNP
    change (A * P) * (B * P) * (A' * P) * (B' * P) = A * B * A' * B' * P
    calc (A * P) * (B * P) * (A' * P) * (B' * P)
        = A * (P * B) * P * (A' * P) * (B' * P) := by simp only [Matrix.mul_assoc]
      _ = A * (B * P) * P * (A' * P) * (B' * P) := by rw [← hBP]
      _ = A * B * (P * P) * (A' * P) * (B' * P) := by simp only [Matrix.mul_assoc]
      _ = A * B * P * (A' * P) * (B' * P) := by rw [hPP]
      _ = A * B * (P * A') * P * (B' * P) := by simp only [Matrix.mul_assoc]
      _ = A * B * (A' * P) * P * (B' * P) := by rw [← hA']
      _ = A * B * A' * (P * P) * (B' * P) := by simp only [Matrix.mul_assoc]
      _ = A * B * A' * P * (B' * P) := by rw [hPP]
      _ = A * B * A' * (P * B') * P := by simp only [Matrix.mul_assoc]
      _ = A * B * A' * (B' * P) * P := by rw [← hB']
      _ = A * B * A' * B' * (P * P) := by simp only [Matrix.mul_assoc]
      _ = A * B * A' * B' * P := by rw [hPP]
  have hMM : ((M : Matrix (Fin n) (Fin n) F) * P) *
      (((M : Matrix (Fin n) (Fin n) F))⁻¹ * P) = P := by
    rw [← Matrix.mul_assoc, hMconj, hPP]
  have hMM : ((M : Matrix (Fin n) (Fin n) F) * P) *
      (((M : Matrix (Fin n) (Fin n) F))⁻¹ * P) = P := by
    rw [← Matrix.mul_assoc, hMconj, hPP]
  have hkey : (M : Matrix (Fin n) (Fin n) F) * (N : Matrix (Fin n) (Fin n) F) *
      ((M : Matrix (Fin n) (Fin n) F))⁻¹ * ((N : Matrix (Fin n) (Fin n) F))⁻¹ * P = P := by
    rw [← e1, hdiagComm]
    calc ((((N : Matrix (Fin n) (Fin n) F) * P) * ((M : Matrix (Fin n) (Fin n) F) * P)) *
          (((M : Matrix (Fin n) (Fin n) F))⁻¹ * P)) *
          (((N : Matrix (Fin n) (Fin n) F))⁻¹ * P)
        = (((N : Matrix (Fin n) (Fin n) F) * P) *
            (((M : Matrix (Fin n) (Fin n) F) * P) *
              (((M : Matrix (Fin n) (Fin n) F))⁻¹ * P))) *
            (((N : Matrix (Fin n) (Fin n) F))⁻¹ * P) := by
          rw [← Matrix.mul_assoc ((N : Matrix (Fin n) (Fin n) F) * P)
            ((M : Matrix (Fin n) (Fin n) F) * P) (((M : Matrix (Fin n) (Fin n) F))⁻¹ * P)]
      _ = (((N : Matrix (Fin n) (Fin n) F) * P) * P) *
            (((N : Matrix (Fin n) (Fin n) F))⁻¹ * P) := by rw [hMM]
      _ = (((N : Matrix (Fin n) (Fin n) F) * (P * P)) *
            (((N : Matrix (Fin n) (Fin n) F))⁻¹ * P)) := by
          simp only [Matrix.mul_assoc]
      _ = (((N : Matrix (Fin n) (Fin n) F) * P) *
            (((N : Matrix (Fin n) (Fin n) F))⁻¹ * P)) := by rw [hPP]
      _ = (((N : Matrix (Fin n) (Fin n) F) * P * ((N : Matrix (Fin n) (Fin n) F))⁻¹) * P) := by
          rw [← Matrix.mul_assoc ((N : Matrix (Fin n) (Fin n) F) * P)
            ((N : Matrix (Fin n) (Fin n) F))⁻¹ P]
      _ = P := by rw [hNconj, hPP]
  have hPC : P * ((M : Matrix (Fin n) (Fin n) F) * (N : Matrix (Fin n) (Fin n) F) *
      ((M : Matrix (Fin n) (Fin n) F))⁻¹ * ((N : Matrix (Fin n) (Fin n) F))⁻¹) =
      ((M : Matrix (Fin n) (Fin n) F) * (N : Matrix (Fin n) (Fin n) F) *
      ((M : Matrix (Fin n) (Fin n) F))⁻¹ * ((N : Matrix (Fin n) (Fin n) F))⁻¹) * P := by
    set A := (M : Matrix (Fin n) (Fin n) F)
    set B := (N : Matrix (Fin n) (Fin n) F)
    set A' := A⁻¹
    set B' := B⁻¹
    have hA' : A' * P = P * A' := hMinvP
    have hB' : B' * P = P * B' := hNinvP
    have hAP := hMP
    have hBP := hNP
    change P * (A * B * A' * B') = A * B * A' * B' * P
    calc P * (A * B * A' * B')
        = (P * A) * B * A' * B' := by simp only [Matrix.mul_assoc]
      _ = (A * P) * B * A' * B' := by rw [← hAP]
      _ = A * (P * B) * A' * B' := by simp only [Matrix.mul_assoc]
      _ = A * (B * P) * A' * B' := by rw [← hBP]
      _ = A * B * (P * A') * B' := by simp only [Matrix.mul_assoc]
      _ = A * B * (A' * P) * B' := by rw [← hA']
      _ = A * B * A' * (P * B') := by simp only [Matrix.mul_assoc]
      _ = A * B * A' * (B' * P) := by rw [← hB']
      _ = A * B * A' * B' * P := by simp only [Matrix.mul_assoc]
  have hMinvmat : ((M⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
      ((M : Matrix (Fin n) (Fin n) F))⁻¹ := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.inv_def, M.2, Ring.inverse_one, one_smul]
  have hNinvmat : ((N⁻¹ : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
      ((N : Matrix (Fin n) (Fin n) F))⁻¹ := by
    rw [Matrix.SpecialLinearGroup.coe_inv, Matrix.inv_def, N.2, Ring.inverse_one, one_smul]
  have hsplit : (((M * N * M⁻¹ * N⁻¹) : SL(n, F)) : Matrix (Fin n) (Fin n) F) =
      (M : Matrix (Fin n) (Fin n) F) * (N : Matrix (Fin n) (Fin n) F) *
        ((M : Matrix (Fin n) (Fin n) F))⁻¹ * ((N : Matrix (Fin n) (Fin n) F))⁻¹ := by
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hMinvmat, hNinvmat]
  rw [CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear_iff_mul]
  refine ⟨?_, ?_⟩
  · rw [hsplit]; exact hkey
  · rw [hsplit]; exact hPC.trans hkey

private theorem exists_two_notMem_pair {N : ℕ} (hN : 4 ≤ N) (i j : Fin N) (hij : i ≠ j) :
    ∃ c d : Fin N, c ≠ d ∧ c ∉ ({i, j} : Finset (Fin N)) ∧ d ∉ ({i, j} : Finset (Fin N)) := by
  classical
  have hcard : ({i, j} : Finset (Fin N)).card = 2 := Finset.card_pair hij
  obtain ⟨c, -, hc⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := ({i, j} : Finset (Fin N))) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin, hcard]; omega)
  have hcard2 : (insert c ({i, j} : Finset (Fin N))).card = 3 := by
    rw [Finset.card_insert_of_notMem hc, hcard]
  obtain ⟨d, -, hd⟩ := Finset.exists_mem_notMem_of_card_lt_card
    (s := insert c ({i, j} : Finset (Fin N))) (t := Finset.univ)
    (by rw [Finset.card_univ, Fintype.card_fin, hcard2]; omega)
  refine ⟨c, d, ?_, hc, ?_⟩
  · intro hcd
    apply hd
    rw [hcd]
    exact Finset.mem_insert_self _ _
  · intro hdmem
    exact hd (Finset.mem_insert_of_mem hdmem)

private theorem prod_pair_diag {F : Type} [Field F] {N : ℕ} {c d : Fin N} (hcd : c ≠ d)
    (ζ : Fˣ) :
    ∏ i, (if i = c then (ζ : F) else if i = d then ((ζ⁻¹ : Fˣ) : F) else 1) = 1 := by
  classical
  rw [show (∏ i, (if i = c then (ζ : F) else if i = d then ((ζ⁻¹ : Fˣ) : F) else 1)) =
      (if c = c then (ζ : F) else if c = d then ((ζ⁻¹ : Fˣ) : F) else 1) *
        ∏ i ∈ Finset.univ \ {c},
          (if i = c then (ζ : F) else if i = d then ((ζ⁻¹ : Fˣ) : F) else 1) from
    Finset.prod_eq_mul_prod_diff_singleton c _ (by simp)]
  have hdmem : d ∈ Finset.univ \ {c} := by
    simp [hcd.symm]
  have h1 : ∏ i ∈ Finset.univ \ {c},
      (if i = c then (ζ : F) else if i = d then ((ζ⁻¹ : Fˣ) : F) else 1) =
      ((ζ⁻¹ : Fˣ) : F) := by
    refine (Finset.prod_eq_single d ?_ ?_).trans ?_
    · intro b hb hbd
      have hbc : b ≠ c := by
        intro h
        exact (Finset.mem_sdiff.mp hb).2 (by simp [h])
      rw [if_neg hbc, if_neg hbd]
    · intro hdnot
      exact absurd hdmem hdnot
    · simp [hcd.symm]
  rw [h1, if_pos rfl, Units.val_inv_eq_inv_val]
  exact mul_inv_cancel₀ (Units.ne_zero ζ)

private theorem coe_blockSL2_matrix {F : Type} [Field F] {m : ℕ} (a : Fin m) (A : SL(2, F)) :
    ((blockSL2 F m a A : Matrix (Fin (m + 1)) (Fin (m + 1)) F)) =
      CFSG.ClassicalInvolution.Phan.blockMat (m + 1) a.val (A : Matrix (Fin 2) (Fin 2) F) :=
  rfl

private theorem isDiag_blockSL2_torusHom {F : Type} [Field F] {m : ℕ} (a : Fin m) (ζ : Fˣ) :
    ((blockSL2 F m a (CFSG.ClassicalInvolution.WeakCT.torusHom F ζ) : Matrix (Fin (m + 1)) (Fin (m + 1)) F)).IsDiag := by
  classical
  intro i j hij
  have hmat : (CFSG.ClassicalInvolution.WeakCT.torusHom F ζ : Matrix (Fin 2) (Fin 2) F) = Matrix.diagonal ![((ζ : F)), (((ζ⁻¹ : Fˣ) : F))] := by
    rw [CFSG.ClassicalInvolution.WeakCT.coe_torusHom]
    ext x y
    fin_cases x <;> fin_cases y <;> simp
  rw [coe_blockSL2_matrix, CFSG.ClassicalInvolution.Phan.blockMat_apply, hmat]
  split_ifs with h
  · rw [Matrix.diagonal_apply]
    have hne : (⟨i.val - a.val, by omega⟩ : Fin 2) ≠
        ⟨j.val - a.val, by omega⟩ := by
      intro heq
      apply hij
      apply Fin.ext
      have hv := congrArg Fin.val heq
      simp only at hv
      omega
    rw [if_neg hne]
  · simp [Matrix.one_apply_ne hij]

private theorem blockSL2_torusHom_castSucc {F : Type} [Field F] {m : ℕ} (a : Fin m) (ζ : Fˣ) :
    ((blockSL2 F m a (CFSG.ClassicalInvolution.WeakCT.torusHom F ζ) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F)) a.castSucc a.castSucc = (ζ : F) := by
  rw [coe_blockSL2_matrix, CFSG.ClassicalInvolution.Phan.blockMat_apply,
    CFSG.ClassicalInvolution.WeakCT.coe_torusHom]
  rw [dif_pos (by simp [Fin.castSucc])]
  have hidx : (⟨a.castSucc.val - a.val, by simp [Fin.castSucc]⟩ : Fin 2) = 0 := by
    apply Fin.ext
    simp [Fin.castSucc]
  rw [hidx]
  simp

private theorem blockSL2_torusHom_succ {F : Type} [Field F] {m : ℕ} (a : Fin m) (ζ : Fˣ) :
    ((blockSL2 F m a (CFSG.ClassicalInvolution.WeakCT.torusHom F ζ) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F)) a.succ a.succ = (((ζ⁻¹ : Fˣ) : F)) := by
  rw [coe_blockSL2_matrix, CFSG.ClassicalInvolution.Phan.blockMat_apply,
    CFSG.ClassicalInvolution.WeakCT.coe_torusHom]
  rw [dif_pos (by simp [Fin.succ])]
  have hidx : (⟨a.succ.val - a.val, by simp [Fin.succ]⟩ : Fin 2) = 1 := by
    apply Fin.ext
    simp [Fin.succ]
  rw [hidx]
  simp

private theorem mem_pair_of_block {m : ℕ} {a : Fin m} {i : Fin (m + 1)}
    (h : a.val ≤ i.val ∧ i.val < a.val + 2) :
    i ∈ ({a.castSucc, a.succ} : Finset (Fin (m + 1))) := by
  rw [Finset.mem_insert, Finset.mem_singleton]
  have hi : i.val = a.val ∨ i.val = a.val + 1 := by omega
  rcases hi with h' | h'
  · left
    apply Fin.ext
    simpa [Fin.castSucc] using h'
  · right
    apply Fin.ext
    simpa [Fin.succ] using h'

private theorem block_of_mem_pair {m : ℕ} {a : Fin m} {i : Fin (m + 1)}
    (h : i ∈ ({a.castSucc, a.succ} : Finset (Fin (m + 1)))) :
    a.val ≤ i.val ∧ i.val < a.val + 2 := by
  simp only [Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with h | h
  · subst h
    simp [Fin.castSucc]
  · subst h
    simp [Fin.succ]

private theorem range_blockSL2_le_blockSpecialLinear {F : Type} [Field F] {m : ℕ} (a : Fin m) :
    (blockSL2 F m a).range ≤
      CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := F)
        ({a.castSucc, a.succ} : Finset (Fin (m + 1))) := by
  rintro _ ⟨A, rfl⟩
  rw [CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear]
  intro i j hij
  rw [coe_blockSL2_matrix, CFSG.ClassicalInvolution.Phan.blockMat_apply]
  by_cases h : (a.val ≤ i.val ∧ i.val < a.val + 2) ∧ (a.val ≤ j.val ∧ j.val < a.val + 2)
  · rw [dif_pos h]
    exfalso
    rcases hij with hi | hj
    · exact hi (mem_pair_of_block h.1)
    · exact hj (mem_pair_of_block h.2)
  · exact dif_neg h

private theorem blockSpecialLinear_le_range_blockSL2 {F : Type} [Field F] {m : ℕ} (a : Fin m) :
    CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := F)
        ({a.castSucc, a.succ} : Finset (Fin (m + 1))) ≤ (blockSL2 F m a).range := by
  classical
  intro M hM
  have hm : a.val + 2 ≤ m + 1 := by omega
  let A : Matrix (Fin 2) (Fin 2) F := fun x y =>
    (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F)
      (CFSG.ClassicalInvolution.Phan.blockIdx a.val hm x)
      (CFSG.ClassicalInvolution.Phan.blockIdx a.val hm y)
  have hAmat : CFSG.ClassicalInvolution.Phan.blockMat (m + 1) a.val A =
      (M : Matrix (Fin (m + 1)) (Fin (m + 1)) F) := by
    ext i j
    by_cases hb : (a.val ≤ i.val ∧ i.val < a.val + 2) ∧ (a.val ≤ j.val ∧ j.val < a.val + 2)
    · rw [CFSG.ClassicalInvolution.Phan.blockMat_apply, dif_pos hb]
      simp only [A]
      have h1 : CFSG.ClassicalInvolution.Phan.blockIdx a.val hm
          (⟨i.val - a.val, by omega⟩ : Fin 2) = i := by
        apply Fin.ext
        simp [CFSG.ClassicalInvolution.Phan.blockIdx]
        omega
      have h2 : CFSG.ClassicalInvolution.Phan.blockIdx a.val hm
          (⟨j.val - a.val, by omega⟩ : Fin 2) = j := by
        apply Fin.ext
        simp [CFSG.ClassicalInvolution.Phan.blockIdx]
        omega
      rw [h1, h2]
    · rw [CFSG.ClassicalInvolution.Phan.blockMat_apply, dif_neg hb]
      rw [CFSG.SeitzReduction.LinearPilot.mem_blockSpecialLinear.mp hM i j ?_]
      rcases not_and_or.mp hb with hi | hj
      · left
        intro hiI
        exact hi (block_of_mem_pair hiI)
      · right
        intro hjI
        exact hj (block_of_mem_pair hjI)
  have hdet : A.det = 1 := by
    have h1 := M.2
    rw [← hAmat, CFSG.ClassicalInvolution.Phan.det_blockMat hm] at h1
    exact h1
  let B : Matrix.SpecialLinearGroup (Fin 2) F := ⟨A, hdet⟩
  refine ⟨B, ?_⟩
  apply Subtype.ext
  rw [coe_blockSL2_matrix]
  exact hAmat

private theorem blockSpecialLinear_pair_eq_range_blockSL2 {F : Type} [Field F] {m : ℕ} (a : Fin m) :
    CFSG.SeitzReduction.LinearPilot.blockSpecialLinear (K := F)
        ({a.castSucc, a.succ} : Finset (Fin (m + 1))) = (blockSL2 F m a).range :=
  le_antisymm (blockSpecialLinear_le_range_blockSL2 a) (range_blockSL2_le_blockSpecialLinear a)

private theorem b1_conjSL_diagGL_blockSL2_eq_self {F : Type} [Field F] {m : ℕ}
    {d : Fin (m + 1) → Fˣ} {a : Fin m} (hd : d a.castSucc = d a.succ) (A : SL(2, F)) :
    InnerDiagA.conjSL (InnerDiagA.diagGL d) (blockSL2 F m a A) = blockSL2 F m a A := by
  apply Subtype.ext
  ext i j
  rw [InnerDiagA.coe_conjSL, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL_inv,
    Matrix.mul_diagonal, Matrix.diagonal_mul, coe_blockSL2_matrix,
    CFSG.ClassicalInvolution.Phan.blockMat_apply]
  have hpair : ∀ k, k ∈ ({a.castSucc, a.succ} : Finset (Fin (m + 1))) → d k = d a.castSucc := by
    intro k hk
    rw [Finset.mem_insert, Finset.mem_singleton] at hk
    rcases hk with rfl | rfl
    · rfl
    · exact hd.symm
  by_cases hb : (a.val ≤ i.val ∧ i.val < a.val + 2) ∧
      (a.val ≤ j.val ∧ j.val < a.val + 2)
  · rw [dif_pos hb, hpair i (mem_pair_of_block hb.1), hpair j (mem_pair_of_block hb.2),
      mul_right_comm, Units.mul_inv, one_mul]
  · rw [dif_neg hb]
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq, mul_one, Units.mul_inv]
    · rw [Matrix.one_apply_ne hij, mul_zero, zero_mul]

private theorem lframe_zeta_sq_ne_one {p f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ} (hχ : Function.Injective χ) :
    ((χ (Multiplicative.ofAdd 1) : (GaloisField 2 f)ˣ) : GaloisField 2 f) ^ 2 ≠ 1 := by
  intro h
  have hζ2 : (χ (Multiplicative.ofAdd 1)) ^ 2 = 1 := by
    apply Units.ext
    simpa using h
  have hsq : (Multiplicative.ofAdd (1 : ZMod p)) ^ 2 =
      Multiplicative.ofAdd (2 : ZMod p) := by
    rw [pow_two, ← ofAdd_add]
    congr 1
    ring
  have hχ2 : χ (Multiplicative.ofAdd (2 : ZMod p)) = 1 := by
    rw [← hsq, map_pow, hζ2]
  have h2 : (2 : ZMod p) = 0 := by
    have hof : Multiplicative.ofAdd (2 : ZMod p) = 1 := by
      refine hχ ?_
      simpa using hχ2
    exact ofAdd_eq_one.mp hof
  have hpdvd2 : p ∣ 2 := (ZMod.natCast_eq_zero_iff 2 p).mp h2
  exact hp2 ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).mp hpdvd2)

private theorem lframe_x_mem {p n r f : ℕ} {Bs L : Subgroup G} {x : G} (hxB : x ∈ Bs)
    (hxL : L ≤ Subgroup.centralizer {x})
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {σ : SL(r + 2, GaloisField 2 f) →* G} {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpLFrame Bs L eta π σ χ) (i j : Fin (r + 2)) :
    x ∈ ggBsCoordEq Bs eta (π i) (π j) := by
  have hxcomm : ∀ u : SL(r + 2, GaloisField 2 f), x * σ u = σ u * x := by
    intro u
    have hu : σ u ∈ L := by
      rw [← hF.2.1]
      exact ⟨u, rfl⟩
    exact (Subgroup.mem_centralizer_iff.mp (hxL hu)) x (by simp)
  have hconj : ∀ u : SL(r + 2, GaloisField 2 f),
      σ (InnerDiagA.conjSL (InnerDiagA.diagGL fun m => χ (eta ⟨x, hxB⟩ (π m))) u) =
        σ (InnerDiagA.conjSL (InnerDiagA.diagGL fun _ =>
          (1 : (GaloisField 2 f)ˣ)) u) := by
    intro u
    have hfr := hF.2.2.2 ⟨x, hxB⟩ u
    have h1 : σ (InnerDiagA.conjSL (InnerDiagA.diagGL fun m =>
        χ (eta ⟨x, hxB⟩ (π m))) u) = σ u := by
      rw [← hfr]
      change x * σ u * x⁻¹ = σ u
      rw [hxcomm u, mul_assoc, mul_inv_cancel, mul_one]
    have h2 : σ (InnerDiagA.conjSL (InnerDiagA.diagGL fun _ =>
        (1 : (GaloisField 2 f)ˣ)) u) = σ u := by
      congr 1
      apply Subtype.ext
      rw [InnerDiagA.coe_conjSL, InnerDiagA.coe_diagGL, InnerDiagA.coe_diagGL_inv]
      simp
    rw [h1, h2]
  have hd := diagGL_mul_inv_eq_of_conjSL_map_eq (m := r + 1) σ hF.1
    (d := fun m => χ (eta ⟨x, hxB⟩ (π m)))
    (e := fun _ => (1 : (GaloisField 2 f)ˣ)) hconj
  refine (coe_mem_ggBsCoordEq (b := ⟨x, hxB⟩)).mpr (hF.2.2.1 ?_)
  have h := hd i j
  simp only [inv_one, mul_one] at h
  exact mul_inv_eq_one.mp h

private theorem lframe_torus_mem {p n r f : ℕ} {Bs L : Subgroup G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {σ : SL(r + 2, GaloisField 2 f) →* G} {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpLFrame Bs L eta π σ χ) (a : Fin (r + 1)) :
    σ (blockSL2 (GaloisField 2 f) (r + 1) a (CFSG.ClassicalInvolution.WeakCT.torusHom
      (GaloisField 2 f) (χ (Multiplicative.ofAdd 1)))) ∈ Bs := by
  set t := σ (blockSL2 (GaloisField 2 f) (r + 1) a
    (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f)
      (χ (Multiplicative.ofAdd 1)))) with ht
  have htcent : t ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hfr := hF.2.2.2 ⟨b, hb⟩
      (blockSL2 (GaloisField 2 f) (r + 1) a
        (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f)
          (χ (Multiplicative.ofAdd 1))))
    rw [conjSL_diagGL_eq_self_of_isDiag (m := r + 1) (d := fun m => χ (eta ⟨b, hb⟩ (π m)))
      (isDiag_blockSL2_torusHom a (χ (Multiplicative.ofAdd 1)))] at hfr
    have hconj : b * t * b⁻¹ = t := hfr
    calc b * t = (b * t * b⁻¹) * b := by group
      _ = t * b := by rw [hconj]
  have hζp : (χ (Multiplicative.ofAdd 1)) ^ p = 1 := by
    rw [← map_pow, ← ofAdd_nsmul, nsmul_eq_mul, ZMod.natCast_self, zero_mul, ofAdd_zero,
      map_one]
  have htpow : t ^ p = 1 := by
    rw [ht, ← map_pow, ← map_pow, ← map_pow, hζp]
    simp
  exact hBs t htcent htpow

private theorem b2_blockSL2_torusHom_apply_self {F : Type} [Field F] {m : ℕ} (a : Fin m) (ζ : Fˣ)
    {i : Fin (m + 1)} (hi : i ∉ ({a.castSucc, a.succ} : Finset (Fin (m + 1)))) :
    ((blockSL2 F m a (CFSG.ClassicalInvolution.WeakCT.torusHom F ζ) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F)) i i = 1 := by
  rw [coe_blockSL2_matrix, CFSG.ClassicalInvolution.Phan.blockMat_apply_of_not_mem_left _
    (fun h => hi (mem_pair_of_block h)) i, Matrix.one_apply_eq]

private theorem b2_blockSL2_torusHom_eq_diagonal {F : Type} [Field F] {m : ℕ} (a : Fin m) (ζ : Fˣ) :
    ((blockSL2 F m a (CFSG.ClassicalInvolution.WeakCT.torusHom F ζ) :
      Matrix (Fin (m + 1)) (Fin (m + 1)) F)) =
      Matrix.diagonal (fun i =>
        ((if i = a.castSucc then ζ else if i = a.succ then ζ⁻¹ else 1 : Fˣ) : F)) := by
  have hD := isDiag_blockSL2_torusHom a ζ
  rw [← hD.diagonal_diag]
  congr 1
  funext i
  rw [Matrix.diag_apply]
  by_cases h1 : i = a.castSucc
  · rw [h1, blockSL2_torusHom_castSucc, if_pos rfl]
  · by_cases h2 : i = a.succ
    · rw [if_neg h1, if_pos h2, h2, blockSL2_torusHom_succ]
    · rw [if_neg h1, if_neg h2]
      exact b2_blockSL2_torusHom_apply_self a ζ (by simp [h1, h2])

private theorem b2_det_diagGL_of_pair {F : Type} [Field F] {m : ℕ} {c d : Fin (m + 1)}
    (hcd : c ≠ d) (ζ : Fˣ) :
    Matrix.GeneralLinearGroup.det
      (InnerDiagA.diagGL (fun i : Fin (m + 1) =>
        if i = c then ζ else if i = d then ζ⁻¹ else 1)) = 1 := by
  apply Units.ext
  rw [Matrix.GeneralLinearGroup.val_det_apply, InnerDiagA.coe_diagGL, Matrix.det_diagonal,
    Units.val_one, ← prod_pair_diag hcd ζ]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h1 : i = c
  · simp [h1]
  · by_cases h2 : i = d <;> simp [h1, h2, Ne.symm hcd]

private theorem b2_torus_coord_diff {p n r f : ℕ} [Fact p.Prime] {Bs L : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {σ : SL(r + 2, GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpLFrame Bs L eta π σ χ) (a : Fin (r + 1)) (b : ↥Bs)
    (hb : (b : G) = σ (blockSL2 (GaloisField 2 f) (r + 1) a
      (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f)
        (χ (Multiplicative.ofAdd 1))))) :
    Multiplicative.toAdd (eta b (π a.castSucc)) -
      Multiplicative.toAdd (eta b (π a.succ)) = 2 := by
  classical
  let ζ : (GaloisField 2 f)ˣ := χ (Multiplicative.ofAdd 1)
  let M : SL(r + 2, GaloisField 2 f) := blockSL2 (GaloisField 2 f) (r + 1) a
    (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) ζ)
  let e_diag : Fin (r + 2) → (GaloisField 2 f)ˣ :=
    fun i => if i = a.castSucc then ζ else if i = a.succ then ζ⁻¹ else 1
  have hdiag : ((M : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f))) =
      Matrix.diagonal (fun i => (e_diag i : GaloisField 2 f)) :=
    b2_blockSL2_torusHom_eq_diagonal a ζ
  have hdet : Matrix.GeneralLinearGroup.det (InnerDiagA.diagGL e_diag) = 1 :=
    b2_det_diagGL_of_pair (Fin.castSucc_lt_succ (i := a)).ne ζ
  have haction : ∀ u : SL(r + 2, GaloisField 2 f),
      σ (InnerDiagA.conjSL (InnerDiagA.diagGL e_diag) u) =
      σ (InnerDiagA.conjSL (InnerDiagA.diagGL (fun m => χ (eta b (π m)))) u) := by
    intro u
    rw [← hF.2.2.2 b u]
    have h1 : (b : G) * σ u * (b : G)⁻¹ = σ (M * u * M⁻¹) := by
      rw [hb, map_mul, map_mul, map_inv]
    rw [h1, mul_conj_eq_conjSL_of_matrix_diagonal hdiag hdet u]
  have hd := diagGL_mul_inv_eq_of_conjSL_map_eq (m := r + 1) σ hF.1 haction
  have hd' := hd a.castSucc a.succ
  have hL : e_diag a.castSucc * (e_diag a.succ)⁻¹ = ζ * ζ := by
    have h1 : e_diag a.castSucc = ζ := if_pos rfl
    have h2 : e_diag a.succ = ζ⁻¹ := by
      show (if a.succ = a.castSucc then ζ else if a.succ = a.succ then ζ⁻¹ else 1) = ζ⁻¹
      rw [if_neg (Fin.castSucc_lt_succ (i := a)).ne', if_pos rfl]
    rw [h1, h2, inv_inv]
  have hχeq : χ (eta b (π a.castSucc) * (eta b (π a.succ))⁻¹) =
      χ (Multiplicative.ofAdd ((1 : ZMod p) + 1)) := by
    calc χ (eta b (π a.castSucc) * (eta b (π a.succ))⁻¹)
        = χ (eta b (π a.castSucc)) * (χ (eta b (π a.succ)))⁻¹ := by
          rw [map_mul]
          exact congrArg (fun u => χ (eta b (π a.castSucc)) * u)
            (map_inv χ (eta b (π a.succ)))
      _ = e_diag a.castSucc * (e_diag a.succ)⁻¹ := hd'.symm
      _ = ζ * ζ := hL
      _ = χ (Multiplicative.ofAdd ((1 : ZMod p) + 1)) := by
          rw [ofAdd_add, map_mul]
  have hprod : eta b (π a.castSucc) * (eta b (π a.succ))⁻¹ =
      Multiplicative.ofAdd ((1 : ZMod p) + 1) := hF.2.2.1 hχeq
  have htoAdd := congrArg Multiplicative.toAdd hprod
  rw [toAdd_mul, toAdd_inv, toAdd_ofAdd] at htoAdd
  rw [show (2 : ZMod p) = 1 + 1 from by norm_num, sub_eq_add_neg]
  exact htoAdd

private theorem b2_coord_eq_of_diff_two {p n : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    (b_e b_t : ↥Bs) (i j : Fin n)
    (hkey : Multiplicative.toAdd (eta b_t i) - Multiplicative.toAdd (eta b_t j) = 2) :
    ∃ k : ℤ, eta (b_e * b_t ^ (-k)) i = eta (b_e * b_t ^ (-k)) j := by
  classical
  have hNeZero : NeZero p := ⟨(Fact.out : p.Prime).ne_zero⟩
  have h2 : (2 : ZMod p) ≠ 0 := Ring.two_ne_zero (by rwa [ZMod.ringChar_zmod_n])
  let δ : ZMod p := Multiplicative.toAdd (eta b_e i) - Multiplicative.toAdd (eta b_e j)
  let k : ℤ := ((δ / 2 : ZMod p).val : ℤ)
  refine ⟨k, ?_⟩
  have hk : (k : ZMod p) * 2 = δ := by
    have hkval : k = ((δ / 2 : ZMod p).val : ℤ) := rfl
    rw [hkval, Int.cast_natCast, ZMod.natCast_zmod_val, div_mul_cancel₀ δ h2]
  have hbh : eta (b_e * b_t ^ (-k)) = eta b_e * (eta b_t) ^ (-k) := by
    rw [map_mul, map_zpow]
    rfl
  have hpt (m : Fin n) : Multiplicative.toAdd (eta (b_e * b_t ^ (-k)) m) =
      Multiplicative.toAdd (eta b_e m) - (k : ZMod p) * Multiplicative.toAdd (eta b_t m) := by
    rw [hbh]
    rw [Pi.mul_apply, Pi.pow_apply, toAdd_mul, toAdd_zpow, zsmul_eq_mul, Int.cast_neg, neg_mul]
    ring
  apply Multiplicative.toAdd.injective
  rw [hpt i, hpt j]
  have hδ : Multiplicative.toAdd (eta b_e i) - Multiplicative.toAdd (eta b_e j) = δ := rfl
  linear_combination hδ - (k : ZMod p) * hkey - hk

private theorem lframe_gen {p n r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2) {Bs L : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {σ : SL(r + 2, GaloisField 2 f) →* G} {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpLFrame Bs L eta π σ χ) (a : Fin (r + 1))
    (htB : σ (blockSL2 (GaloisField 2 f) (r + 1) a (CFSG.ClassicalInvolution.WeakCT.torusHom
      (GaloisField 2 f) (χ (Multiplicative.ofAdd 1)))) ∈ Bs) :
    ∀ e ∈ Bs, ∃ h ∈ ggBsCoordEq Bs eta (π a.castSucc) (π a.succ), ∃ k : ℤ,
      e = h * σ (blockSL2 (GaloisField 2 f) (r + 1) a (CFSG.ClassicalInvolution.WeakCT.torusHom
        (GaloisField 2 f) (χ (Multiplicative.ofAdd 1)))) ^ k := by
  classical
  let ζ : (GaloisField 2 f)ˣ := χ (Multiplicative.ofAdd 1)
  let M : SL(r + 2, GaloisField 2 f) := blockSL2 (GaloisField 2 f) (r + 1) a
    (CFSG.ClassicalInvolution.WeakCT.torusHom (GaloisField 2 f) ζ)
  let t : G := σ M
  let b_t : ↥Bs := ⟨t, htB⟩
  have hkey : Multiplicative.toAdd (eta b_t (π a.castSucc)) -
      Multiplicative.toAdd (eta b_t (π a.succ)) = 2 :=
    b2_torus_coord_diff hF a b_t (by rfl)
  intro e he
  let b_e : ↥Bs := ⟨e, he⟩
  obtain ⟨k, hk⟩ := b2_coord_eq_of_diff_two hp2 b_e b_t (π a.castSucc) (π a.succ) hkey
  refine ⟨((b_e * b_t ^ (-k) : ↥Bs) : G), ?_, k, ?_⟩
  · rw [coe_mem_ggBsCoordEq]
    exact hk
  · have hcoe : ((b_e * b_t ^ (-k) : ↥Bs) : G) = e * t ^ (-k) := by
      rw [Subgroup.coe_mul, Subgroup.coe_zpow]
    rw [hcoe, mul_assoc, ← zpow_add, neg_add_cancel, zpow_zero, mul_one]

private theorem lframe_range_le_centralizer {p n r f : ℕ} {Bs L : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {σ : SL(r + 2, GaloisField 2 f) →* G} {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpLFrame Bs L eta π σ χ) (a : Fin (r + 1)) :
    (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) a)).range ≤
      Subgroup.centralizer (ggBsCoordEq Bs eta (π a.castSucc) (π a.succ) : Set G) := by
  intro g hg
  obtain ⟨A, rfl⟩ := MonoidHom.mem_range.mp hg
  rw [Subgroup.mem_centralizer_iff]
  intro h hh
  have hhBs : h ∈ Bs := ggBsCoordEq_le _ _ hh
  have hcoord : eta ⟨h, hhBs⟩ (π a.castSucc) = eta ⟨h, hhBs⟩ (π a.succ) :=
    (coe_mem_ggBsCoordEq (b := ⟨h, hhBs⟩)).mp hh
  have hd : (fun m => χ (eta ⟨h, hhBs⟩ (π m))) a.castSucc =
      (fun m => χ (eta ⟨h, hhBs⟩ (π m))) a.succ :=
    congrArg χ hcoord
  have hfr := hF.2.2.2 ⟨h, hhBs⟩ (blockSL2 (GaloisField 2 f) (r + 1) a A)
  rw [b1_conjSL_diagGL_blockSL2_eq_self (m := r + 1)
    (d := fun m => χ (eta ⟨h, hhBs⟩ (π m))) hd A] at hfr
  have hconj : h * σ (blockSL2 (GaloisField 2 f) (r + 1) a A) * h⁻¹ =
      σ (blockSL2 (GaloisField 2 f) (r + 1) a A) := hfr
  calc h * σ (blockSL2 (GaloisField 2 f) (r + 1) a A)
      = (h * σ (blockSL2 (GaloisField 2 f) (r + 1) a A) * h⁻¹) * h := by group
    _ = σ (blockSL2 (GaloisField 2 f) (r + 1) a A) * h := by rw [hconj]

private theorem b3_lframe_chi_ofAdd_one_pow {p f : ℕ} [Fact p.Prime]
    (χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ) :
    (χ (Multiplicative.ofAdd 1)) ^ p = 1 := by
  have h : (Multiplicative.ofAdd (1 : ZMod p)) ^ p = 1 := by
    rw [← ofAdd_nsmul]
    rw [show p • (1 : ZMod p) = 0 from by
      rw [nsmul_eq_mul, mul_one, ZMod.natCast_self]]
    rfl
  rw [← map_pow, h, map_one]

private theorem b3_lframe_diagSL_pow_eq_one {r p : ℕ} {F : Type} [Field F]
    {d : Fin (r + 2) → Fˣ} (hd : ∀ i, (d i : F) ^ p = 1)
    {M : SL(r + 2, F)}
    (hM : (M : Matrix (Fin (r + 2)) (Fin (r + 2)) F) =
      Matrix.diagonal (fun i => (d i : F))) :
    M ^ p = 1 := by
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, hM, Matrix.diagonal_pow]
  rw [show ((fun i => (d i : F)) ^ p) = fun _ => 1 from by funext i; exact hd i,
    Matrix.diagonal_one]
  simp

private theorem b3_lframe_isDiag_mem_centralizer {r f : ℕ}
    {G : Type} [Group G] {Bs L : Subgroup G} {n p : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {σ : SL(r + 2, GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpLFrame Bs L eta π σ χ)
    {M : SL(r + 2, GaloisField 2 f)}
    (hM : (M : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f)).IsDiag) :
    σ M ∈ Subgroup.centralizer (Bs : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro b hb
  have hconj : InnerDiagA.conjSL (InnerDiagA.diagGL
      (fun k => χ (eta ⟨b, hb⟩ (π k)))) M = M :=
    conjSL_diagGL_eq_self_of_isDiag (m := r + 1) hM
  have hframe := hF.2.2.2 ⟨b, hb⟩ M
  rw [hconj] at hframe
  calc b * σ M = b * σ M * b⁻¹ * b := by group
    _ = σ M * b := by rw [hframe]

private theorem b3_lframe_mem_Bs_of_diagSL {r p f : ℕ} [Fact p.Prime]
    {G : Type} [Group G] {Bs L : Subgroup G} {n : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {σ : SL(r + 2, GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpLFrame Bs L eta π σ χ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    {ev : Fin (r + 2) → (GaloisField 2 f)ˣ} {M : SL(r + 2, GaloisField 2 f)}
    (hM : (M : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f)) =
      Matrix.diagonal (fun i => (ev i : GaloisField 2 f)))
    (hevp : ∀ i, (ev i : GaloisField 2 f) ^ p = 1) :
    σ M ∈ Bs := by
  have hdiag : (M : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f)).IsDiag := by
    rw [hM]
    exact Matrix.isDiag_diagonal _
  have hcent : σ M ∈ Subgroup.centralizer (Bs : Set G) :=
    b3_lframe_isDiag_mem_centralizer hF hdiag
  have hpow : (σ M) ^ p = 1 := by
    rw [← map_pow, b3_lframe_diagSL_pow_eq_one hevp hM, map_one]
  exact hBs (σ M) hcent hpow

private theorem b3_lframe_conjSL_diag_eq_of_frame {r f : ℕ}
    {G : Type} [Group G] {Bs L : Subgroup G} {n p : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {σ : SL(r + 2, GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpLFrame Bs L eta π σ χ)
    {ev : Fin (r + 2) → (GaloisField 2 f)ˣ} {M : SL(r + 2, GaloisField 2 f)}
    (hM : (M : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f)) =
      Matrix.diagonal (fun i => (ev i : GaloisField 2 f)))
    (hdet : Matrix.GeneralLinearGroup.det (InnerDiagA.diagGL ev) = 1)
    (hB : σ M ∈ Bs) :
    ∀ u : SL(r + 2, GaloisField 2 f),
      σ (InnerDiagA.conjSL (InnerDiagA.diagGL ev) u) =
        σ (InnerDiagA.conjSL (InnerDiagA.diagGL
          (fun k => χ (eta ⟨σ M, hB⟩ (π k)))) u) := by
  intro u
  have hconj : M * u * M⁻¹ = InnerDiagA.conjSL (InnerDiagA.diagGL ev) u :=
    mul_conj_eq_conjSL_of_matrix_diagonal (m := r + 1) hM hdet u
  have hframe := hF.2.2.2 ⟨σ M, hB⟩ u
  have h3 : σ (M * u * M⁻¹) =
      (↑(⟨σ M, hB⟩ : ↥Bs) : G) * σ u * (↑(⟨σ M, hB⟩ : ↥Bs) : G)⁻¹ := by
    simp only [map_mul, map_inv]
  have h1 := congrArg σ hconj
  rw [h3] at h1
  rw [hframe] at h1
  exact h1.symm

private theorem b3_lframe_diagSL_coord_eq_of_frame {r f : ℕ}
    {G : Type} [Group G] {Bs L : Subgroup G} {n p : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {σ : SL(r + 2, GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpLFrame Bs L eta π σ χ)
    {ev : Fin (r + 2) → (GaloisField 2 f)ˣ} {M : SL(r + 2, GaloisField 2 f)}
    (hM : (M : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f)) =
      Matrix.diagonal (fun i => (ev i : GaloisField 2 f)))
    (hdet : Matrix.GeneralLinearGroup.det (InnerDiagA.diagGL ev) = 1)
    (hB : σ M ∈ Bs) {i j : Fin (r + 2)} (hvi : ev i = 1) (hvj : ev j = 1) :
    eta ⟨σ M, hB⟩ (π i) = eta ⟨σ M, hB⟩ (π j) := by
  have hD := b3_lframe_conjSL_diag_eq_of_frame hF hM hdet hB
  have h := diagGL_mul_inv_eq_of_conjSL_map_eq (m := r + 1) σ hF.1 hD i j
  rw [hvi, hvj] at h
  simp only [inv_one, mul_one] at h
  exact hF.2.2.1 (mul_inv_eq_one.mp h.symm)

private theorem b3_lframe_diagSL_notMem_centralizer {r p f : ℕ} [Fact p.Prime]
    {G : Type} [Group G] {Bs L : Subgroup G} {n : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {σ : SL(r + 2, GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hζ : ((χ (Multiplicative.ofAdd 1) : (GaloisField 2 f)ˣ) : GaloisField 2 f) ^ 2 ≠ 1)
    (hF : GGSecFiveBPermSpLFrame Bs L eta π σ χ)
    {ev : Fin (r + 2) → (GaloisField 2 f)ˣ} {M : SL(r + 2, GaloisField 2 f)}
    (hM : (M : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f)) =
      Matrix.diagonal (fun i => (ev i : GaloisField 2 f)))
    (hdet : Matrix.GeneralLinearGroup.det (InnerDiagA.diagGL ev) = 1)
    {i j : Fin (r + 2)} (hvi : ev i = χ (Multiplicative.ofAdd 1))
    (hvj : ev j = (χ (Multiplicative.ofAdd 1))⁻¹) :
    σ M ∉ Subgroup.centralizer (L : Set G) := by
  intro hcent
  have hcomm : ∀ u : SL(r + 2, GaloisField 2 f), σ u * σ M = σ M * σ u := by
    intro u
    exact Subgroup.mem_centralizer_iff.mp hcent (σ u) (by rw [← hF.2.1]; exact ⟨u, rfl⟩)
  have hMu : ∀ u : SL(r + 2, GaloisField 2 f), σ M * σ u * (σ M)⁻¹ = σ u := by
    intro u
    rw [← hcomm u]
    group
  have hD1 : ∀ u : SL(r + 2, GaloisField 2 f),
      σ (InnerDiagA.conjSL (InnerDiagA.diagGL ev) u) =
        σ (InnerDiagA.conjSL (InnerDiagA.diagGL (fun _ => 1)) u) := by
    intro u
    have hconj : M * u * M⁻¹ = InnerDiagA.conjSL (InnerDiagA.diagGL ev) u :=
      mul_conj_eq_conjSL_of_matrix_diagonal (m := r + 1) hM hdet u
    calc σ (InnerDiagA.conjSL (InnerDiagA.diagGL ev) u)
        = σ (M * u * M⁻¹) := by rw [hconj]
      _ = σ M * σ u * (σ M)⁻¹ := by simp only [map_mul, map_inv]
      _ = σ u := hMu u
      _ = σ (InnerDiagA.conjSL (InnerDiagA.diagGL (fun _ => 1)) u) := by
          rw [show (fun _ => (1 : (GaloisField 2 f)ˣ)) =
            (1 : Fin (r + 2) → (GaloisField 2 f)ˣ) from rfl,
            LinFusion.diagGL_one, LinFusion.conjSL_one]
  have h := diagGL_mul_inv_eq_of_conjSL_map_eq (m := r + 1) σ hF.1 hD1 i j
  rw [hvi, hvj] at h
  simp only [inv_one, mul_one, inv_inv] at h
  have hζ2u : (χ (Multiplicative.ofAdd 1)) ^ 2 = 1 := by
    rw [pow_two]
    exact h
  have hζ2 : ((χ (Multiplicative.ofAdd 1) : (GaloisField 2 f)ˣ) : GaloisField 2 f) ^ 2 = 1 := by
    rw [← Units.val_pow_eq_pow_val, hζ2u, Units.val_one]
  exact hζ hζ2

private theorem b3_lframe_exists_pair_outside {r : ℕ} (hr : 2 ≤ r) (a : Fin (r + 1)) :
    ∃ c e : Fin (r + 2), c ≠ e ∧ a.castSucc ≠ c ∧ a.castSucc ≠ e ∧
      a.succ ≠ c ∧ a.succ ≠ e := by
  have hN : 4 ≤ r + 2 := by omega
  have hcast : a.castSucc ≠ a.succ := by
    intro h
    have hv := congrArg Fin.val h
    simp [Fin.castSucc, Fin.succ] at hv
  obtain ⟨c, e, hce, hc, he⟩ := exists_two_notMem_pair hN a.castSucc a.succ hcast
  exact ⟨c, e, hce,
    fun h => hc (by rw [h]; exact Finset.mem_insert_self _ _),
    fun h => he (by rw [h]; exact Finset.mem_insert_self _ _),
    fun h => hc (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _)),
    fun h => he (by rw [h]; exact Finset.mem_insert_of_mem (Finset.mem_singleton_self _))⟩

private theorem b3_lframe_exists_pair_diagSL {r p f : ℕ} [Fact p.Prime]
    {G : Type} [Group G] {Bs L : Subgroup G} {n : ℕ}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {σ : SL(r + 2, GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hr : 2 ≤ r) (hF : GGSecFiveBPermSpLFrame Bs L eta π σ χ)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (a : Fin (r + 1)) :
    ∃ (ev : Fin (r + 2) → (GaloisField 2 f)ˣ)
      (M' : SL(r + 2, GaloisField 2 f)) (c e : Fin (r + 2)),
      c ≠ e ∧ ev c = χ (Multiplicative.ofAdd 1) ∧
        ev e = (χ (Multiplicative.ofAdd 1))⁻¹ ∧ ev a.castSucc = 1 ∧ ev a.succ = 1 ∧
        (M' : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f)) =
          Matrix.diagonal (fun i => (ev i : GaloisField 2 f)) ∧
        Matrix.GeneralLinearGroup.det (InnerDiagA.diagGL ev) = 1 ∧
        σ M' ∈ Bs := by
  classical
  obtain ⟨c, e, hce, hac, hae, hsc, hse⟩ := b3_lframe_exists_pair_outside hr a
  let ζ : (GaloisField 2 f)ˣ := χ (Multiplicative.ofAdd 1)
  let ev : Fin (r + 2) → (GaloisField 2 f)ˣ := fun i =>
    if i = c then ζ else if i = e then ζ⁻¹ else 1
  have hfun : (fun i => (ev i : GaloisField 2 f)) =
      (fun i => if i = c then (ζ : GaloisField 2 f) else
        if i = e then (((ζ⁻¹ : (GaloisField 2 f)ˣ) : GaloisField 2 f)) else 1) := by
    funext i
    by_cases hic : i = c
    · simp [ev, hic]
    · by_cases hie : i = e
      · simp [ev, hie, hce.symm]
      · simp [ev, hic, hie]
  have hprod : ∏ i, (ev i : GaloisField 2 f) = 1 := by
    rw [hfun]
    exact prod_pair_diag hce ζ
  let M' : SL(r + 2, GaloisField 2 f) :=
    ⟨Matrix.diagonal (fun i => (ev i : GaloisField 2 f)), by
      rw [Matrix.det_diagonal]
      exact hprod⟩
  have hM' : (M' : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f)) =
      Matrix.diagonal (fun i => (ev i : GaloisField 2 f)) := rfl
  have hdet : Matrix.GeneralLinearGroup.det (InnerDiagA.diagGL ev) = 1 := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, InnerDiagA.coe_diagGL,
      Matrix.det_diagonal, Units.val_one]
    exact hprod
  have hζp : ζ ^ p = 1 := b3_lframe_chi_ofAdd_one_pow χ
  have hevp : ∀ i, (ev i : GaloisField 2 f) ^ p = 1 := by
    intro i
    by_cases hic : i = c
    · rw [hic]
      rw [show ev c = ζ from by simp [ev], ← Units.val_pow_eq_pow_val, hζp, Units.val_one]
    · by_cases hie : i = e
      · rw [hie]
        rw [show ev e = ζ⁻¹ from by simp [ev, hce.symm], ← Units.val_pow_eq_pow_val,
          inv_pow, hζp, inv_one, Units.val_one]
      · rw [show ev i = 1 from by simp [ev, hic, hie], Units.val_one, one_pow]
  have hrB : σ M' ∈ Bs := b3_lframe_mem_Bs_of_diagSL hF hBs hM' hevp
  exact ⟨ev, M', c, e, hce, by simp [ev, ζ], by simp [ev, ζ, hce.symm],
    by simp [ev, hac, hae], by simp [ev, hsc, hse], hM', hdet, hrB⟩

private theorem lframe_centralizer_le_normalizer [Finite G] {p n r f : ℕ} [Fact p.Prime]
    (hp2 : p ≠ 2) (hr : 2 ≤ r) {Bs L : Subgroup G} {x : G}
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hxB : x ∈ Bs) (hL : IsComponentOf L (Subgroup.centralizer {x}))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {σ : SL(r + 2, GaloisField 2 f) →* G} {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpLFrame Bs L eta π σ χ) (a : Fin (r + 1)) :
    Subgroup.centralizer (ggBsCoordEq Bs eta (π a.castSucc) (π a.succ) : Set G) ≤
      Subgroup.normalizer (L : Set G) := by
  classical
  obtain ⟨ev, M', c, e, hce, hvc, hve, hva, hvs, hM', hdet, hrB⟩ :=
    b3_lframe_exists_pair_diagSL hr hF hBs a
  have hcoord : eta ⟨σ M', hrB⟩ (π a.castSucc) = eta ⟨σ M', hrB⟩ (π a.succ) :=
    b3_lframe_diagSL_coord_eq_of_frame hF hM' hdet hrB hva hvs
  have hrH : σ M' ∈ ggBsCoordEq Bs eta (π a.castSucc) (π a.succ) :=
    mem_ggBsCoordEq.mpr ⟨hrB, hcoord⟩
  have hrL : σ M' ∈ L := by
    rw [← hF.2.1]
    exact ⟨M', rfl⟩
  have hrC : σ M' ∉ Subgroup.centralizer (L : Set G) :=
    b3_lframe_diagSL_notMem_centralizer (lframe_zeta_sq_ne_one hp2 hF.2.2.1) hF hM' hdet hvc hve
  intro g hg
  have hxH : x ∈ ggBsCoordEq Bs eta (π a.castSucc) (π a.succ) :=
    lframe_x_mem hxB hL.1 hF a.castSucc a.succ
  have hgx : g * x = x * g := ((Subgroup.mem_centralizer_iff.mp hg) x hxH).symm
  have hgr : g * σ M' = σ M' * g := ((Subgroup.mem_centralizer_iff.mp hg) (σ M') hrH).symm
  have hgC : g ∈ Subgroup.centralizer ({x} : Set G) :=
    Subgroup.mem_centralizer_singleton_iff.mpr hgx
  have hgN : g ∈ Subgroup.normalizer (Subgroup.centralizer ({x} : Set G) : Set G) :=
    Subgroup.le_normalizer hgC
  exact ggMem_normalizer_of_component hL hrL hrC hgN hgr

private theorem b4_zeta_facts {F : Type} [Field F] {ζ : Fˣ} (h : (ζ : F) ^ 2 ≠ 1) :
    ((ζ : F) ≠ 1) ∧ (((ζ⁻¹ : Fˣ) : F) ≠ (ζ : F)) := by
  refine ⟨fun h1 => h (by rw [h1, one_pow]), fun h1 => h ?_⟩
  rw [Units.val_inv_eq_inv_val] at h1
  have h2 : (1 : F) = (ζ : F) * (ζ : F) := by
    calc (1 : F) = (ζ : F)⁻¹ * (ζ : F) := (inv_mul_cancel₀ (Units.ne_zero ζ)).symm
      _ = (ζ : F) * (ζ : F) := by rw [h1]
  rw [pow_two]
  exact h2.symm

private theorem b4_exists_coord {p n r f : ℕ}
    {Bs : Subgroup G} {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))}
    {π : Fin (r + 2) ≃ Fin n} {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (a : Fin (r + 1)) {c : Fin (r + 2)}
    (hc : c ∉ ({a.castSucc, a.succ} : Finset (Fin (r + 2)))) :
    ∃ h : ↥Bs, (h : G) ∈ ggBsCoordEq Bs eta (π a.castSucc) (π a.succ) ∧
      ∀ m, χ (eta h (π m)) = if m = c then χ (Multiplicative.ofAdd 1) else 1 := by
  classical
  let h : ↥Bs := eta.symm (Pi.mulSingle (π c) (Multiplicative.ofAdd 1))
  have hh : eta h = Pi.mulSingle (π c) (Multiplicative.ofAdd 1) := by
    simp only [h, MulEquiv.apply_symm_apply]
  have hne1 : π a.castSucc ≠ π c := fun heq => hc (by
    have h' : a.castSucc = c := π.injective heq
    rw [← h']; simp)
  have hne2 : π a.succ ≠ π c := fun heq => hc (by
    have h' : a.succ = c := π.injective heq
    rw [← h']; simp)
  refine ⟨h, ?_, ?_⟩
  · rw [coe_mem_ggBsCoordEq, hh, Pi.mulSingle_eq_of_ne hne1, Pi.mulSingle_eq_of_ne hne2]
  · intro m
    by_cases hm : m = c
    · subst hm
      rw [hh, Pi.mulSingle_eq_same, if_pos rfl]
    · rw [hh, Pi.mulSingle_eq_of_ne (fun heq => hm (π.injective heq)), map_one, if_neg hm]

private theorem b4_diag_mul_eq_smul {p n r f : ℕ}
    {Bs L : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {σ : SL(r + 2, GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpLFrame Bs L eta π σ χ) {a : Fin (r + 1)}
    {u : SL(r + 2, GaloisField 2 f)}
    (hu : σ u ∈ Subgroup.centralizer
      (ggBsCoordEq Bs eta (π a.castSucc) (π a.succ) : Set G))
    {c : Fin (r + 2)} (hc : c ∉ ({a.castSucc, a.succ} : Finset (Fin (r + 2)))) :
    ∃ z : GaloisField 2 f,
      Matrix.diagonal (fun i => if i = c then
          (χ (Multiplicative.ofAdd 1) : GaloisField 2 f) else 1) *
        (u : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f)) *
        (Matrix.diagonal (fun i => if i = c then
          (χ (Multiplicative.ofAdd 1) : GaloisField 2 f) else 1))⁻¹ =
      z • (u : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f)) := by
  classical
  obtain ⟨h, hhH, hhχ⟩ := b4_exists_coord (Bs := Bs) (eta := eta) (π := π) (χ := χ) a hc
  have hcent : (h : G) * σ u = σ u * (h : G) :=
    Subgroup.mem_centralizer_iff.mp hu (h : G) hhH
  have hfix : (h : G) * σ u * (h : G)⁻¹ = σ u := by rw [hcent]; group
  have hconj : σ (InnerDiagA.conjSL
      (InnerDiagA.diagGL (fun m => χ (eta h (π m)))) u) = σ u :=
    (hF.2.2.2 h u).symm.trans hfix
  have hker : InnerDiagA.conjSL (InnerDiagA.diagGL (fun m => χ (eta h (π m)))) u *
      u⁻¹ ∈ σ.ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, hconj, mul_inv_cancel]
  obtain ⟨z, -, hru⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp (hF.1 hker)
  set D : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f) :=
    Matrix.diagonal (fun i => if i = c then
      (χ (Multiplicative.ofAdd 1) : GaloisField 2 f) else 1) with hD
  set M : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f) :=
    (u : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f)) with hM
  have hAd : ((InnerDiagA.diagGL (fun m => χ (eta h (π m))) :
      GL (Fin (r + 2)) (GaloisField 2 f)) :
      Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f)) = D := by
    rw [hD, InnerDiagA.coe_diagGL]
    congr 1
    funext i
    rw [hhχ i]
    by_cases hi : i = c <;> simp [hi]
  have hMdet : M.det ≠ 0 := by rw [hM, u.2]; exact one_ne_zero
  have hu_inv : ((u⁻¹ : SL(r + 2, GaloisField 2 f)) :
      Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f)) = M⁻¹ := by
    rw [hM, Matrix.SpecialLinearGroup.coe_inv, Matrix.inv_def, u.2, Ring.inverse_one, one_smul]
  have hsc : (Matrix.scalar (Fin (r + 2)) z : Matrix (Fin (r + 2)) (Fin (r + 2))
      (GaloisField 2 f)) = D * M * D⁻¹ * M⁻¹ := by
    rw [hru, Matrix.SpecialLinearGroup.coe_mul, InnerDiagA.coe_conjSL,
      Matrix.GeneralLinearGroup.coe_inv, hu_inv, hAd, ← hM]
  refine ⟨z, ?_⟩
  have hstep : (Matrix.scalar (Fin (r + 2)) z : Matrix (Fin (r + 2)) (Fin (r + 2))
      (GaloisField 2 f)) * M = D * M * D⁻¹ := by
    rw [hsc, Matrix.mul_assoc (D * M * D⁻¹) M⁻¹ M,
      Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hMdet), Matrix.mul_one]
  have hscalar : (Matrix.scalar (Fin (r + 2)) z : Matrix (Fin (r + 2)) (Fin (r + 2))
      (GaloisField 2 f)) * M = z • M := by
    rw [Matrix.scalar_apply]
    ext i j
    rw [Matrix.diagonal_mul, Matrix.smul_apply, smul_eq_mul]
  rw [← hstep, hscalar]

private theorem b4_diag_comm {p n r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs L : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {σ : SL(r + 2, GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpLFrame Bs L eta π σ χ) {a : Fin (r + 1)}
    {u : SL(r + 2, GaloisField 2 f)}
    (hu : σ u ∈ Subgroup.centralizer
      (ggBsCoordEq Bs eta (π a.castSucc) (π a.succ) : Set G))
    {c : Fin (r + 2)} (hc : c ∉ ({a.castSucc, a.succ} : Finset (Fin (r + 2)))) :
    Matrix.diagonal (fun i => if i = c then
        (χ (Multiplicative.ofAdd 1) : GaloisField 2 f) else 1) *
      (u : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f)) =
      (u : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f)) *
        Matrix.diagonal (fun i => if i = c then
          (χ (Multiplicative.ofAdd 1) : GaloisField 2 f) else 1) := by
  classical
  obtain ⟨z, hsmul⟩ := b4_diag_mul_eq_smul hF hu hc
  obtain ⟨hζ1, hζinv⟩ := b4_zeta_facts (lframe_zeta_sq_ne_one hp2 hF.2.2.1)
  set D : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f) :=
    Matrix.diagonal (fun i => if i = c then
      (χ (Multiplicative.ofAdd 1) : GaloisField 2 f) else 1) with hD
  set M : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f) :=
    (u : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f)) with hM
  have hMdet : M.det ≠ 0 := by rw [hM, u.2]; exact one_ne_zero
  have hz : z = 1 := two_eigenvalue (N := r + 2) (by omega) hζ1 hζinv hMdet hsmul
  rw [hz, one_smul] at hsmul
  have hDdet : D.det ≠ 0 := by
    rw [hD, Matrix.det_diagonal]
    refine Finset.prod_ne_zero_iff.mpr (fun i _ => ?_)
    by_cases hi : i = c
    · simp [hi, Units.ne_zero (χ (Multiplicative.ofAdd 1))]
    · simp [hi]
  have hDmul : (D * M * D⁻¹) * D = D * M := by
    rw [Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_iff_ne_zero.mpr hDdet),
      Matrix.mul_one]
  rw [← hDmul, hsmul]

private theorem b4_row_col_zero {F : Type} [Field F] {N : ℕ} {c : Fin N} {ζ : Fˣ}
    (hζ : (ζ : F) ≠ 1) {u : Matrix (Fin N) (Fin N) F}
    (hcomm : Matrix.diagonal (fun i => if i = c then (ζ : F) else 1) * u =
      u * Matrix.diagonal (fun i => if i = c then (ζ : F) else 1)) :
    (∀ j, j ≠ c → u c j = 0) ∧ (∀ j, j ≠ c → u j c = 0) := by
  constructor
  · intro j hj
    have h1 := congrFun (congrFun hcomm c) j
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
    simp only [if_neg hj, if_true, mul_one] at h1
    have h2 : ((ζ : F) - 1) * u c j = 0 := by rw [sub_mul, one_mul, h1, sub_self]
    exact (mul_eq_zero.mp h2).resolve_left (sub_ne_zero.mpr hζ)
  · intro j hj
    have h1 := congrFun (congrFun hcomm j) c
    rw [Matrix.diagonal_mul, Matrix.mul_diagonal] at h1
    simp only [if_neg hj, if_true, one_mul] at h1
    have h2 : u j c * ((ζ : F) - 1) = 0 := by rw [mul_sub, mul_one, ← h1, sub_self]
    exact (mul_eq_zero.mp h2).resolve_right (sub_ne_zero.mpr hζ)

private theorem b4_entries_zero {p n r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs L : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {σ : SL(r + 2, GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpLFrame Bs L eta π σ χ) (a : Fin (r + 1))
    {u : SL(r + 2, GaloisField 2 f)}
    (hu : σ u ∈ Subgroup.centralizer
      (ggBsCoordEq Bs eta (π a.castSucc) (π a.succ) : Set G)) :
    ∀ i j, i ≠ j → (i ∉ ({a.castSucc, a.succ} : Finset (Fin (r + 2))) ∨
      j ∉ ({a.castSucc, a.succ} : Finset (Fin (r + 2)))) →
      (u : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f)) i j = 0 := by
  intro i j hij hIJ
  obtain ⟨hζ1, -⟩ := b4_zeta_facts (lframe_zeta_sq_ne_one hp2 hF.2.2.1)
  rcases hIJ with hi | hj
  · exact (b4_row_col_zero hζ1 (b4_diag_comm hp2 hF hu hi)).1 j hij.symm
  · exact (b4_row_col_zero hζ1 (b4_diag_comm hp2 hF hu hj)).2 i hij

private theorem b4_block_and_offdiag {p n r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs L : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {σ : SL(r + 2, GaloisField 2 f) →* G}
    {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpLFrame Bs L eta π σ χ) (a : Fin (r + 1))
    {u : SL(r + 2, GaloisField 2 f)}
    (hu : σ u ∈ Subgroup.centralizer
      (ggBsCoordEq Bs eta (π a.castSucc) (π a.succ) : Set G)) :
    u ∈ CFSG.SeitzReduction.LinearPilot.blockDiagSL
        ({a.castSucc, a.succ} : Finset (Fin (r + 2))) ∧
      (∀ i j, i ∉ ({a.castSucc, a.succ} : Finset (Fin (r + 2))) →
        j ∉ ({a.castSucc, a.succ} : Finset (Fin (r + 2))) → i ≠ j →
        (u : Matrix (Fin (r + 2)) (Fin (r + 2)) (GaloisField 2 f)) i j = 0) := by
  constructor
  · rw [CFSG.SeitzReduction.LinearPilot.mem_blockDiagSL]
    intro i j hij
    have hne : i ≠ j := by
      intro h
      subst h
      by_cases hi : i ∈ ({a.castSucc, a.succ} : Finset (Fin (r + 2)))
      · exact (hij.mp hi) hi
      · exact hi (hij.mpr hi)
    exact b4_entries_zero hp2 hF a hu i j hne (by
      by_cases hi : i ∈ ({a.castSucc, a.succ} : Finset (Fin (r + 2)))
      · exact Or.inr (hij.mp hi)
      · exact Or.inl hi)
  · intro i j hi hj hij
    exact b4_entries_zero hp2 hF a hu i j hij (Or.inl hi)

private theorem lframe_commutator_le_range {p n r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    {Bs L : Subgroup G}
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {σ : SL(r + 2, GaloisField 2 f) →* G} {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpLFrame Bs L eta π σ χ) (a : Fin (r + 1)) :
    ⁅L ⊓ Subgroup.centralizer (ggBsCoordEq Bs eta (π a.castSucc) (π a.succ) : Set G),
      L ⊓ Subgroup.centralizer (ggBsCoordEq Bs eta (π a.castSucc) (π a.succ) : Set G)⁆ ≤
      (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) a)).range := by
  classical
  rw [Subgroup.commutator_le]
  intro g1 hg1 g2 hg2
  obtain ⟨u1, hu1⟩ : ∃ u1 : SL(r + 2, GaloisField 2 f), σ u1 = g1 := by
    have hmem : g1 ∈ σ.range := by rw [hF.2.1]; exact hg1.1
    exact hmem
  obtain ⟨u2, hu2⟩ : ∃ u2 : SL(r + 2, GaloisField 2 f), σ u2 = g2 := by
    have hmem : g2 ∈ σ.range := by rw [hF.2.1]; exact hg2.1
    exact hmem
  obtain ⟨hb1, ho1⟩ := b4_block_and_offdiag hp2 hF a (u := u1) (by rw [hu1]; exact hg1.2)
  obtain ⟨hb2, ho2⟩ := b4_block_and_offdiag hp2 hF a (u := u2) (by rw [hu2]; exact hg2.2)
  have hmem := commutator_mem_blockSpecialLinear hb1 hb2 ho1 ho2
  rw [blockSpecialLinear_pair_eq_range_blockSL2 (F := GaloisField 2 f) (m := r + 1) a] at hmem
  obtain ⟨B, hB⟩ := hmem
  refine ⟨B, ?_⟩
  rw [MonoidHom.comp_apply, hB, ← commutatorElement_def, map_commutatorElement, hu1, hu2]

theorem ggSecFiveBPermSp_reflComm_L [Finite G] {p n r f : ℕ} [Fact p.Prime] (hp2 : p ≠ 2)
    (hr : 2 ≤ r) {Bs L : Subgroup G} {x : G}
    (hBc : ∀ a ∈ Bs, ∀ b ∈ Bs, a * b = b * a)
    (hBs : ∀ g ∈ Subgroup.centralizer (Bs : Set G), g ^ p = 1 → g ∈ Bs)
    (hxB : x ∈ Bs) (hL : IsComponentOf L (Subgroup.centralizer {x}))
    {eta : ↥Bs ≃* (Fin n → Multiplicative (ZMod p))} {π : Fin (r + 2) ≃ Fin n}
    {σ : SL(r + 2, GaloisField 2 f) →* G} {χ : Multiplicative (ZMod p) →* (GaloisField 2 f)ˣ}
    (hF : GGSecFiveBPermSpLFrame Bs L eta π σ χ) (a : Fin (r + 1)) :
    ⁅Subgroup.centralizer (ggBsCoordEq Bs eta (π a.castSucc) (π a.succ) : Set G), Bs⁆ =
      (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) a)).range := by
  set R := (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) a)).range with hRdef
  have hζ2 := lframe_zeta_sq_ne_one hp2 hF.2.2.1
  have htB := lframe_torus_mem hBs hF a
  have hRC := lframe_range_le_centralizer hF a
  have hRt := ggRange_le_commutator_zpowers_torusHom
    (σ.comp (blockSL2 (GaloisField 2 f) (r + 1) a)) hζ2
  have hRL : R ≤ L := by
    rintro _ ⟨A, rfl⟩
    rw [← hF.2.1]
    exact ⟨_, rfl⟩
  have htR : σ (blockSL2 (GaloisField 2 f) (r + 1) a (CFSG.ClassicalInvolution.WeakCT.torusHom
      (GaloisField 2 f) (χ (Multiplicative.ofAdd 1)))) ∈ R := ⟨_, rfl⟩
  refine ggCommutator_centralizer_eq hBc (ggBsCoordEq_le _ _) htB (lframe_gen hp2 hF a htB)
    (lframe_centralizer_le_normalizer hp2 hr hBs hxB hL hF a) ?_
    (lframe_commutator_le_range hp2 hF a) hRC hRt
  have hRD := le_inf hRL hRC
  exact Subgroup.commutator_mono hRD hRD
    (Subgroup.commutator_mono le_rfl (Subgroup.zpowers_le.mpr htR) (hRt htR))

end CFSG.StandardType

end
