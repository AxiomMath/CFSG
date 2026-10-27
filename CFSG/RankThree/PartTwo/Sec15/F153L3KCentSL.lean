module

public import CFSG.RankThree.PartTwo.Sec3.Sims321Transv
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.LocalAnalysis.AGLEmbeddingD2.Ambient
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec15.F153L3K

section Cube
open scoped MatrixGroups Matrix
open Matrix
open CFSG.LargeExtraspecial

theorem cayley_hamilton_fin_three {R : Type*} [CommRing R] (M : Matrix (Fin 3) (Fin 3) R) :
    M ^ 3 - Matrix.trace M • M ^ 2 + Matrix.trace (Matrix.adjugate M) • M
      - M.det • (1 : Matrix (Fin 3) (Fin 3) R) = 0 := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_succ, Matrix.mul_apply, Fin.sum_univ_three, Matrix.trace_fin_three,
      Matrix.det_fin_three, Matrix.adjugate_fin_three, Matrix.one_apply] <;> ring

theorem smul_sub_eq_zero_of_cayley {F : Type} [Field F] (M : Matrix (Fin 3) (Fin 3) F)
    (hCH : 1 - Matrix.trace M • M ^ 2 + Matrix.trace M • M - 1 = 0) :
    Matrix.trace M = 0 ∨ M ^ 2 - M = 0 := by
  have key : Matrix.trace M • (M ^ 2 - M) = 0 := by
    rw [smul_sub]
    have h0 : Matrix.trace M • M ^ 2 - Matrix.trace M • M =
        -(1 - Matrix.trace M • M ^ 2 + Matrix.trace M • M - 1) := by
      abel
    rw [h0, hCH, neg_zero]
  exact smul_eq_zero.mp key

theorem trace_eq_zero_of_cube_eq_one {F : Type} [Field F]
    (Y : Matrix.SpecialLinearGroup (Fin 3) F) (hY3 : Y ^ 3 = 1) (hY1 : Y ≠ 1)
    (hinv : Matrix.trace ((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      Matrix.trace ((Y : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) :
    Matrix.trace ((Y : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) = 0 := by
  have hCH := cayley_hamilton_fin_three
    ((Y : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)
  have hM3 : ((Y : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) ^ 3 = 1 := by
    rw [← Matrix.SpecialLinearGroup.coe_pow, hY3, Matrix.SpecialLinearGroup.coe_one]
  have hdet : Matrix.det ((Y : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
      1 :=
    Matrix.SpecialLinearGroup.det_coe Y
  have hadj : Matrix.adjugate ((Y : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) =
      ((Y⁻¹ : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) :=
    (Matrix.SpecialLinearGroup.coe_inv Y).symm
  rw [hM3, hdet, hadj, hinv, one_smul] at hCH
  rcases smul_sub_eq_zero_of_cayley _ hCH with hs | hMM
  · exact hs
  · have hMM' : ((Y : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) *
        ((Y : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        ((Y : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
      rw [← pow_two]
      exact sub_eq_zero.mp hMM
    have hYY : Y * Y = Y * 1 := by
      apply Subtype.ext
      simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, mul_one]
      exact hMM'
    exact absurd (mul_left_cancel hYY) hY1

theorem tv_mul_self_of_char_two {F : Type} [Field F] [CharP F 2] {u φ : Fin 3 → F}
    (h : φ ⬝ᵥ u = 0) : A2Mod.tv u φ * A2Mod.tv u φ = 1 := by
  have h2 : φ + φ = 0 := by
    funext i
    exact CharTwo.add_self_eq_zero (φ i)
  rw [A2Mod.tv_mul_tv_left h h, h2, A2Mod.tv_zero_right]

theorem add_self_zero_matrix {F : Type} [Field F] [CharP F 2] (M : Matrix (Fin 3) (Fin 3) F) :
    M + M = 0 := by
  ext i j
  exact CharTwo.add_self_eq_zero (M i j)

theorem vmv_AA {F : Type} [Field F] {v ψ : Fin 3 → F} (hψv : ψ ⬝ᵥ v = 0) :
    vecMulVec v ψ * vecMulVec v ψ = 0 := by
  rw [vecMulVec_mul_vecMulVec, hψv, zero_smul, vecMulVec_zero]

theorem vmv_BB {F : Type} [Field F] {u φ : Fin 3 → F} (hφu : φ ⬝ᵥ u = 0) :
    vecMulVec u φ * vecMulVec u φ = 0 := by
  rw [vecMulVec_mul_vecMulVec, hφu, zero_smul, vecMulVec_zero]

theorem vmv_ABA {F : Type} [Field F] {u v φ ψ : Fin 3 → F}
    (hab : (ψ ⬝ᵥ u) * (φ ⬝ᵥ v) = 1) :
    vecMulVec v ψ * vecMulVec u φ * vecMulVec v ψ = vecMulVec v ψ := by
  simp only [vecMulVec_mul_vecMulVec, vecMulVec_smul, Matrix.smul_mul, smul_smul, hab, one_smul]

theorem vmv_BAB {F : Type} [Field F] {u v φ ψ : Fin 3 → F}
    (hab' : (φ ⬝ᵥ v) * (ψ ⬝ᵥ u) = 1) :
    vecMulVec u φ * vecMulVec v ψ * vecMulVec u φ = vecMulVec u φ := by
  simp only [vecMulVec_mul_vecMulVec, vecMulVec_smul, Matrix.smul_mul, smul_smul, hab', one_smul]

theorem braid_matrix {F : Type} [Field F] [CharP F 2] {u φ v ψ : Fin 3 → F}
    (hψv : ψ ⬝ᵥ v = 0) (hφu : φ ⬝ᵥ u = 0) (hab : (ψ ⬝ᵥ u) * (φ ⬝ᵥ v) = 1) :
    (1 + vecMulVec v ψ) * (1 + vecMulVec u φ) * (1 + vecMulVec v ψ) =
      (1 + vecMulVec u φ) * (1 + vecMulVec v ψ) * (1 + vecMulVec u φ) := by
  have hab' : (φ ⬝ᵥ v) * (ψ ⬝ᵥ u) = 1 := by
    rw [mul_comm]
    exact hab
  simp only [add_mul, mul_add, one_mul, mul_one]
  linear_combination (norm := module) add_self_zero_matrix (vecMulVec v ψ)
    - add_self_zero_matrix (vecMulVec u φ) + vmv_AA hψv - vmv_BB hφu
    + vmv_ABA hab - vmv_BAB hab'

theorem cube_of_braid {G : Type*} [Group G] {τ ξ : G} (hτ : τ * τ = 1) (hξ : ξ * ξ = 1)
    (hb : τ * ξ * τ = ξ * τ * ξ) : (τ * ξ) ^ 3 = 1 := by
  have hτi : τ⁻¹ = τ := inv_eq_of_mul_eq_one_right hτ
  have hξi : ξ⁻¹ = ξ := inv_eq_of_mul_eq_one_right hξ
  have h1 : (τ * ξ) ^ 3 = (τ * ξ * τ) * (ξ * τ * ξ) := by
    simp only [pow_succ, pow_zero, one_mul, mul_assoc]
  have h2 : (ξ * τ * ξ) * (ξ * τ * ξ) = 1 := by
    rw [mul_eq_one_iff_eq_inv, _root_.mul_inv_rev, _root_.mul_inv_rev, hξi, hτi, mul_assoc]
  rw [h1, hb, h2]

theorem braid_tv {F : Type} [Field F] [CharP F 2] {u φ v ψ : Fin 3 → F}
    (hφu : φ ⬝ᵥ u = 0) (hψv : ψ ⬝ᵥ v = 0) (hab : (ψ ⬝ᵥ u) * (φ ⬝ᵥ v) = 1) :
    A2Mod.tv v ψ * A2Mod.tv u φ * A2Mod.tv v ψ =
      A2Mod.tv u φ * A2Mod.tv v ψ * A2Mod.tv u φ := by
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul, A2Mod.coe_tv hψv, A2Mod.coe_tv hφu]
  exact braid_matrix hψv hφu hab

theorem trace_tv_mul_tv {F : Type} [Field F] {u φ v ψ : Fin 3 → F}
    (hψv : ψ ⬝ᵥ v = 0) (hφu : φ ⬝ᵥ u = 0) :
    Matrix.trace ((A2Mod.tv v ψ * A2Mod.tv u φ : Matrix.SpecialLinearGroup (Fin 3) F) :
        Matrix (Fin 3) (Fin 3) F) =
      3 + (ψ ⬝ᵥ v) + (φ ⬝ᵥ u) + (ψ ⬝ᵥ u) * (φ ⬝ᵥ v) := by
  rw [Matrix.SpecialLinearGroup.coe_mul, A2Mod.coe_tv hψv, A2Mod.coe_tv hφu]
  simp [Matrix.trace_fin_three, Matrix.mul_apply, Fin.sum_univ_three, dotProduct,
    Matrix.vecMulVec_apply, Matrix.one_apply]
  ring

theorem cube_iff_of_tv {F : Type} [Field F] [CharP F 2] {u φ v ψ : Fin 3 → F}
    (hφu : φ ⬝ᵥ u = 0) (hψv : ψ ⬝ᵥ v = 0) :
    ((A2Mod.tv v ψ * A2Mod.tv u φ) ^ 3 = 1 ∧ A2Mod.tv u φ ≠ A2Mod.tv v ψ) ↔
      (ψ ⬝ᵥ u) * (φ ⬝ᵥ v) = 1 := by
  have hτ : A2Mod.tv v ψ * A2Mod.tv v ψ = 1 := tv_mul_self_of_char_two hψv
  have hξ : A2Mod.tv u φ * A2Mod.tv u φ = 1 := tv_mul_self_of_char_two hφu
  constructor
  · rintro ⟨h3, hne⟩
    have hτi : (A2Mod.tv v ψ)⁻¹ = A2Mod.tv v ψ := inv_eq_of_mul_eq_one_right hτ
    have hY1 : A2Mod.tv v ψ * A2Mod.tv u φ ≠ 1 := by
      intro h
      apply hne
      exact (eq_inv_of_mul_eq_one_right h).trans hτi
    have hYinv : (A2Mod.tv v ψ * A2Mod.tv u φ)⁻¹ = A2Mod.tv u φ * A2Mod.tv v ψ := by
      apply inv_eq_of_mul_eq_one_right
      rw [mul_assoc, ← mul_assoc (A2Mod.tv u φ) (A2Mod.tv u φ), hξ, one_mul, hτ]
    have hinv : Matrix.trace (((A2Mod.tv v ψ * A2Mod.tv u φ)⁻¹ :
          Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
        Matrix.trace ((A2Mod.tv v ψ * A2Mod.tv u φ : Matrix.SpecialLinearGroup (Fin 3) F) :
          Matrix (Fin 3) (Fin 3) F) := by
      rw [hYinv, Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
        Matrix.trace_mul_comm]
    have hs := trace_eq_zero_of_cube_eq_one _ h3 hY1 hinv
    have hT := trace_tv_mul_tv hψv hφu
    have h2 : (2 : F) = 0 := CharTwo.two_eq_zero
    linear_combination -hT + hs - hψv - hφu - 2 * h2
  · intro hab
    refine ⟨cube_of_braid hτ hξ (braid_tv hφu hψv hab), ?_⟩
    intro heq
    have hx : (A2Mod.tv u φ : Matrix (Fin 3) (Fin 3) F) *ᵥ u =
        (A2Mod.tv v ψ : Matrix (Fin 3) (Fin 3) F) *ᵥ u := by
      rw [heq]
    rw [A2Mod.tv_mulVec hφu, A2Mod.tv_mulVec hψv, hφu, zero_smul, add_zero] at hx
    have h0 : (ψ ⬝ᵥ u) • v = 0 := by
      have h00 : u + 0 = u + (ψ ⬝ᵥ u) • v := by
        rw [add_zero]
        exact hx
      exact (add_left_cancel h00).symm
    rcases smul_eq_zero.mp h0 with ha | hv
    · rw [ha, zero_mul] at hab
      exact zero_ne_one hab
    · rw [hv, dotProduct_zero, mul_zero] at hab
      exact zero_ne_one hab


end Cube

section PGL
open scoped MatrixGroups Matrix
open CFSG.LargeExtraspecial

theorem kpgl_add_self {F : Type} [Field F] [CharP F 2] (ψ : Fin 3 → F) : ψ + ψ = 0 := by
  funext i
  rw [Pi.add_apply, Pi.zero_apply]
  first
    | rw [← two_mul, CharTwo.two_eq_zero, zero_mul]
    | exact CharTwo.add_self_eq_zero (ψ i)
    | simp [← two_mul, CharTwo.two_eq_zero]

theorem kpgl_tv_mul_self {F : Type} [Field F] [CharP F 2] {v ψ : Fin 3 → F}
    (h : ψ ⬝ᵥ v = 0) : A2Mod.tv v ψ * A2Mod.tv v ψ = 1 := by
  rw [A2Mod.tv_mul_tv_left h h, kpgl_add_self, A2Mod.tv_zero_right]

theorem kpgl_common_kernel {F : Type} [Field F] (ψ φ : Fin 3 → F) :
    ∃ w : Fin 3 → F, w ≠ 0 ∧ ψ ⬝ᵥ w = 0 ∧ φ ⬝ᵥ w = 0 := by
  let M : Matrix (Fin 3) (Fin 3) F := Matrix.of ![ψ, φ, 0]
  have hrow : ∀ j, M 2 j = 0 := by
    intro j
    fin_cases j <;> (first | rfl | simp [M])
  have hdet : M.det = 0 := Matrix.det_eq_zero_of_row_eq_zero 2 hrow
  obtain ⟨w, hw, hMw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hdet
  refine ⟨w, hw, ?_, ?_⟩
  · first
      | exact congrFun hMw 0
      | simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun hMw 0
  · first
      | exact congrFun hMw 1
      | simpa [M, Matrix.mulVec, dotProduct, Fin.sum_univ_three] using congrFun hMw 1

theorem kpgl_eq_one_of_mem_center {F : Type} [Field F]
    {g : Matrix.SpecialLinearGroup (Fin 3) F} {w : Fin 3 → F} (hw : w ≠ 0)
    (hg : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w)
    (hc : g ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 3) F)) : g = 1 := by
  obtain ⟨r, -, hr⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hc
  have h1 : Matrix.scalar (Fin 3) r *ᵥ w = w := by
    rw [hr]
    exact hg
  have h2 : ∀ i, r * w i = w i := by
    intro i
    have h3 := congrFun h1 i
    first
      | (rw [Matrix.scalar_apply, Matrix.mulVec_diagonal] at h3; exact h3)
      | simpa [Matrix.scalar_apply, Matrix.mulVec_diagonal] using h3
  obtain ⟨i, hi⟩ : ∃ i, w i ≠ 0 := by
    by_contra hcon
    exact hw (funext fun i => Classical.byContradiction fun hne => hcon ⟨i, hne⟩)
  have hr1 : r = 1 := mul_right_cancel₀ hi (by rw [one_mul]; exact h2 i)
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_one, ← hr, hr1, map_one]

theorem kpgl_toPGL_eq_one_iff {F : Type} [Field F]
    {g : Matrix.SpecialLinearGroup (Fin 3) F} {w : Fin 3 → F} (hw : w ≠ 0)
    (hg : (g : Matrix (Fin 3) (Fin 3) F) *ᵥ w = w) :
    Matrix.SpecialLinearGroup.toPGL g = 1 ↔ g = 1 := by
  have key : Matrix.SpecialLinearGroup.toPGL g = 1 ↔
      g ∈ Matrix.SpecialLinearGroup.toPGL.ker := MonoidHom.mem_ker.symm
  rw [key, Matrix.SpecialLinearGroup.toPGL_ker]
  constructor
  · exact kpgl_eq_one_of_mem_center hw hg
  · rintro rfl
    exact Subgroup.one_mem _

public theorem orderOf_toPGL_mul_eq_three_iff {F : Type} [Field F] [CharP F 2]
    {u φ v ψ : Fin 3 → F} (hφu : φ ⬝ᵥ u = 0) (hψv : ψ ⬝ᵥ v = 0) :
    orderOf (Matrix.SpecialLinearGroup.toPGL (A2Mod.tv v ψ) *
        Matrix.SpecialLinearGroup.toPGL (A2Mod.tv u φ)) = 3 ↔
      ((A2Mod.tv v ψ * A2Mod.tv u φ) ^ 3 = 1 ∧ A2Mod.tv u φ ≠ A2Mod.tv v ψ) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨w, hw, hψw, hφw⟩ := kpgl_common_kernel ψ φ
  have hτw : ((A2Mod.tv v ψ : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ w = w :=
    A2Mod.tv_mulVec_of_dotProduct_eq_zero hψw
  have hξw : ((A2Mod.tv u φ : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ w = w :=
    A2Mod.tv_mulVec_of_dotProduct_eq_zero hφw
  have hyw : ((A2Mod.tv v ψ * A2Mod.tv u φ : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := by
    rw [A2Mod.sl_mulVec_mul, hξw, hτw]
  have hpow : ∀ k : ℕ, (((A2Mod.tv v ψ * A2Mod.tv u φ) ^ k : Matrix.SpecialLinearGroup (Fin 3) F) :
      Matrix (Fin 3) (Fin 3) F) *ᵥ w = w := by
    intro k
    induction k with
    | zero => rw [pow_zero, Matrix.SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    | succ k ih => rw [pow_succ, A2Mod.sl_mulVec_mul, hyw, ih]
  have hτ : A2Mod.tv v ψ * A2Mod.tv v ψ = 1 := kpgl_tv_mul_self hψv
  have hτinv : (A2Mod.tv v ψ)⁻¹ = A2Mod.tv v ψ := inv_eq_of_mul_eq_one_right hτ
  have hy1 : A2Mod.tv v ψ * A2Mod.tv u φ = 1 ↔ A2Mod.tv u φ = A2Mod.tv v ψ := by
    rw [mul_eq_one_iff_inv_eq, hτinv]
    exact eq_comm
  have hmul : Matrix.SpecialLinearGroup.toPGL (A2Mod.tv v ψ * A2Mod.tv u φ) =
      Matrix.SpecialLinearGroup.toPGL (A2Mod.tv v ψ) *
        Matrix.SpecialLinearGroup.toPGL (A2Mod.tv u φ) :=
    map_mul _ _ _
  have hpow3 : Matrix.SpecialLinearGroup.toPGL ((A2Mod.tv v ψ * A2Mod.tv u φ) ^ 3) =
      Matrix.SpecialLinearGroup.toPGL (A2Mod.tv v ψ * A2Mod.tv u φ) ^ 3 :=
    map_pow _ _ _
  have hord : orderOf (Matrix.SpecialLinearGroup.toPGL (A2Mod.tv v ψ * A2Mod.tv u φ)) = 3 ↔
      Matrix.SpecialLinearGroup.toPGL (A2Mod.tv v ψ * A2Mod.tv u φ) ^ 3 = 1 ∧
        Matrix.SpecialLinearGroup.toPGL (A2Mod.tv v ψ * A2Mod.tv u φ) ≠ 1 :=
    orderOf_eq_prime_iff
  rw [← hmul, hord, ← hpow3, kpgl_toPGL_eq_one_iff hw (hpow 3), ne_eq,
    kpgl_toPGL_eq_one_iff hw hyw]
  constructor
  · rintro ⟨h3, h1⟩
    exact ⟨h3, fun h => h1 (hy1.mpr h)⟩
  · rintro ⟨h3, h1⟩
    exact ⟨h3, fun h => h1 (hy1.mp h)⟩

end PGL

section Std
open scoped MatrixGroups Matrix
open Matrix CFSG.LargeExtraspecial CFSG.RankThree.PartTwo.Sec3.Sims321

theorem char2_two {F : Type} [Field F] [CharP F 2] : (2 : F) = 0 := by
  exact_mod_cast CharP.cast_eq_zero F 2
theorem tv_involution {F : Type} [Field F] [CharP F 2] {u φ : Fin 3 → F} (h : φ ⬝ᵥ u = 0) :
    A2Mod.tv u φ * A2Mod.tv u φ = 1 := by
  have h2 : φ + φ = 0 := by
    funext i
    show φ i + φ i = 0
    linear_combination (φ i) * (char2_two (F := F))
  rw [A2Mod.tv_mul_tv_left h h, h2, A2Mod.tv_zero_right]

theorem dot_e1_e0 {F : Type} [Field F] :
    (Pi.single 1 1 : Fin 3 → F) ⬝ᵥ (Pi.single 0 1 : Fin 3 → F) = 0 := by
  simp [dotProduct, Pi.single_apply]

theorem tau0_ne_one {F : Type} [Field F] :
    A2Mod.tv (Pi.single 0 1 : Fin 3 → F) (Pi.single 1 1) ≠ 1 := by
  intro h
  have hm := congrArg
    (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 1 1 : Fin 3 → F)) h
  simp only [A2Mod.tv_mulVec (dot_e1_e0 (F := F)), Matrix.SpecialLinearGroup.coe_one,
    Matrix.one_mulVec] at hm
  have h0 := congrFun hm 0
  simp [dotProduct, Pi.single_apply] at h0

theorem tau0_cube {F : Type} [Field F] [CharP F 2] :
    (A2Mod.tv (Pi.single 0 1 : Fin 3 → F) (Pi.single 1 1)) ^ 3 =
      A2Mod.tv (Pi.single 0 1 : Fin 3 → F) (Pi.single 1 1) := by
  rw [pow_three, tv_involution (dot_e1_e0 (F := F)), mul_one]

theorem exists_tv_of_involution' {F : Type} [Field F] [CharP F 2] {ξ : SL(3,F)}
    (hξ : ξ * ξ = 1) (hξ1 : ξ ≠ 1) :
    ∃ u φ : Fin 3 → F, u ≠ 0 ∧ φ ≠ 0 ∧ φ ⬝ᵥ u = 0 ∧ ξ = A2Mod.tv u φ := by
  have hτ := tv_involution (dot_e1_e0 (F := F))
  obtain ⟨h, hh⟩ := exists_conj_eq_of_involution _ _ hτ tau0_ne_one hξ hξ1
  rw [A2Mod.conj_tv] at hh
  refine ⟨(h : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 0 1 : Fin 3 → F),
    A2Mod.contra h (Pi.single 1 1), ?_, ?_, ?_, hh⟩
  · intro h0
    have h1 := (A2Mod.sl_mulVec_eq_zero_iff h).mp h0
    have h2 := congrFun h1 0
    simp at h2
  · intro h0
    have h1 := (A2Mod.contra_eq_zero_iff h).mp h0
    have h2 := congrFun h1 1
    simp at h2
  · rw [A2Mod.contra_dotProduct_mulVec]
    exact dot_e1_e0

noncomputable def parTv {F : Type} [Field F] (a c d : F) : SL(3, F) :=
  A2Mod.tv ![a, 1, c] ![1, a + d * c, d]

theorem par_dot {F : Type} [Field F] [CharP F 2] (a c d : F) :
    (![1, a + d * c, d] : Fin 3 → F) ⬝ᵥ (![a, 1, c] : Fin 3 → F) = 0 := by
  have e : (![1, a + d * c, d] : Fin 3 → F) ⬝ᵥ (![a, 1, c] : Fin 3 → F) =
      1 * a + (a + d * c) * 1 + d * c := by
    simp [dotProduct, Fin.sum_univ_three]
  rw [e]
  linear_combination (a + d * c) * (char2_two (F := F))

theorem par_mul_self {F : Type} [Field F] [CharP F 2] (a c d : F) :
    parTv a c d * parTv a c d = 1 :=
  tv_involution (par_dot a c d)

theorem par_cube {F : Type} [Field F] [CharP F 2] (a c d : F) :
    (A2Mod.tv (Pi.single 0 1 : Fin 3 → F) (Pi.single 1 1) * parTv a c d) ^ 3 = 1 ∧
      parTv a c d ≠ A2Mod.tv (Pi.single 0 1 : Fin 3 → F) (Pi.single 1 1) := by
  have hval : ((Pi.single 1 1 : Fin 3 → F) ⬝ᵥ (![a, 1, c] : Fin 3 → F)) *
      ((![1, a + d * c, d] : Fin 3 → F) ⬝ᵥ (Pi.single 0 1 : Fin 3 → F)) = 1 := by
    simp [dotProduct, Pi.single_apply]
  exact (cube_iff_of_tv (par_dot a c d) (dot_e1_e0 (F := F))).mpr hval

theorem par_inj {F : Type} [Field F] [CharP F 2] {a c d a' c' d' : F}
    (h : parTv a c d = parTv a' c' d') : a = a' ∧ c = c' ∧ d = d' := by
  have hx : ∀ x : Fin 3 → F,
      x + ((![1, a + d * c, d] : Fin 3 → F) ⬝ᵥ x) • (![a, 1, c] : Fin 3 → F) =
        x + ((![1, a' + d' * c', d'] : Fin 3 → F) ⬝ᵥ x) • (![a', 1, c'] : Fin 3 → F) := by
    intro x
    rw [← A2Mod.tv_mulVec (par_dot a c d) x, ← A2Mod.tv_mulVec (par_dot a' c' d') x]
    exact congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) *ᵥ x) h
  have hs0 := add_left_cancel (hx (Pi.single 0 1))
  have hs2 := add_left_cancel (hx (Pi.single 2 1))
  have ha := congrFun hs0 0
  have hc := congrFun hs0 2
  have hd := congrFun hs2 1
  simp [dotProduct, Pi.single_apply] at ha hc hd
  exact ⟨ha, hc, hd⟩

theorem tv_eq_parTv {F : Type} [Field F] [CharP F 2] {u φ : Fin 3 → F} (hu1 : u 1 = 1)
    (hφ0 : φ 0 = 1) (hφu : φ ⬝ᵥ u = 0) :
    A2Mod.tv u φ = parTv (u 0) (u 2) (φ 2) := by
  have hu : u = ![u 0, 1, u 2] := by
    funext i
    fin_cases i <;> simp [hu1]
  have hexp : φ ⬝ᵥ u = φ 0 * u 0 + φ 1 * u 1 + φ 2 * u 2 := by
    simp [dotProduct, Fin.sum_univ_three]
  have h1 : φ 1 = u 0 + φ 2 * u 2 := by
    rw [hexp, hφ0, hu1] at hφu
    linear_combination hφu - (u 0 + φ 2 * u 2) * (char2_two (F := F))
  have hφ : φ = ![1, u 0 + φ 2 * u 2, φ 2] := by
    funext i
    fin_cases i <;> simp [hφ0, h1]
  have e : A2Mod.tv u φ = A2Mod.tv ![u 0, 1, u 2] ![1, u 0 + φ 2 * u 2, φ 2] := by
    rw [← hu, ← hφ]
  exact e

theorem exists_parTv {F : Type} [Field F] [CharP F 2] {ξ : SL(3, F)}
    (hξ : ξ * ξ = 1) (hξ1 : ξ ≠ 1)
    (hc : (A2Mod.tv (Pi.single 0 1 : Fin 3 → F) (Pi.single 1 1) * ξ) ^ 3 = 1)
    (hne : ξ ≠ A2Mod.tv (Pi.single 0 1 : Fin 3 → F) (Pi.single 1 1)) :
    ∃ a c d : F, ξ = parTv a c d := by
  obtain ⟨u, φ, _, _, hφu, rfl⟩ := exists_tv_of_involution' hξ hξ1
  have h1 : u 1 * φ 0 = 1 := by
    have h := (cube_iff_of_tv hφu (dot_e1_e0 (F := F))).mp ⟨hc, hne⟩
    simpa [dotProduct, Fin.sum_univ_three, Pi.single_apply] using h
  have hs0 : u 1 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h1
    exact zero_ne_one h1
  have hτ : A2Mod.tv u φ = A2Mod.tv ((u 1)⁻¹ • u) ((u 1) • φ) := by
    rw [A2Mod.tv_smul_left, smul_smul, inv_mul_cancel₀ hs0, one_smul]
  have hu1' : ((u 1)⁻¹ • u) 1 = 1 := by
    simp [inv_mul_cancel₀ hs0]
  have hφ0' : ((u 1) • φ) 0 = 1 := by
    simpa using h1
  have hφu' : ((u 1) • φ) ⬝ᵥ ((u 1)⁻¹ • u) = 0 := by
    simp [smul_dotProduct, dotProduct_smul, hφu]
  exact ⟨((u 1)⁻¹ • u) 0, ((u 1)⁻¹ • u) 2, ((u 1) • φ) 2,
    hτ.trans (tv_eq_parTv hu1' hφ0' hφu')⟩

theorem card_partners_sl_std {F : Type} [Field F] [Finite F] [CharP F 2] :
    Nat.card {ξ : SL(3,F) // ξ * ξ = 1 ∧ ξ ≠ A2Mod.tv (Pi.single 0 1) (Pi.single 1 1) ∧
      (A2Mod.tv (Pi.single 0 1) (Pi.single 1 1) * ξ) ^ 3 = 1} = Nat.card F ^ 3 := by
  have hmem : ∀ p : F × F × F,
      parTv p.1 p.2.1 p.2.2 * parTv p.1 p.2.1 p.2.2 = 1 ∧
        parTv p.1 p.2.1 p.2.2 ≠ A2Mod.tv (Pi.single 0 1 : Fin 3 → F) (Pi.single 1 1) ∧
        (A2Mod.tv (Pi.single 0 1 : Fin 3 → F) (Pi.single 1 1) * parTv p.1 p.2.1 p.2.2) ^ 3 = 1 :=
    fun p => ⟨par_mul_self p.1 p.2.1 p.2.2, (par_cube p.1 p.2.1 p.2.2).2,
      (par_cube p.1 p.2.1 p.2.2).1⟩
  let f : F × F × F → {ξ : SL(3,F) // ξ * ξ = 1 ∧ ξ ≠ A2Mod.tv (Pi.single 0 1) (Pi.single 1 1) ∧
      (A2Mod.tv (Pi.single 0 1) (Pi.single 1 1) * ξ) ^ 3 = 1} :=
    fun p => ⟨parTv p.1 p.2.1 p.2.2, hmem p⟩
  have hinj : Function.Injective f := by
    rintro ⟨a, c, d⟩ ⟨a', c', d'⟩ h
    have h' : parTv a c d = parTv a' c' d' := congrArg Subtype.val h
    obtain ⟨rfl, rfl, rfl⟩ := par_inj h'
    rfl
  have hsurj : Function.Surjective f := by
    rintro ⟨ξ, hξ, hne, hc⟩
    have hξ1 : ξ ≠ 1 := by
      rintro rfl
      rw [mul_one, tau0_cube (F := F)] at hc
      exact tau0_ne_one hc
    obtain ⟨a, c, d, rfl⟩ := exists_parTv hξ hξ1 hc hne
    exact ⟨(a, c, d), rfl⟩
  refine (Nat.card_congr (Equiv.ofBijective f ⟨hinj, hsurj⟩)).symm.trans ?_
  rw [Nat.card_prod, Nat.card_prod]
  ring


end Std

section Trans

theorem eq_one_of_pow_two_of_odd {Z : Type} [Group Z] [Finite Z] (hZ : Odd (Nat.card Z))
    {z : Z} (h : z ^ 2 = 1) : z = 1 := by
  have h2 : orderOf z ∣ 2 := orderOf_dvd_of_pow_eq_one h
  have hn : orderOf z ∣ Nat.card Z := orderOf_dvd_natCard z
  rw [← orderOf_eq_one_iff]
  rcases (Nat.dvd_prime Nat.prime_two).mp h2 with h1 | h1
  · exact h1
  · exfalso
    rw [h1] at hn
    obtain ⟨k, hk⟩ := hZ
    omega

theorem exists_involution_lift_of_cover {M T : Type} [Group M] [Finite M] [Group T] (π : M →* T)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center M) (hodd : Odd (Nat.card π.ker))
    {x : T} (hx : orderOf x = 2) : ∃ ξ : M, ξ * ξ = 1 ∧ π ξ = x := by
  obtain ⟨x0, hx0⟩ := hπ x
  subst hx0
  have hx2 : π x0 ^ 2 = 1 := by
    have h := pow_orderOf_eq_one (π x0)
    rwa [hx] at h
  obtain ⟨k, hk⟩ := id hodd
  have hmem : x0 ^ 2 ∈ π.ker := by
    rw [MonoidHom.mem_ker, map_pow]
    exact hx2
  have hw : (⟨x0 ^ 2, hmem⟩ : π.ker) ^ Nat.card π.ker = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp (orderOf_dvd_natCard _)
  have hw' : (x0 ^ 2) ^ Nat.card π.ker = 1 := by
    have h := congrArg Subtype.val hw
    rw [Subgroup.coe_pow] at h
    exact h
  refine ⟨x0 ^ Nat.card π.ker, ?_, ?_⟩
  · rw [← pow_add, ← Nat.two_mul, pow_mul]
    exact hw'
  · rw [map_pow, hk, pow_succ, pow_mul, hx2, one_pow, one_mul]

theorem eq_of_involution_of_cover {M T : Type} [Group M] [Group T] [Finite M] (π : M →* T)
    (hker : π.ker ≤ Subgroup.center M) (hodd : Odd (Nat.card π.ker))
    {ξ η : M} (hξ : ξ * ξ = 1) (hη : η * η = 1) (h : π ξ = π η) : ξ = η := by
  obtain ⟨z, hzdef⟩ : ∃ z : M, z = ξ⁻¹ * η := ⟨_, rfl⟩
  have hzk : z ∈ π.ker := by
    rw [MonoidHom.mem_ker, hzdef, map_mul, map_inv, h, inv_mul_cancel]
  have hc : Commute ξ z := Subgroup.mem_center_iff.mp (hker hzk) ξ
  have hξz : ξ * z = η := by
    rw [hzdef, mul_inv_cancel_left]
  have hξ2 : ξ ^ 2 = 1 := by
    rw [pow_two]
    exact hξ
  have hη2 : η ^ 2 = 1 := by
    rw [pow_two]
    exact hη
  have hkey : (ξ * z) ^ 2 = z ^ 2 := by
    rw [hc.mul_pow, hξ2, one_mul]
  have hz2 : z ^ 2 = 1 := by
    rw [← hkey, hξz]
    exact hη2
  have hz1 : (⟨z, hzk⟩ : π.ker) = 1 := by
    apply eq_one_of_pow_two_of_odd hodd
    apply Subtype.ext
    simpa using hz2
  have hz1' : z = 1 := congrArg Subtype.val hz1
  rw [hz1', mul_one] at hξz
  exact hξz

theorem card_partners_of_cover {M T : Type} [Group M] [Finite M] [Group T] (π : M →* T)
    (hπ : Function.Surjective π) (hker : π.ker ≤ Subgroup.center M) (hodd : Odd (Nat.card π.ker))
    (τ : M) (hτ : τ * τ = 1) (hτ1 : π τ ≠ 1) (P : M → Prop)
    (hP : ∀ ξ : M, ξ * ξ = 1 → (orderOf (π τ * π ξ) = 3 ↔ P ξ)) :
    Nat.card {x : T // orderOf x = 2 ∧ orderOf (π τ * x) = 3} =
      Nat.card {ξ : M // ξ * ξ = 1 ∧ P ξ} := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hτ2 : π τ * π τ = 1 := by
    rw [← map_mul, hτ, map_one]
  have hτsq : π τ ^ 2 = 1 := by
    rw [pow_two]
    exact hτ2
  have hwd : ∀ ξ : M, ξ * ξ = 1 → P ξ → orderOf (π ξ) = 2 ∧ orderOf (π τ * π ξ) = 3 := by
    intro ξ hξ hPξ
    have h3 : orderOf (π τ * π ξ) = 3 := (hP ξ hξ).mpr hPξ
    have hξsq : π ξ ^ 2 = 1 := by
      rw [pow_two, ← map_mul, hξ, map_one]
    have hξ1 : π ξ ≠ 1 := by
      intro h1
      rw [h1, mul_one, orderOf_eq_prime hτsq hτ1] at h3
      norm_num at h3
    exact ⟨orderOf_eq_prime hξsq hξ1, h3⟩
  refine Nat.card_congr (Equiv.ofBijective
    (fun ξ : {ξ : M // ξ * ξ = 1 ∧ P ξ} =>
      (⟨π ξ.1, hwd ξ.1 ξ.2.1 ξ.2.2⟩ : {x : T // orderOf x = 2 ∧ orderOf (π τ * x) = 3})) ⟨?_, ?_⟩).symm
  · rintro ⟨ξ₁, h₁, _⟩ ⟨ξ₂, h₂, _⟩ hf
    have hπeq : π ξ₁ = π ξ₂ := congrArg Subtype.val hf
    exact Subtype.ext (eq_of_involution_of_cover π hker hodd h₁ h₂ hπeq)
  · rintro ⟨x, hx2, hx3⟩
    obtain ⟨ξ, hξsq, hξx⟩ := exists_involution_lift_of_cover π hπ hker hodd hx2
    have hPξ : P ξ := (hP ξ hξsq).mp (by rw [hξx]; exact hx3)
    exact ⟨⟨ξ, hξsq, hPξ⟩, Subtype.ext hξx⟩


end Trans

section Glue
open scoped MatrixGroups Matrix
open CFSG.LargeExtraspecial

theorem projSL_eq_range (n : ℕ) (F : Type) [Field F] :
    CFSG.PGLModel.projSL n F =
      (Matrix.SpecialLinearGroup.toPGL : SL(n, F) →* PGL(n, F)).range := by
  ext x
  constructor
  · intro hx
    obtain ⟨g, hg, rfl⟩ := Subgroup.mem_map.1 hx
    have hdet : (g : Matrix (Fin n) (Fin n) F).det = 1 := by
      have := (MonoidHom.mem_ker.1 hg)
      simpa [Units.ext_iff] using this
    refine ⟨⟨(g : Matrix (Fin n) (Fin n) F), hdet⟩, ?_⟩
    change Matrix.ProjGenLinGroup.mk (Matrix.SpecialLinearGroup.toGL
      ⟨(g : Matrix (Fin n) (Fin n) F), hdet⟩) = Matrix.ProjGenLinGroup.mk g
    congr 1
    ext1
    rfl
  · rintro ⟨s, rfl⟩
    refine Subgroup.mem_map.2 ⟨Matrix.SpecialLinearGroup.toGL s, ?_, rfl⟩
    rw [MonoidHom.mem_ker]
    ext
    simp

noncomputable def piSL (F : Type) [Field F] : SL(3, F) →* ↥(CFSG.PGLModel.projSL 3 F) :=
  (Matrix.SpecialLinearGroup.toPGL : SL(3, F) →* PGL(3, F)).codRestrict
    (CFSG.PGLModel.projSL 3 F) (fun s => by rw [projSL_eq_range]; exact ⟨s, rfl⟩)

theorem piSL_surjective (F : Type) [Field F] : Function.Surjective (piSL F) := by
  rintro ⟨x, hx⟩
  rw [projSL_eq_range] at hx
  obtain ⟨s, rfl⟩ := hx
  exact ⟨s, rfl⟩

theorem ker_piSL (F : Type) [Field F] : (piSL F).ker = Subgroup.center SL(3, F) := by
  rw [piSL, MonoidHom.ker_codRestrict]
  exact Matrix.SpecialLinearGroup.toPGL_ker

theorem pow_three_eq_one_of_mem_center {F : Type} [Field F] {g : SL(3, F)}
    (hg : g ∈ Subgroup.center SL(3, F)) : g ^ 3 = 1 := by
  obtain ⟨r, hr, hrg⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hg
  have hr3 : r ^ 3 = 1 := by simpa using hr
  have h : ((g ^ 3 : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) = 1 := by
    rw [Matrix.SpecialLinearGroup.coe_pow, ← hrg, ← map_pow, hr3, map_one]
  exact Subtype.ext h

theorem odd_card_center_sl (F : Type) [Field F] [Finite F] :
    Odd (Nat.card (Subgroup.center SL(3, F))) := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  by_contra hodd
  have h2 : 2 ∣ Nat.card (Subgroup.center SL(3, F)) := by
    rcases Nat.even_or_odd (Nat.card (Subgroup.center SL(3, F))) with he | ho
    · exact even_iff_two_dvd.1 he
    · exact absurd ho hodd
  obtain ⟨g, hg⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center SL(3, F)) 2 h2
  have h3 : (g : SL(3, F)) ^ 3 = 1 := pow_three_eq_one_of_mem_center g.2
  have h4 : orderOf (g : SL(3, F)) ∣ 3 := orderOf_dvd_of_pow_eq_one h3
  rw [Subgroup.orderOf_coe, hg] at h4
  omega

theorem ker_piSL_le_center (F : Type) [Field F] : (piSL F).ker ≤ Subgroup.center SL(3, F) :=
  (ker_piSL F).le

theorem odd_card_ker_piSL (F : Type) [Field F] [Finite F] : Odd (Nat.card (piSL F).ker) := by
  rw [ker_piSL]
  exact odd_card_center_sl F

theorem card_partners_sl {F : Type} [Field F] [Finite F] [CharP F 2] (τ : SL(3, F))
    (hτ : τ * τ = 1) (hτ1 : τ ≠ 1) :
    Nat.card {ξ : SL(3, F) // ξ * ξ = 1 ∧ ξ ≠ τ ∧ (τ * ξ) ^ 3 = 1} = Nat.card F ^ 3 := by
  set τ0 : SL(3, F) := A2Mod.tv (Pi.single 0 1) (Pi.single 1 1) with hτ0
  have hdot : (Pi.single 1 1 : Fin 3 → F) ⬝ᵥ (Pi.single 0 1 : Fin 3 → F) = 0 := by
    simp [dotProduct, Fin.sum_univ_three, Pi.single_apply]
  have hτ0sq : τ0 * τ0 = 1 := tv_involution hdot
  have hτ01 : τ0 ≠ 1 := by
    intro h
    have h1 := congrArg (fun g : SL(3, F) =>
      (g : Matrix (Fin 3) (Fin 3) F) *ᵥ (Pi.single 1 1 : Fin 3 → F)) h
    simp only [hτ0, A2Mod.tv_mulVec hdot] at h1
    simp at h1
    have h2 := congrFun h1 0
    simp at h2
  obtain ⟨h, hh⟩ := CFSG.RankThree.PartTwo.Sec3.Sims321.exists_conj_eq_of_involution τ0 τ hτ0sq
    hτ01 hτ hτ1
  rw [← card_partners_sl_std]
  set φ : MulAut SL(3, F) := MulAut.conj h⁻¹ with hφ
  have hφτ : φ τ = τ0 := by
    rw [hφ, MulAut.conj_apply, hh]
    group
  refine Nat.card_congr (Equiv.subtypeEquiv φ.toEquiv ?_)
  intro ξ
  show (ξ * ξ = 1 ∧ ξ ≠ τ ∧ (τ * ξ) ^ 3 = 1) ↔
    (φ ξ * φ ξ = 1 ∧ φ ξ ≠ τ0 ∧ (τ0 * φ ξ) ^ 3 = 1)
  rw [← hφτ, ← map_mul, ← map_mul, ← map_pow, MulEquiv.map_eq_one_iff, MulEquiv.map_eq_one_iff]
  simp only [ne_eq, EmbeddingLike.apply_eq_iff_eq]

theorem card_s3Partners_projSL {F : Type} [Field F] [Finite F] [CharP F 2]
    (t : ↥(CFSG.PGLModel.projSL 3 F)) (ht : orderOf t = 2) :
    Nat.card {x : ↥(CFSG.PGLModel.projSL 3 F) // orderOf x = 2 ∧ orderOf (t * x) = 3} =
      Nat.card F ^ 3 := by
  obtain ⟨τ, hτ, rfl⟩ := exists_involution_lift_of_cover (piSL F) (piSL_surjective F)
    (ker_piSL_le_center F) (odd_card_ker_piSL F) ht
  have hτ1' : piSL F τ ≠ 1 := by
    intro h
    rw [h, orderOf_one] at ht
    omega
  have hτ1 : τ ≠ 1 := fun h => hτ1' (by rw [h, map_one])
  rw [card_partners_of_cover (piSL F) (piSL_surjective F) (ker_piSL_le_center F)
    (odd_card_ker_piSL F) τ hτ hτ1' (fun ξ => (τ * ξ) ^ 3 = 1 ∧ ξ ≠ τ) ?_]
  · exact (Nat.card_congr (Equiv.subtypeEquiv (Equiv.refl _)
      (fun ξ => by constructor <;> rintro ⟨h1, h2, h3⟩ <;> tauto))).trans (card_partners_sl τ hτ hτ1)
  · intro ξ hξ
    by_cases hξ1 : ξ = 1
    · subst hξ1
      have h3 : (τ * 1) ^ 3 ≠ 1 := by
        have : (τ * 1) ^ 3 = τ := by
          rw [mul_one, pow_succ, pow_two, hτ, one_mul]
        rw [this]
        exact hτ1
      constructor
      · intro h
        rw [map_one, mul_one, ht] at h
        omega
      · rintro ⟨h, -⟩
        exact absurd h h3
    · obtain ⟨u, φ, hu, hφ, hφu, hξeq⟩ := exists_tv_of_involution' hξ hξ1
      obtain ⟨v, ψ, hv, hψ, hψv, hτeq⟩ := exists_tv_of_involution' hτ hτ1
      subst hξeq
      subst hτeq
      rw [← Subgroup.orderOf_coe]
      exact orderOf_toPGL_mul_eq_three_iff hφu hψv

@[expose] def S3CountOK (T : Type) [Group T] : Prop :=
  ∀ t : T, orderOf t = 2 → ¬ 3 ∣ Nat.card {x : T // orderOf x = 2 ∧ orderOf (t * x) = 3}

theorem s3CountOK_of_mulEquiv {T T' : Type} [Group T] [Group T'] (e : T ≃* T')
    (h : S3CountOK T') : S3CountOK T := by
  intro t ht
  have ht' : orderOf (e t) = 2 := by rw [MulEquiv.orderOf_eq]; exact ht
  have hcard : Nat.card {x : T // orderOf x = 2 ∧ orderOf (t * x) = 3} =
      Nat.card {x : T' // orderOf x = 2 ∧ orderOf (e t * x) = 3} := by
    refine Nat.card_congr (Equiv.subtypeEquiv e.toEquiv ?_)
    intro x
    simp only [MulEquiv.toEquiv_eq_coe, MulEquiv.coe_toEquiv, MulEquiv.orderOf_eq, ← map_mul]
  rw [hcard]
  exact h (e t) ht'

theorem s3CountOK_projSL (f : ℕ) (hf : 1 ≤ f) :
    S3CountOK ↥(CFSG.PGLModel.projSL 3 (GaloisField 2 f)) := by
  intro t ht
  rw [card_s3Partners_projSL t ht, GaloisField.card 2 f (by omega), ← pow_mul]
  intro h
  have := Nat.Prime.dvd_of_dvd_pow Nat.prime_three h
  omega


end Glue

end CFSG.RankThree.PartTwo.Sec15.F153L3K
