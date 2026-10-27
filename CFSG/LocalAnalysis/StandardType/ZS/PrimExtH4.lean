module

public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtBond
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtSetting
import CFSG.LocalAnalysis.StandardType.ZS.Basic
import CFSG.LocalAnalysis.StandardType.ZS.BlockSuccRankOne
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtH3Gen

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

open scoped Matrix

private theorem isUnit_det_of_mul_self {n : ℕ} {K : Type} [Field K]
    (M : Matrix (Fin n) (Fin n) K) (h : M * M = 1) : IsUnit M.det :=
  isUnit_iff_exists.mpr ⟨M.det, by rw [← Matrix.det_mul, h, Matrix.det_one],
    by rw [← Matrix.det_mul, h, Matrix.det_one]⟩

private theorem isUnit_diagSignMat_det_five {n : ℕ} (i : Fin n) :
    IsUnit (diagSignMat i : Matrix (Fin n) (Fin n) (ZMod p)).det := by
  rw [show (diagSignMat i : Matrix (Fin n) (Fin n) (ZMod p)).det = -1 by
    rw [show (diagSignMat i : Matrix (Fin n) (Fin n) (ZMod p)) =
      Matrix.diagonal (fun j => if j = i then -1 else 1) from rfl, Matrix.det_diagonal]
    rw [Finset.prod_eq_single i]
    · simp
    · intro j _ hji; simp [hji]
    · intro hi; exact absurd (Finset.mem_univ i) hi]
  exact isUnit_neg_one

private theorem exists_toMatrix_eq_of_isUnit_det {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) U)
    {M : Matrix (Fin n) (Fin n) (ZMod p)} (hdet : IsUnit M.det) :
    ∃ g : U ≃ₗ[ZMod p] U, LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = M := by
  let g : U ≃ₗ[ZMod p] U := LinearEquiv.ofIsUnitDet (v := f) (v' := f)
    (f := Matrix.toLin f f M) (by rw [LinearMap.toMatrix_toLin]; exact hdet)
  exact ⟨g, by dsimp only [g]; rw [LinearEquiv.coe_ofIsUnitDet, LinearMap.toMatrix_toLin]⟩

private theorem exists_mem_h4Mats_of_gen {α : ZMod p}
    (f : Module.Basis (Fin 5) (ZMod p) U)
    (hdiag : ∀ j : Fin 3, IsUnit (diagSignMat j : Matrix (Fin 3) (Fin 3) (ZMod p)).det)
    (gen : ∀ {M : Matrix (Fin 4) (Fin 4) (ZMod p)}, M ∈ h4BlockMats α → IsUnit M.det →
      ∃ g ∈ basisClosure f (h4Mats α),
        LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = Matrix.blockSucc M)
    (h3id : (h3BlockMat α : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      1 - Matrix.vecMulVec ![α - 2, 1, 1] ![-(1 / 2), (1 + α) / 2, 1 / 2])
    (h3mem : Matrix.blockSucc (h3BlockMat α) ∈ h4BlockMats α)
    (hdmem : ∀ j : Fin 3, Matrix.blockSucc (diagSignMat j) ∈ h4BlockMats α)
    (h3det : IsUnit (h3BlockMat α : Matrix (Fin 3) (Fin 3) (ZMod p)).det)
    (h4det : IsUnit (h4BlockMat α : Matrix (Fin 4) (Fin 4) (ZMod p)).det) :
    (∀ i : Fin 5, i.val < 3 → ∃ g ∈ basisClosure f (h4Mats α),
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = diagSignMat i) ∧
    (∃ g ∈ basisClosure f (h4Mats α),
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = Matrix.blockSucc (h4BlockMat α)) ∧
    ∃ g ∈ basisClosure f (h4Mats α), LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
      1 - Matrix.vecMulVec ![α - 2, 1, 1, 0, 0] ![-(1 / 2), (1 + α) / 2, 1 / 2, 0, 0] := by
  refine ⟨?_, ?_, ?_⟩
  · intro i hi
    obtain ⟨gh0, hgh0, hhm0⟩ := gen (M := Matrix.blockSucc (diagSignMat 0)) (hdmem 0)
      (by rw [Matrix.det_blockSucc]; exact hdiag 0)
    obtain ⟨gh1, hgh1, hhm1⟩ := gen (M := Matrix.blockSucc (diagSignMat 1)) (hdmem 1)
      (by rw [Matrix.det_blockSucc]; exact hdiag 1)
    obtain ⟨gh2, hgh2, hhm2⟩ := gen (M := Matrix.blockSucc (diagSignMat 2)) (hdmem 2)
      (by rw [Matrix.det_blockSucc]; exact hdiag 2)
    have hi012 : i.val = 0 ∨ i.val = 1 ∨ i.val = 2 := by omega
    rcases hi012 with h | h | h
    · rw [show i = 0 from Fin.ext (by omega)]
      exact ⟨gh0, hgh0, by rw [hhm0, blockSucc_diagSignMat, blockSucc_diagSignMat]; rfl⟩
    · rw [show i = 1 from Fin.ext (by omega)]
      exact ⟨gh1, hgh1, by rw [hhm1, blockSucc_diagSignMat, blockSucc_diagSignMat]; rfl⟩
    · rw [show i = 2 from Fin.ext (by omega)]
      exact ⟨gh2, hgh2, by rw [hhm2, blockSucc_diagSignMat, blockSucc_diagSignMat]; rfl⟩
  · obtain ⟨ga2, hga2, hma2⟩ := gen (M := h4BlockMat α) (Set.mem_insert _ _) h4det
    exact ⟨ga2, hga2, hma2⟩
  · obtain ⟨ga1, hga1, hma1⟩ := gen (M := Matrix.blockSucc (h3BlockMat α)) h3mem
      (by rw [Matrix.det_blockSucc]; exact h3det)
    refine ⟨ga1, hga1, ?_⟩
    rw [hma1, h3id, Matrix.blockSucc_one_sub_vecMulVec, Matrix.blockSucc_one_sub_vecMulVec]
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem exists_mem_h4Mats (hp : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1)
    (f : Module.Basis (Fin 5) (ZMod p) U) :
    (∀ i : Fin 5, i.val < 3 → ∃ g ∈ basisClosure f (h4Mats α),
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = diagSignMat i) ∧
    (∃ g ∈ basisClosure f (h4Mats α),
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = Matrix.blockSucc (h4BlockMat α)) ∧
    ∃ g ∈ basisClosure f (h4Mats α), LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
      1 - Matrix.vecMulVec ![α - 2, 1, 1, 0, 0] ![-(1 / 2), (1 + α) / 2, 1 / 2, 0, 0] := by
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hα3 : α ^ 3 = 2 * α + 1 := by linear_combination (norm := ring_nf) (α + 1) * hα
  have hdiag : ∀ j : Fin 3, IsUnit (diagSignMat j : Matrix (Fin 3) (Fin 3) (ZMod p)).det := by
    intro j
    rw [diagSignMat, Matrix.det_diagonal]
    simp
  have h3inv : (h3BlockMat α : Matrix (Fin 3) (Fin 3) (ZMod p)) * h3BlockMat α = 1 := by
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [h3BlockMat, Matrix.mul_apply, Fin.sum_univ_three, Matrix.cons_val] <;>
      field_simp [h2ne] <;> ring_nf <;> simp only [hα] <;> ring
  have h3det : IsUnit (h3BlockMat α : Matrix (Fin 3) (Fin 3) (ZMod p)).det :=
    isUnit_det_of_mul_self _ h3inv
  have h4inv : (h4BlockMat α : Matrix (Fin 4) (Fin 4) (ZMod p)) * h4BlockMat α = 1 := by
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [h4BlockMat, Matrix.mul_apply, Fin.sum_univ_four, Matrix.cons_val] <;>
      field_simp [h2ne] <;> ring_nf <;> simp only [hα] <;> ring
  have h4det : IsUnit (h4BlockMat α : Matrix (Fin 4) (Fin 4) (ZMod p)).det :=
    isUnit_det_of_mul_self _ h4inv
  have h3id : (h3BlockMat α : Matrix (Fin 3) (Fin 3) (ZMod p)) =
      1 - Matrix.vecMulVec ![α - 2, 1, 1] ![-(1 / 2), (1 + α) / 2, 1 / 2] := by
    ext r c
    fin_cases r <;> fin_cases c <;>
      simp [h3BlockMat] <;>
      (try field_simp [h2ne]) <;> (try linear_combination (norm := ring_nf) hα) <;>
      (try linear_combination (norm := ring_nf) (-hα))
  have h3mem : Matrix.blockSucc (h3BlockMat α) ∈ h4BlockMats α :=
    Set.mem_insert_of_mem (h4BlockMat α) ⟨h3BlockMat α, by simp [h3BlockMats], rfl⟩
  have hdmem : ∀ j : Fin 3, Matrix.blockSucc (diagSignMat j) ∈ h4BlockMats α := by
    intro j
    refine Set.mem_insert_of_mem (h4BlockMat α) ⟨diagSignMat j, ?_, rfl⟩
    fin_cases j <;> simp [h3BlockMats]
  have gen : ∀ {M : Matrix (Fin 4) (Fin 4) (ZMod p)}, M ∈ h4BlockMats α → IsUnit M.det →
      ∃ g ∈ basisClosure f (h4Mats α),
        LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) = Matrix.blockSucc M := by
    intro M hM hdet
    exact exists_mem_basisClosure_toMatrix_eq f ⟨M, hM, rfl⟩ (by rwa [Matrix.det_blockSucc])
  exact exists_mem_h4Mats_of_gen f hdiag gen h3id h3mem hdmem h3det h4det


private def mMat (α : ZMod p) : Matrix (Fin 4) (Fin 4) (ZMod p) :=
  diagSignMat (1 : Fin 4) * h4BlockMat α

private theorem mMat_sq (hp2 : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1) :
    mMat α * mMat α =
      Matrix.of ![![1, 0, 0, 0], ![0, (α - 1) / 2, (α - 1) / 2, -α / 2],
        ![0, -α / 2, α / 2, 1 / 2], ![0, α / 2, (2 - α) / 2, 1 / 2]] := by
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mMat, diagSignMat, h4BlockMat, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.of_apply]
  all_goals field_simp [h2ne]
  all_goals (try ring_nf)
  all_goals (try simp only [hα])
  all_goals (try ring)

private theorem mMat_pow_four (hp2 : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1) :
    (mMat α) ^ 4 =
      Matrix.of ![![1, 0, 0, 0], ![0, -α / 2, (2 - α) / 2, -1 / 2],
        ![0, -1 / 2, 1 / 2, (α + 1) / 2], ![0, 1 / 2, 1 / 2, (1 - α) / 2]] := by
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  have h2 : (mMat α) ^ 2 = Matrix.of ![![1, 0, 0, 0], ![0, (α - 1) / 2, (α - 1) / 2, -α / 2],
        ![0, -α / 2, α / 2, 1 / 2], ![0, α / 2, (2 - α) / 2, 1 / 2]] := by
    rw [pow_two]; exact mMat_sq hp2 hα
  have h4 : (mMat α) ^ 4 = ((mMat α) ^ 2) ^ 2 := by rw [← pow_mul]
  rw [h4, h2, pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.of_apply]
  all_goals field_simp [h2ne]
  all_goals (try ring_nf)
  all_goals (try simp only [hα])
  all_goals (try ring)

private theorem mMat_pow_five (hp2 : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1) :
    (mMat α) ^ 5 = 1 := by
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  have h5 : (mMat α) ^ 5 = (mMat α) ^ 4 * mMat α := by
    rw [show (5 : ℕ) = 4 + 1 by norm_num, pow_succ]
  rw [h5, mMat_pow_four hp2 hα]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [mMat, diagSignMat, h4BlockMat, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, Matrix.of_apply]
  all_goals field_simp [h2ne]
  all_goals (try ring_nf)
  all_goals (try simp only [hα])
  all_goals (try ring)

private def nzMat (α : ZMod p) : Matrix (Fin 4) (Fin 4) (ZMod p) :=
  Matrix.of ![![1, 0, 0, 0], ![0, α / 2, (α - 2) / 2, -1 / 2],
    ![0, 1 / 2, -1 / 2, (α + 1) / 2], ![0, -1 / 2, -1 / 2, (1 - α) / 2]]

private theorem nzMat_eq (hp2 : p ≠ 2) (α : ZMod p) :
    nzMat α = h4BlockMat α * diagSignMat (2 : Fin 4) := by
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nzMat, diagSignMat, h4BlockMat, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals field_simp [h2ne]
  all_goals ring

private theorem nzMat_sq (hp2 : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1) :
    nzMat α * nzMat α =
      Matrix.of ![![1, 0, 0, 0], ![0, α / 2, (2 - α) / 2, -1 / 2],
        ![0, -1 / 2, -1 / 2, -(α + 1) / 2], ![0, -1 / 2, 1 / 2, (1 - α) / 2]] := by
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nzMat, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals field_simp [h2ne]
  all_goals (try ring_nf)
  all_goals (try simp only [hα])
  all_goals (try ring)

private theorem nzMat_pow_three (hp2 : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1) :
    (nzMat α) ^ 3 = 1 := by
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  have h3 : (nzMat α) ^ 3 = nzMat α * nzMat α * nzMat α := by
    rw [show (3 : ℕ) = 2 + 1 by norm_num, pow_add, pow_two, pow_one]
  rw [h3, nzMat_sq hp2 hα]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [nzMat, Matrix.mul_apply, Fin.sum_univ_four,
      Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
  all_goals field_simp [h2ne]
  all_goals (try ring_nf)
  all_goals (try simp only [hα])
  all_goals (try ring)

private theorem diag12_sq :
    ((diagSignMat (1 : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod p)) *
      diagSignMat (2 : Fin 4)) ^ 2 = 1 := by
  rw [pow_two]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [diagSignMat, Matrix.mul_apply, Fin.sum_univ_four]

private theorem mMat_ne_one (hp2 : p ≠ 2) (hp5 : p ≠ 5) {α : ZMod p}
    (hα : α ^ 2 = α + 1) : mMat α ≠ 1 := by
  intro h
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  have hentry : (mMat α) 1 1 = -(2 : ZMod p)⁻¹ * α := by
    simp [mMat, diagSignMat, h4BlockMat]
  rw [h] at hentry
  simp only [Matrix.one_apply, Fin.isValue, ↓reduceIte] at hentry
  have hαeq : α = -2 := by
    have h' := hentry
    field_simp [h2ne] at h'
    linear_combination h'
  have h5z : ((5 : ℤ) : ZMod p) = 0 := by
    have h4 : (4 : ZMod p) = -1 := by
      have h := hα
      rw [hαeq] at h
      norm_num at h
      exact h
    push_cast
    linear_combination h4
  have hdvd : (p : ℤ) ∣ 5 := (ZMod.intCast_zmod_eq_zero_iff_dvd (5 : ℤ) p).mp h5z
  have hdvd' : p ∣ 5 := by exact_mod_cast hdvd
  exact hp5 ((Nat.prime_dvd_prime_iff_eq (Fact.out : Nat.Prime p) (by norm_num)).mp hdvd')

private theorem nzMat_ne_one (hp2 : p ≠ 2) {α : ZMod p} : nzMat (p := p) α ≠ 1 := by
  intro h
  have hentry : (nzMat (p := p) α) 1 3 = -(2 : ZMod p)⁻¹ := by
    simp [nzMat]
    ring
  rw [h] at hentry
  simp only [Matrix.one_apply, Fin.isValue] at hentry
  exact inv_ne_zero (ZMod.prime_ne_zero p 2 hp2) (neg_eq_zero.mp hentry.symm)

private theorem diag12_ne_one (hp2 : p ≠ 2) :
    (((diagSignMat (1 : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod p)) *
      diagSignMat (2 : Fin 4)) : Matrix (Fin 4) (Fin 4) (ZMod p)) ≠ 1 := by
  intro h
  have hentry : (((diagSignMat (1 : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod p)) *
      diagSignMat (2 : Fin 4)) : Matrix (Fin 4) (Fin 4) (ZMod p)) 1 1 = -1 := by
    simp [diagSignMat, Matrix.mul_apply, Fin.sum_univ_four]
  rw [h] at hentry
  simp only [Matrix.one_apply, Fin.isValue, ↓reduceIte] at hentry
  exact (ZMod.prime_ne_zero p 2 hp2) (by linear_combination hentry)

private theorem orderOf_mMat (hp2 : p ≠ 2) (hp5 : p ≠ 5) {α : ZMod p}
    (hα : α ^ 2 = α + 1) : orderOf (mMat α) = 5 := by
  have : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  exact orderOf_eq_prime (mMat_pow_five hp2 hα) (mMat_ne_one hp2 hp5 hα)

private theorem orderOf_nzMat (hp2 : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1) :
    orderOf (nzMat (p := p) α) = 3 := by
  have : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  exact orderOf_eq_prime (nzMat_pow_three hp2 hα) (nzMat_ne_one hp2)

private theorem orderOf_diag12 (hp2 : p ≠ 2) :
    orderOf ((diagSignMat (1 : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod p)) *
      diagSignMat (2 : Fin 4)) = 2 := by
  have : Fact (Nat.Prime 2) := ⟨by norm_num⟩
  exact orderOf_eq_prime diag12_sq (diag12_ne_one hp2)


private noncomputable def toMatHom5 (f : Module.Basis (Fin 5) (ZMod p) U) :
    (U ≃ₗ[ZMod p] U) →* Matrix (Fin 5) (Fin 5) (ZMod p) where
  toFun g := LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U)
  map_one' := by rw [LinearEquiv.coe_toLinearMap_one]; exact LinearMap.toMatrix_one f
  map_mul' g h := by rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul]

private theorem blockSucc_diagSignMat_one :
    (Matrix.blockSucc (diagSignMat (1 : Fin 4)) : Matrix (Fin 5) (Fin 5) (ZMod p)) =
      diagSignMat (1 : Fin 5) := by
  rw [blockSucc_diagSignMat]
  congr 1

private theorem blockSucc_diagSignMat_two :
    (Matrix.blockSucc (diagSignMat (2 : Fin 4)) : Matrix (Fin 5) (Fin 5) (ZMod p)) =
      diagSignMat (2 : Fin 5) := by
  rw [blockSucc_diagSignMat]
  congr 1

private theorem toMatHom5_injective (f : Module.Basis (Fin 5) (ZMod p) U) :
    Function.Injective (toMatHom5 f) := by
  intro g h hgh
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrixAlgEquiv f).injective
  exact hgh

theorem orderOf_mul_h4Triple (hp : p ≠ 2) (hp5 : p ≠ 5) {α : ZMod p} (hα : α ^ 2 = α + 1)
    (f : Module.Basis (Fin 5) (ZMod p) U) {x y z : U ≃ₗ[ZMod p] U}
    (hx : LinearMap.toMatrix f f (x : U →ₗ[ZMod p] U) = diagSignMat 1)
    (hy : LinearMap.toMatrix f f (y : U →ₗ[ZMod p] U) = Matrix.blockSucc (h4BlockMat α))
    (hz : LinearMap.toMatrix f f (z : U →ₗ[ZMod p] U) = diagSignMat 2) :
    orderOf (x * y) = 5 ∧ orderOf (y * z) = 3 ∧ orderOf (x * z) = 2 := by
  have hb : Function.Injective (Matrix.blockSuccMonoidHom (ZMod p) 4) := by
    intro a b hab
    exact Matrix.blockSucc_injective (by simpa only [Matrix.blockSuccMonoidHom_apply] using hab)
  have hxy : toMatHom5 f (x * y) = Matrix.blockSucc (mMat α) := by
    simp only [toMatHom5, MonoidHom.coe_mk, OneHom.coe_mk, map_mul]
    rw [hx, hy, ← blockSucc_diagSignMat_one, ← Matrix.blockSucc_mul]
    rfl
  have hyz : toMatHom5 f (y * z) = Matrix.blockSucc (nzMat α) := by
    simp only [toMatHom5, MonoidHom.coe_mk, OneHom.coe_mk, map_mul]
    rw [hy, hz, ← blockSucc_diagSignMat_two, ← Matrix.blockSucc_mul, ← nzMat_eq hp]
  have hxz : toMatHom5 f (x * z) = Matrix.blockSucc
      ((diagSignMat (1 : Fin 4) : Matrix (Fin 4) (Fin 4) (ZMod p)) * diagSignMat 2) := by
    simp only [toMatHom5, MonoidHom.coe_mk, OneHom.coe_mk, map_mul]
    rw [hx, hz, ← blockSucc_diagSignMat_one, ← blockSucc_diagSignMat_two, ← Matrix.blockSucc_mul]
  refine ⟨?_, ?_, ?_⟩
  · rw [← orderOf_injective (toMatHom5 f) (toMatHom5_injective f) (x * y), hxy,
      ← Matrix.blockSuccMonoidHom_apply,
      orderOf_injective (Matrix.blockSuccMonoidHom (ZMod p) 4) hb]
    exact orderOf_mMat hp hp5 hα
  · rw [← orderOf_injective (toMatHom5 f) (toMatHom5_injective f) (y * z), hyz,
      ← Matrix.blockSuccMonoidHom_apply,
      orderOf_injective (Matrix.blockSuccMonoidHom (ZMod p) 4) hb]
    exact orderOf_nzMat hp hα
  · rw [← orderOf_injective (toMatHom5 f) (toMatHom5_injective f) (x * z), hxz,
      ← Matrix.blockSuccMonoidHom_apply,
      orderOf_injective (Matrix.blockSuccMonoidHom (ZMod p) 4) hb]
    exact orderOf_diag12 hp

theorem false_of_h4Mats_bond (hp7 : 7 < p) [Module.Finite (ZMod p) U]
    {G : Subgroup (U ≃ₗ[ZMod p] U)} (hG : DMax p G 5) {α : ZMod p}
    (f : Module.Basis (Fin 5) (ZMod p) U) {a₁ : U ≃ₗ[ZMod p] U} (ha₁ : a₁ ∈ G)
    (ha₁m : LinearMap.toMatrix f f (a₁ : U →ₗ[ZMod p] U) =
      1 - Matrix.vecMulVec ![α - 2, 1, 1, 0, 0] ![-(1 / 2), (1 + α) / 2, 1 / 2, 0, 0])
    {w : U} {ψ : Module.Dual (ZMod p) U} (hψ : ψ w = 2) (hc : Module.reflection hψ ∈ G)
    (hne : Module.reflection hψ ≠ a₁) (hw0 : f.repr w 0 = 0) (hψ0 : ψ (f 0) = 0)
    (hw1 : f.repr w 1 = 0) (hψ1 : ψ (f 1) = 0) (h2 : 2 * (ψ (f 2) * f.repr w 2) = 1) :
    False := by
  have hp2 : p ≠ 2 := by omega
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  have hκρ : ∑ i : Fin 5, (![-(1 / 2), (1 + α) / 2, 1 / 2, 0, 0] : Fin 5 → ZMod p) i *
      (![α - 2, 1, 1, 0, 0] : Fin 5 → ZMod p) i = 2 := by
    rw [Fin.sum_univ_five]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp [h2ne]
    ring
  have h := etaOK_of_toMatrix hG (d := 5) (by norm_num) (by omega) hp2 f hc ha₁ hne hψ rfl
    ha₁m hκρ
  have hs : (∑ i : Fin 5, ψ (f i) * (![α - 2, 1, 1, 0, 0] : Fin 5 → ZMod p) i) = ψ (f 2) := by
    rw [Fin.sum_univ_five]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hψ0, hψ1]
    ring
  have ht : (∑ i : Fin 5, (![-(1 / 2), (1 + α) / 2, 1 / 2, 0, 0] : Fin 5 → ZMod p) i *
      f.repr w i) = f.repr w 2 / 2 := by
    rw [Fin.sum_univ_five]
    simp only [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val, hw0, hw1]
    ring
  rw [hs, ht] at h
  refine not_etaOK_five_of_mul_eq_quarter hp7 ?_ h
  have hw : ψ (f 2) * f.repr w 2 = 2⁻¹ := eq_inv_of_mul_eq_one_right h2
  rw [show f.repr w 2 / 2 = f.repr w 2 * 2⁻¹ by ring, ← mul_assoc, hw]
  rw [show (1 / 4 : ZMod p) = (4 : ZMod p)⁻¹ by rw [one_div],
    show (4 : ZMod p) = 2 * 2 by norm_num, mul_inv]

namespace PrimExtSetting

variable {G H : Subgroup (U ≃ₗ[ZMod p] U)}

theorem exists_isCentralizingSplit_of_h4Mats (hp5 : p ≠ 5) [Module.Finite (ZMod p) U] {d : ℕ}
    (S : PrimExtSetting G H d) (hneg : TFNegOrGen p (Module.finrank (ZMod p) U - 1))
    (hH5 : TFH4Model5 p) {α : ZMod p} (hα : α ^ 2 = α + 1)
    {f : Module.Basis (Fin 5) (ZMod p) U} (hfH : H = basisClosure f (h4Mats α))
    {h₁ : U ≃ₗ[ZMod p] U} (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0) :
    ∃ B, IsCentralizingSplit p G H B h₁ := by
  have hp2 : p ≠ 2 := by have := seven_lt_of_sq_eq_add_one hp5 hα; omega
  have hfr5 : Module.finrank (ZMod p) U = 5 := by
    rw [Module.finrank_eq_card_basis f]; simp
  have hzdet : IsUnit (diagSignMat (0 : Fin 5) * diagSignMat (1 : Fin 5) *
      diagSignMat (2 : Fin 5) : Matrix (Fin 5) (Fin 5) (ZMod p)).det := by
    rw [Matrix.det_mul, Matrix.det_mul]
    exact IsUnit.mul (IsUnit.mul (isUnit_diagSignMat_det_five 0) (isUnit_diagSignMat_det_five 1))
      (isUnit_diagSignMat_det_five 2)
  obtain ⟨z, hz⟩ := exists_toMatrix_eq_of_isUnit_det f hzdet
  obtain ⟨τ, hτ⟩ := exists_toMatrix_eq_of_isUnit_det f
    (isUnit_diagSignMat_det_five (3 : Fin 5))
  obtain ⟨hfr, hdim5, hirr5⟩ := hH5 U f α hp2 hp5 hα h₁ z τ hh₁ hz hτ
  have hfrH : PrimFrameData p H h₁ z τ := by rw [hfH]; exact hfr
  obtain ⟨b, hpair⟩ := exists_pair hp2 S hneg hfrH
  refine ⟨_, exists_isCentralizingSplit hp2 S hpair ?_ ?_⟩
  · rw [hfH, hfr5]; exact hdim5
  · rw [hfH]; exact hirr5

private theorem h4BlockMat_eq_one_sub_vecMulVec (hp2 : p ≠ 2) {α : ZMod p}
    (hα : α ^ 2 = α + 1) :
    h4BlockMat α = 1 - Matrix.vecMulVec ![0, 2 - α, -1, 1]
      ![0, 1 / 2, -1 / 2, (1 + α) / 2] := by
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [h4BlockMat]
  all_goals field_simp [h2ne]
  all_goals (try ring_nf)
  all_goals (try simp only [hα])
  all_goals (try ring)

private theorem isRefl_diagSignMat5 (hp2 : p ≠ 2) (f : Module.Basis (Fin 5) (ZMod p) U)
    {h : U ≃ₗ[ZMod p] U} {i : Fin 5}
    (hh : LinearMap.toMatrix f f (h : U →ₗ[ZMod p] U) = diagSignMat i) : IsRefl p h := by
  have hbs : diagSignMat i = (1 : Matrix (Fin 5) (Fin 5) (ZMod p)) -
      Matrix.vecMulVec (Pi.single i (1 : ZMod p)) (Pi.single i (2 : ZMod p)) :=
    diagSignMat_eq_one_sub_vecMulVec i
  have hsum : (∑ k : Fin 5, (Pi.single i (2 : ZMod p)) k * (Pi.single i (1 : ZMod p)) k) =
        (2 : ZMod p) := by
    fin_cases i <;> simp [Fin.sum_univ_five, Pi.single_eq_same, Pi.single_eq_of_ne]
  exact isRefl_of_toMatrix hp2 f (by rw [hh]; exact hbs) hsum

private theorem isRefl_h4BlockMat (hp2 : p ≠ 2) {α : ZMod p} (hα : α ^ 2 = α + 1)
    (f : Module.Basis (Fin 5) (ZMod p) U) {a : U ≃ₗ[ZMod p] U}
    (ha : LinearMap.toMatrix f f (a : U →ₗ[ZMod p] U) = Matrix.blockSucc (h4BlockMat α)) :
    IsRefl p a := by
  have hbs : Matrix.blockSucc (h4BlockMat α) =
      1 - Matrix.vecMulVec (Fin.snoc (![0, 2 - α, -1, 1] : Fin 4 → ZMod p) 0)
        (Fin.snoc (![0, 1 / 2, -1 / 2, (1 + α) / 2] : Fin 4 → ZMod p) 0) := by
    rw [h4BlockMat_eq_one_sub_vecMulVec hp2 hα, Matrix.blockSucc_one_sub_vecMulVec]
  have hsum : ∑ i : Fin 5, (Fin.snoc (![0, 1 / 2, -1 / 2, (1 + α) / 2] :
        Fin 4 → ZMod p) 0 : Fin 5 → ZMod p) i *
      (Fin.snoc (![0, 2 - α, -1, 1] : Fin 4 → ZMod p) 0 : Fin 5 → ZMod p) i = 2 := by
    have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
    rw [Fin.sum_univ_five]
    simp [Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.cons_val]
    field_simp [h2]
    ring
  exact isRefl_of_toMatrix hp2 f (by rw [ha, hbs]) hsum

private theorem toMatrix_injective {f : Module.Basis (Fin 5) (ZMod p) U}
    {g h : U ≃ₗ[ZMod p] U}
    (hgh : LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) =
      LinearMap.toMatrix f f (h : U →ₗ[ZMod p] U)) : g = h := by
  apply LinearEquiv.toLinearMap_injective
  apply (LinearMap.toMatrixAlgEquiv f).injective
  exact hgh

private theorem row_zero_diagSignMat {i : Fin 5} (hi : i ≠ 0) :
    ∀ j, (diagSignMat i : Matrix (Fin 5) (Fin 5) (ZMod p)) 0 j =
      (1 : Matrix (Fin 5) (Fin 5) (ZMod p)) 0 j := by
  intro j
  simp only [diagSignMat, Matrix.diagonal_apply, Matrix.one_apply]
  by_cases hj : (0 : Fin 5) = j
  · subst hj
    simp [show (0 : Fin 5) ≠ i from fun h => hi h.symm]
  · simp [hj]

private theorem row_zero_blockSucc_h4BlockMat (hp2 : p ≠ 2) {α : ZMod p} :
    ∀ j, (Matrix.blockSucc (h4BlockMat α) : Matrix (Fin 5) (Fin 5) (ZMod p)) 0 j =
      (1 : Matrix (Fin 5) (Fin 5) (ZMod p)) 0 j := by
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
  intro j
  fin_cases j
  · show (Matrix.blockSucc (h4BlockMat α)) (Fin.castSucc (0 : Fin 4)) (Fin.castSucc (0 : Fin 4)) =
      (1 : Matrix (Fin 5) (Fin 5) (ZMod p)) (0 : Fin 5) (0 : Fin 5)
    rw [Matrix.blockSucc_castSucc_castSucc]
    simp [h4BlockMat]
    field_simp [h2ne]
  · show (Matrix.blockSucc (h4BlockMat α)) (Fin.castSucc (0 : Fin 4)) (Fin.castSucc (1 : Fin 4)) =
      (1 : Matrix (Fin 5) (Fin 5) (ZMod p)) (0 : Fin 5) (1 : Fin 5)
    rw [Matrix.blockSucc_castSucc_castSucc]
    simp [h4BlockMat]
  · show (Matrix.blockSucc (h4BlockMat α)) (Fin.castSucc (0 : Fin 4)) (Fin.castSucc (2 : Fin 4)) =
      (1 : Matrix (Fin 5) (Fin 5) (ZMod p)) (0 : Fin 5) (2 : Fin 5)
    rw [Matrix.blockSucc_castSucc_castSucc]
    simp [h4BlockMat]
  · show (Matrix.blockSucc (h4BlockMat α)) (Fin.castSucc (0 : Fin 4)) (Fin.castSucc (3 : Fin 4)) =
      (1 : Matrix (Fin 5) (Fin 5) (ZMod p)) (0 : Fin 5) (3 : Fin 5)
    rw [Matrix.blockSucc_castSucc_castSucc]
    simp [h4BlockMat]
  · show (Matrix.blockSucc (h4BlockMat α)) (Fin.castSucc (0 : Fin 4)) (Fin.last 4) =
      (1 : Matrix (Fin 5) (Fin 5) (ZMod p)) (0 : Fin 5) (Fin.last 4)
    rw [Matrix.blockSucc_castSucc_last]
    simp

private theorem zs3g_sub_mem_ker {f : Module.Basis (Fin 5) (ZMod p) U} {h₁ g : U ≃ₗ[ZMod p] U}
    (_hp2 : p ≠ 2) (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0)
    (hrow : ∀ j, LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) 0 j =
      (1 : Matrix (Fin 5) (Fin 5) (ZMod p)) 0 j) (v : U) :
    g v - v ∈ LinearMap.ker ((h₁ : U →ₗ[ZMod p] U) - 1) := by
  rw [LinearMap.mem_ker, LinearMap.sub_apply, sub_eq_zero]
  change h₁ (g v - v) = g v - v
  apply f.repr.injective
  ext j
  change f.repr ((h₁ : U →ₗ[ZMod p] U) (g v - v)) j =
    f.repr ((g : U →ₗ[ZMod p] U) v - v) j
  have hx0 : (LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) *ᵥ f.repr v) 0 - (f.repr v) 0 = 0 := by
    have h0 : (LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) *ᵥ f.repr v) 0 = (f.repr v) 0 := by
      rw [Matrix.mulVec_apply]
      change (∑ x : Fin 5, (LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U)) 0 x * (f.repr v) x) =
        (f.repr v) 0
      simp only [hrow, Matrix.one_apply]
      rw [Finset.sum_eq_single 0]
      · simp
      · intro b _ hb
        have h0b : (0 : Fin 5) ≠ b := fun h => hb h.symm
        simp [h0b]
      · intro h; exact absurd (Finset.mem_univ 0) h
    rw [h0, sub_self]
  have h1j : f.repr ((h₁ : U →ₗ[ZMod p] U) (g v - v)) j =
      (LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) *ᵥ f.repr (g v - v)) j :=
    congrFun (LinearMap.toMatrix_mulVec_repr f f (h₁ : U →ₗ[ZMod p] U) (g v - v)).symm j
  have hsub : f.repr ((g : U →ₗ[ZMod p] U) v - v) =
      LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) *ᵥ f.repr v - f.repr v := by
    rw [map_sub, Finsupp.coe_sub]
    rw [← LinearMap.toMatrix_mulVec_repr f f (g : U →ₗ[ZMod p] U) v]
  rw [h1j, hh₁]
  change (diagSignMat 0 *ᵥ f.repr ((g : U →ₗ[ZMod p] U) v - v)) j =
    f.repr ((g : U →ₗ[ZMod p] U) v - v) j
  rw [hsub]
  rw [show (diagSignMat (0 : Fin 5) : Matrix (Fin 5) (Fin 5) (ZMod p)) =
    Matrix.diagonal (fun j => if j = 0 then -1 else 1) from rfl]
  simp only [Matrix.mulVec_diagonal, Pi.sub_apply]
  by_cases hj : j = 0
  · subst hj
    have hAB : (LinearMap.toMatrix f f (g : U →ₗ[ZMod p] U) *ᵥ f.repr v) 0 = (f.repr v) 0 :=
      sub_eq_zero.mp hx0
    simp [hAB]
  · simp [hj]

theorem exists_refl_of_h4Mats (hp5 : p ≠ 5) [Module.Finite (ZMod p) U]
    (S : PrimExtSetting G H 5) (hneg : TFNegOrGen p (Module.finrank (ZMod p) U - 1))
    (h19 : LemmaOneNineInput) (hext : TFH4Extend p) (hH5 : TFH4Model5 p) {α : ZMod p}
    (hα : α ^ 2 = α + 1) {f : Module.Basis (Fin 5) (ZMod p) U}
    (hfH : H = basisClosure f (h4Mats α)) {h₁ x z : U ≃ₗ[ZMod p] U}
    (hh₁ : LinearMap.toMatrix f f (h₁ : U →ₗ[ZMod p] U) = diagSignMat 0)
    (hx : LinearMap.toMatrix f f (x : U →ₗ[ZMod p] U) = diagSignMat 1)
    (hz : LinearMap.toMatrix f f (z : U →ₗ[ZMod p] U) = diagSignMat 2) :
    ∃ b ∈ G, IsRefl p b ∧ b * h₁ = h₁ * b ∧ orderOf (b * x) = 2 ∧ orderOf (b * z) = 3 := by
  have hp2 : p ≠ 2 := by have := seven_lt_of_sq_eq_add_one hp5 hα; omega
  have hp7 : 7 < p := seven_lt_of_sq_eq_add_one hp5 hα
  have h5p : 5 < p := by omega
  have hfr5 : Module.finrank (ZMod p) U = 5 := by
    rw [Module.finrank_eq_card_basis f]; simp
  obtain ⟨B, hB⟩ := exists_isCentralizingSplit_of_h4Mats hp5 S hneg hH5 hα hfH hh₁
  obtain ⟨hdiag, ha2, _⟩ := exists_mem_h4Mats hp2 hα f
  obtain ⟨g0, hg0, hg0m⟩ := hdiag 0 (by decide)
  obtain ⟨g1, hg1, hg1m⟩ := hdiag 1 (by decide)
  obtain ⟨g2, hg2, hg2m⟩ := hdiag 2 (by decide)
  obtain ⟨ga, hga, hgam⟩ := ha2
  have hg0e : g0 = h₁ := toMatrix_injective (hg0m.trans hh₁.symm)
  have hg1e : g1 = x := toMatrix_injective (hg1m.trans hx.symm)
  have hg2e : g2 = z := toMatrix_injective (hg2m.trans hz.symm)
  have hxH : x ∈ H := by rw [hfH, ← hg1e]; exact hg1
  have hzH : z ∈ H := by rw [hfH, ← hg2e]; exact hg2
  have haH : ga ∈ H := by rw [hfH]; exact hga
  have hxr : IsRefl p x := isRefl_diagSignMat5 hp2 f hx
  have hzr : IsRefl p z := isRefl_diagSignMat5 hp2 f hz
  have har : IsRefl p ga := isRefl_h4BlockMat hp2 hα f hgam
  have hxrefl : x ∈ reflSubgroupIn p H (LinearMap.ker ((h₁ : U →ₗ[ZMod p] U) - 1)) := by
    refine Subgroup.subset_closure ⟨hxH, hxr, ?_⟩
    intro v
    exact zs3g_sub_mem_ker hp2 hh₁ (by intro j; rw [hx]; exact row_zero_diagSignMat (by decide) j) v
  have harefl : ga ∈ reflSubgroupIn p H (LinearMap.ker ((h₁ : U →ₗ[ZMod p] U) - 1)) := by
    refine Subgroup.subset_closure ⟨haH, har, ?_⟩
    intro v
    exact zs3g_sub_mem_ker hp2 hh₁
      (by intro j; rw [hgam]; exact row_zero_blockSucc_h4BlockMat hp2 j) v
  have hzrefl : z ∈ reflSubgroupIn p H (LinearMap.ker ((h₁ : U →ₗ[ZMod p] U) - 1)) := by
    refine Subgroup.subset_closure ⟨hzH, hzr, ?_⟩
    intro v
    exact zs3g_sub_mem_ker hp2 hh₁ (by intro j; rw [hz]; exact row_zero_diagSignMat (by decide) j) v
  have hxB : x ∈ B := hB.2.2.2.2 hxrefl
  have haB : ga ∈ B := hB.2.2.2.2 harefl
  have hzB : z ∈ B := hB.2.2.2.2 hzrefl
  have htriple := orderOf_mul_h4Triple hp2 hp5 hα f hx hgam hz
  have hBtf : QTwoLin.TransvectionFree B := fun g hg => S.transvectionFree g (hB.1 hg)
  have hBsplit : SplitSupport B 4 := by
    rw [show (4 : ℕ) = Module.finrank (ZMod p) U - 1 by omega]; exact hB.2.2.1
  have hBcent := (centreOrderBound hp2 S h19) B hB.1 hB.2.1 hB.2.2.1
  have hBdmax : DMax p B 5 :=
    ⟨fun a ha b hb har hbr => S.dmax.1 a (hB.1 ha) b (hB.1 hb) har hbr,
      x, hxB, ga, haB, hxr, har, htriple.1⟩
  obtain ⟨b, hbB, hbr, hbx, hbz⟩ := hext U B h5p hB.2.1 hBtf hBsplit hBdmax hBcent
    x hxB ga haB z hzB hxr har hzr htriple.1 htriple.2.1 htriple.2.2
  refine ⟨b, hB.1 hbB, hbr, ?_, hbx, hbz⟩
  exact (Subgroup.mem_centralizer_iff.mp (hB.2.2.2.1 hbB) h₁ (by simp)).symm

theorem lemmaThreeFour (hp5 : p ≠ 5) [Module.Finite (ZMod p) U] (S : PrimExtSetting G H 5)
    (hneg : TFNegOrGen p (Module.finrank (ZMod p) U - 1)) (h19 : LemmaOneNineInput)
    (hext : TFH4Extend p) (hH5 : TFH4Model5 p) {α : ZMod p} (hα : α ^ 2 = α + 1)
    {f : Module.Basis (Fin 5) (ZMod p) U} (hfH : H = basisClosure f (h4Mats α)) : False := by
  have hp2 : p ≠ 2 := by have := seven_lt_of_sq_eq_add_one hp5 hα; omega
  have hp7 : 7 < p := seven_lt_of_sq_eq_add_one hp5 hα
  obtain ⟨hdiag, _ha2, ha1⟩ := exists_mem_h4Mats hp2 hα f
  obtain ⟨g0, hg0, hm0⟩ := hdiag 0 (by decide)
  obtain ⟨g1, hg1, hm1⟩ := hdiag 1 (by decide)
  obtain ⟨g2, hg2, hm2⟩ := hdiag 2 (by decide)
  obtain ⟨ga1, hga1, hma1⟩ := ha1
  obtain ⟨b, hbG, hbr, hbcomm0, hbx2, hbz3⟩ :=
    exists_refl_of_h4Mats hp5 S hneg h19 hext hH5 hα hfH hm0 hm1 hm2
  obtain ⟨w, ψ, hψw, hbrefl⟩ := (isRefl_iff hp2 b).mp hbr
  rw [hbrefl] at hbG hbcomm0 hbx2 hbz3
  have hb2 : Module.reflection hψw * Module.reflection hψw = 1 := by
    rw [← Module.reflection_inv]; exact mul_inv_cancel _
  have hg0_2 : g0 * g0 = 1 := by
    apply toMatHom5_injective f
    simp only [toMatHom5, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_one]
    rw [hm0]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagSignMat, Matrix.mul_apply, Fin.sum_univ_five]
  have hg1_2 : g1 * g1 = 1 := by
    apply toMatHom5_injective f
    simp only [toMatHom5, MonoidHom.coe_mk, OneHom.coe_mk, map_mul, map_one]
    rw [hm1]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [diagSignMat, Matrix.mul_apply, Fin.sum_univ_five]
  have hcomm1 : Module.reflection hψw * g1 = g1 * Module.reflection hψw := by
    have h := pow_orderOf_eq_one (Module.reflection hψw * g1)
    rw [hbx2, pow_two] at h
    have h1 := eq_inv_of_mul_eq_one_left h
    rw [mul_inv_rev, inv_eq_of_mul_eq_one_left hb2, inv_eq_of_mul_eq_one_left hg1_2] at h1
    exact h1
  have hg0g2 : orderOf (g0 * g2) = 2 := by
    rw [← orderOf_injective (toMatHom5 f) (toMatHom5_injective f) (g0 * g2)]
    simp only [toMatHom5, MonoidHom.coe_mk, OneHom.coe_mk, map_mul]
    rw [hm0, hm2]
    apply orderOf_eq_prime
    · rw [pow_two]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [diagSignMat, Matrix.mul_apply, Fin.sum_univ_five]
    · intro h
      have h00 : ((diagSignMat (0 : Fin 5) : Matrix (Fin 5) (Fin 5) (ZMod p)) *
          (diagSignMat (2 : Fin 5) : Matrix (Fin 5) (Fin 5) (ZMod p))) 0 0 = -1 := by
        simp [diagSignMat, Matrix.mul_apply, Fin.sum_univ_five]
      rw [h] at h00
      simp at h00
      have h2z : (2 : ZMod p) = 0 := by linear_combination h00
      exact (ZMod.prime_ne_zero p 2 hp2) h2z
  have hg1g2 : orderOf (g1 * g2) = 2 := by
    rw [← orderOf_injective (toMatHom5 f) (toMatHom5_injective f) (g1 * g2)]
    simp only [toMatHom5, MonoidHom.coe_mk, OneHom.coe_mk, map_mul]
    rw [hm1, hm2]
    apply orderOf_eq_prime
    · rw [pow_two]
      ext i j
      fin_cases i <;> fin_cases j <;>
        simp [diagSignMat, Matrix.mul_apply, Fin.sum_univ_five]
    · intro h
      have h11 : ((diagSignMat (1 : Fin 5) : Matrix (Fin 5) (Fin 5) (ZMod p)) *
          (diagSignMat (2 : Fin 5) : Matrix (Fin 5) (Fin 5) (ZMod p))) 1 1 = -1 := by
        simp [diagSignMat, Matrix.mul_apply, Fin.sum_univ_five]
      rw [h] at h11
      simp at h11
      have h2z : (2 : ZMod p) = 0 := by linear_combination h11
      exact (ZMod.prime_ne_zero p 2 hp2) h2z
  have hne0 : Module.reflection hψw ≠ g0 := by
    intro heq
    have h3 := hbz3
    rw [heq] at h3
    rw [hg0g2] at h3
    omega
  have hne1 : Module.reflection hψw ≠ g1 := by
    intro heq
    have h3 := hbz3
    rw [heq] at h3
    rw [hg1g2] at h3
    omega
  have hne_a1 : Module.reflection hψw ≠ ga1 := by
    intro heq
    have hc : ga1 * g0 = g0 * ga1 := by rw [← heq]; exact hbcomm0
    have h01 := congrArg (fun t : U ≃ₗ[ZMod p] U =>
      (LinearMap.toMatrix f f (t : U →ₗ[ZMod p] U)) 0 1) hc
    rw [LinearEquiv.coe_toLinearMap_mul, LinearEquiv.coe_toLinearMap_mul,
      LinearMap.toMatrix_mul, LinearMap.toMatrix_mul, hma1, hm0] at h01
    have e1 : (((1 : Matrix (Fin 5) (Fin 5) (ZMod p)) -
        Matrix.vecMulVec ![α - 2, 1, 1, 0, 0] ![-(1 / 2), (1 + α) / 2, 1 / 2, 0, 0]) *
        (diagSignMat (0 : Fin 5) : Matrix (Fin 5) (Fin 5) (ZMod p))) 0 1 =
        -((α - 2) * ((1 + α) / 2)) := by
      simp [Matrix.mul_apply, Fin.sum_univ_five, diagSignMat, Matrix.one_apply]
    have e2 : ((diagSignMat (0 : Fin 5) : Matrix (Fin 5) (Fin 5) (ZMod p)) *
        ((1 : Matrix (Fin 5) (Fin 5) (ZMod p)) -
        Matrix.vecMulVec ![α - 2, 1, 1, 0, 0] ![-(1 / 2), (1 + α) / 2, 1 / 2, 0, 0])) 0 1 =
        (α - 2) * ((1 + α) / 2) := by
      simp [Matrix.mul_apply, Fin.sum_univ_five, diagSignMat, Matrix.one_apply]
    rw [e1, e2] at h01
    have h2 : (α - 2) * (1 + α) = 0 := by
      have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp2
      have h2X : (2 : ZMod p) * ((α - 2) * ((1 + α) / 2)) = 0 := by
        linear_combination (norm := ring_nf) -h01
      have hX : (α - 2) * ((1 + α) / 2) = 0 := (mul_eq_zero.mp h2X).resolve_left h2ne
      have h2eq : (α - 2) * (1 + α) = 2 * ((α - 2) * ((1 + α) / 2)) := by
        field_simp [h2ne]
      rw [h2eq, hX, mul_zero]
    rcases mul_eq_zero.mp h2 with h | h
    · have hα2 : α = 2 := sub_eq_zero.mp h
      have h4 : (4 : ZMod p) = 3 := by
        have hα' := hα
        rw [hα2] at hα'
        norm_num at hα'
        exact hα'
      exact one_ne_zero (by linear_combination h4)
    · have hα2 : α = -1 := by linear_combination h
      have h4 : (1 : ZMod p) = 0 := by
        have hα' := hα
        rw [hα2] at hα'
        norm_num at hα'
      exact one_ne_zero h4
  have hw0 := apply_eq_zero_of_commute_diagSignMat hp2 f hm0 hψw hbcomm0 hne0
  have hw1 := apply_eq_zero_of_commute_diagSignMat hp2 f hm1 hψw hcomm1 hne1
  have h2 := two_mul_apply_mul_eq_one_of_diagSignMat hp2 f hm2 hψw hbz3
  have hga1H : ga1 ∈ H := hfH.symm ▸ hga1
  exact false_of_h4Mats_bond hp7 S.dmax f (S.H_le hga1H) hma1 hψw hbG hne_a1
    hw0.2 hw0.1 hw1.2 hw1.1 h2


end PrimExtSetting

end CFSG.StandardType.ZS

end
