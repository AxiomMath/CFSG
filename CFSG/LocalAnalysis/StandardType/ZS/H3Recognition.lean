module

public import CFSG.LocalAnalysis.StandardType.ZS.ReflFrame
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtMatrices
import CFSG.LocalAnalysis.StandardType.ZS.CommutingRefl
import CFSG.LocalAnalysis.StandardType.ZS.ExcMatricesRefl
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtBond
import CFSG.LocalAnalysis.StandardType.ZS.RootMatrix
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelH3

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W] [Module (ZMod p) W]
  [Module.Finite (ZMod p) W]

private theorem rh3_one_sub_vecMulVec_single {K : Type} [Field K] {n : ℕ} (i : Fin n) {c d : K}
    (hcd : c * d = 2) :
    1 - Matrix.vecMulVec (Pi.single i c) (Pi.single i d) = diagSignMat i := by
  have h1 : Matrix.vecMulVec (Pi.single i c) (Pi.single i d) =
      (c * d) • Matrix.vecMulVec (Pi.single i (1 : K)) (Pi.single i 1) := by
    ext r s
    simp only [Matrix.vecMulVec_apply, Pi.single_apply, Matrix.smul_apply, smul_eq_mul]
    by_cases hr : r = i <;> by_cases hs : s = i <;> simp [hr, hs]
  rw [h1, hcd]
  ext r s
  simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.smul_apply, Matrix.vecMulVec_apply,
    Pi.single_apply, diagSignMat, Matrix.diagonal_apply, smul_eq_mul]
  by_cases hrs : r = s
  · subst hrs
    by_cases hri : r = i
    · subst hri; norm_num
    · simp [hri]
  · by_cases hri : r = i <;> by_cases hsi : s = i <;> simp_all

private theorem rh3_one_sub_vecMulVec_h3BlockMat {K : Type} [Field K] {α : K}
    (hα : α ^ 2 = α + 1) (h2 : (2 : K) ≠ 0) :
    1 - Matrix.vecMulVec (fun i : Fin 4 => ![α - 2, 1, 1, 0] i)
        (fun i : Fin 4 => ![-(2 : K)⁻¹, (1 + α) * (2 : K)⁻¹, (2 : K)⁻¹, 0] i) =
      Matrix.blockSucc (h3BlockMat α) := by
  ext r s
  induction r using Fin.lastCases with
  | last =>
      induction s using Fin.lastCases with
      | last => rw [Matrix.blockSucc_last_last]; simp
      | cast s =>
          rw [Matrix.blockSucc_last_castSucc]
          simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply]
          rw [if_neg (fun h => Fin.castSucc_ne_last s h.symm)]
          simp
  | cast r =>
      induction s using Fin.lastCases with
      | last =>
          rw [Matrix.blockSucc_castSucc_last]
          simp only [Matrix.sub_apply, Matrix.one_apply, Matrix.vecMulVec_apply]
          rw [if_neg (Fin.castSucc_ne_last r)]
          simp
      | cast s =>
          rw [Matrix.blockSucc_castSucc_castSucc]
          fin_cases r <;> (fin_cases s <;>
            simp [Matrix.sub_apply, h3BlockMat] <;>
            field_simp [h2] <;>
            (try ring) <;> (try linear_combination -hα))

omit [Module.Finite (ZMod p) W] in
private theorem rh3_toMatrix_reflection_h3BlockMat {f : Module.Basis (Fin 4) (ZMod p) W}
    {r : W} {ψ : Module.Dual (ZMod p) W} (hψ : ψ r = 2) {α : ZMod p} (hα : α ^ 2 = α + 1)
    (h2 : (2 : ZMod p) ≠ 0)
    (hr : ∀ i, f.repr r i = ![α - 2, 1, 1, 0] i)
    (hψf : ∀ i, ψ (f i) = ![-(2 : ZMod p)⁻¹, (1 + α) * (2 : ZMod p)⁻¹, (2 : ZMod p)⁻¹, 0] i) :
    LinearMap.toMatrix f f (Module.reflection hψ : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (h3BlockMat α) := by
  rw [toMatrix_reflection f hψ, funext hr, funext hψf]
  exact rh3_one_sub_vecMulVec_h3BlockMat hα h2

omit [Module.Finite (ZMod p) W] in
private theorem rh3_toMatrix_reflection_diagSignMat {f : Module.Basis (Fin 4) (ZMod p) W}
    {r : W} {φ : Module.Dual (ZMod p) W} (hφ : φ r = 2) {i : Fin 3} {c d : ZMod p}
    (hcd : c * d = 2) (hr : ∀ j, f.repr r j = (Pi.single (Fin.castSucc i) c : Fin 4 → ZMod p) j)
    (hφf : ∀ j, φ (f j) = (Pi.single (Fin.castSucc i) d : Fin 4 → ZMod p) j) :
    LinearMap.toMatrix f f (Module.reflection hφ : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (diagSignMat i) := by
  rw [toMatrix_reflection f hφ, funext hr, funext hφf, rh3_one_sub_vecMulVec_single _ hcd]
  exact (blockSucc_diagSignMat i).symm

section Rh3Aux

omit [Module.Finite (ZMod p) W] in
private theorem rh3_linearIndependent_of_det {n : ℕ} {u : Fin n → W}
    {φ : Fin n → Module.Dual (ZMod p) W}
    (hdet : (Matrix.of fun i j => φ i (u j)).det ≠ 0) : LinearIndependent (ZMod p) u := by
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have hrow : ∀ i, ∑ j, φ i (u j) * g j = 0 := by
    intro i
    have h := congrArg (φ i) hg
    simp only [map_sum, map_smul, smul_eq_mul, map_zero] at h
    rwa [Finset.sum_congr rfl fun j _ => mul_comm (g j) (φ i (u j))] at h
  have hM : Matrix.mulVec (Matrix.of fun i j => φ i (u j)) g = 0 := by
    ext i
    simpa [Matrix.mulVec, dotProduct] using hrow i
  intro i
  simpa using congrFun (Matrix.eq_zero_of_mulVec_eq_zero hdet hM) i

omit [Module.Finite (ZMod p) W] in
private theorem rh3_repr_smul_self {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) W) (i : Fin n)
    (c : ZMod p) : (fun k => f.repr (c • f i) k) = Pi.single i c := by
  funext k
  rw [map_smul, Finsupp.smul_apply, Module.Basis.repr_self]
  simp [Pi.single_apply, Finsupp.single_apply, smul_eq_mul, eq_comm]

omit [Module.Finite (ZMod p) W] in
private theorem rh3_repr_sum_single {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) W)
    (ρ : Fin n → ZMod p) (i : Fin n) : f.repr (∑ j, ρ j • f j) i = ρ i := by
  have h1 : f.repr (∑ j, ρ j • f j) = ∑ j, Finsupp.single j (ρ j) := by
    simp [map_sum, map_smul, Module.Basis.repr_self, Finsupp.smul_single]
  rw [h1, Finsupp.finsetSum_apply]
  simp only [Finsupp.single_apply]
  rw [Finset.sum_eq_single i]
  · simp
  · intro j _ hij; rw [if_neg hij]
  · intro hi; simp at hi

omit [Module.Finite (ZMod p) W] in
private theorem rh3_repr_eq_of_sum {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) W) {r : W}
    {ρ : Fin n → ZMod p} (hr : r = ∑ i, ρ i • f i) :
    (fun k => f.repr r k) = ρ := by
  subst hr
  funext k
  exact rh3_repr_sum_single f ρ k

omit [Module.Finite (ZMod p) W] in
private theorem rh3_dual_sum {m : ℕ} (φ : Module.Dual (ZMod p) W) (c : Fin m → ZMod p)
    (v : Fin m → W) : φ (∑ i, c i • v i) = ∑ i, c i * φ (v i) := by
  simp [map_sum, map_smul, smul_eq_mul]

omit [Module.Finite (ZMod p) W] in
private theorem rh3_phi_r {m : ℕ} {φ : Module.Dual (ZMod p) W} {v : Fin m → W}
    {y : Fin m → ZMod p} {r : W} (hy : (∑ i, y i • v i) = r) (i : Fin m) {c : ZMod p}
    (hvi : φ (v i) = c) (hzero : ∀ j, j ≠ i → φ (v j) = 0) : φ r = c * y i := by
  rw [← hy, rh3_dual_sum, Finset.sum_eq_single i]
  · rw [hvi]; ring
  · intro j _ hji; rw [hzero j hji, mul_zero]
  · intro hi; exact absurd (Finset.mem_univ i) hi

omit [Module.Finite (ZMod p) W] in
private theorem rh3_linearIndependent_smul {m : ℕ} {v : Fin m → W}
    (hv : LinearIndependent (ZMod p) v) {s : Fin m → ZMod p} (hs : ∀ i, s i ≠ 0) :
    LinearIndependent (ZMod p) (fun i => s i • v i) := by
  rw [Fintype.linearIndependent_iff] at hv ⊢
  intro g hg
  have hg' : (∑ i, (g i * s i) • v i) = 0 := by simpa only [smul_smul] using hg
  have h := hv (fun i => g i * s i) hg'
  intro i
  exact (mul_eq_zero.mp (h i)).resolve_right (hs i)

omit [Module.Finite (ZMod p) W] in
private theorem rh3_coroot_single {φ : Module.Dual (ZMod p) W}
    (f : Module.Basis (Fin 4) (ZMod p) W) (i : Fin 3) {d : ZMod p}
    (hi : φ (f (Fin.castSucc i)) = d)
    (hzero : ∀ j : Fin 4, j ≠ Fin.castSucc i → φ (f j) = 0) :
    (fun k => φ (f k)) = (Pi.single (Fin.castSucc i) d : Fin 4 → ZMod p) := by
  funext k
  by_cases hk : k = Fin.castSucc i
  · rw [hk]; simpa [Pi.single_apply] using hi
  · rw [hzero k hk]; simp [hk]

@[instance_reducible]
private noncomputable def rh3_fintype_X (f : Module.Basis (Fin 4) (ZMod p) W)
    (X : Subgroup (W ≃ₗ[ZMod p] W)) : Fintype X := by
  haveI : Finite W := Finite.of_injective (fun x : W => f.repr x)
    (fun x y h => by
      calc x = ∑ i, f.repr x i • f i := (f.sum_repr x).symm
        _ = ∑ i, f.repr y i • f i := congrArg (fun g => ∑ i, g i • f i) h
        _ = y := f.sum_repr y)
  haveI : Finite (W ≃ₗ[ZMod p] W) :=
    Finite.of_injective (fun e : W ≃ₗ[ZMod p] W => (e : W → W))
      (fun e1 e2 h => LinearEquiv.ext (congrFun h))
  haveI : Finite X := Subtype.finite
  exact Fintype.ofFinite X

end Rh3Aux

section Rh3Field

variable {K : Type} [Field K]

private theorem rh3_mul_ne_zero_of_eq_two {y x c : K}
    (h : c = 2 * y * x) (hc : c ≠ 0) : y ≠ 0 ∧ x ≠ 0 := by
  refine ⟨fun hy => hc ?_, fun hx => hc ?_⟩
  · simp [h, hy]
  · simp [h, hx]

private theorem rh3_yx_of_two_mul {y x c : K} (h2 : (2 : K) ≠ 0)
    (h : 2 * y * x = c) : y * x = c * (2 : K)⁻¹ := by
  have h2' : 2 * (y * x) = c := by linear_combination h
  rw [← h2', mul_comm (2 : K) (y * x), mul_assoc, mul_inv_cancel₀ h2, mul_one]

private theorem rh3_coroot_zero {α y x : K}
    (h2 : (2 : K) ≠ 0) (hα2 : α - 2 ≠ 0) (h : 2 * y * x = 2 - α) :
    (y * (α - 2)⁻¹) * x = -(2 : K)⁻¹ := by
  have hxy : y * x = (2 - α) * (2 : K)⁻¹ := rh3_yx_of_two_mul h2 h
  rw [show (y * (α - 2)⁻¹) * x = (α - 2)⁻¹ * (y * x) by ring, hxy,
    show (2 : K) - α = -(α - 2) by ring, neg_mul, mul_neg, ← mul_assoc,
    inv_mul_cancel₀ hα2, one_mul]

private theorem rh3_coroot_one {α y x : K} (h2 : (2 : K) ≠ 0)
    (h : 2 * y * x = 1 + α) : y * x = (1 + α) * (2 : K)⁻¹ :=
  rh3_yx_of_two_mul h2 h

private theorem rh3_coroot_two {y x : K} (h2 : (2 : K) ≠ 0)
    (h : 2 * y * x = 1) : y * x = (2 : K)⁻¹ := by
  simpa using rh3_yx_of_two_mul (c := 1) h2 h

private theorem rh3_alpha_of {c0 c1 c2 : K}
    (h0 : c0 ^ 2 - 3 * c0 + 1 = 0) (h1 : c1 ^ 2 - 3 * c1 + 1 = 0) (h2 : c2 = 1)
    (hsum : c0 + c1 + c2 = 4) :
    (2 - c0) ^ 2 = (2 - c0) + 1 ∧ c1 = 1 + (2 - c0) ∧ c0 ≠ 0 ∧ c1 ≠ 0 ∧ (2 - c0) ≠ 2 := by
  have hc0 : c0 ≠ 0 := by
    intro hc
    rw [hc] at h0
    simp at h0
  have hc1 : c1 ≠ 0 := by
    intro hc
    rw [hc] at h1
    simp at h1
  exact ⟨by linear_combination h0, by linear_combination hsum - h2, hc0, hc1,
    fun h => hc0 (by linear_combination -h)⟩

private theorem rh3_scale_comm (a b : K) (ha : a ≠ 0) : a * (b * a⁻¹) = b := by
  rw [← mul_assoc, mul_comm a b, mul_assoc, mul_inv_cancel₀ ha, mul_one]

end Rh3Field

omit [Module.Finite (ZMod p) W] in
private theorem rh3_final (hp : p ≠ 2) {X : Subgroup (W ≃ₗ[ZMod p] W)}
    (hcard : Nat.card X = 120) {f : Module.Basis (Fin 4) (ZMod p) W}
    {h0 h1 h2 a : W ≃ₗ[ZMod p] W} {α : ZMod p} (hα : α ^ 2 = α + 1)
    (hh0X : h0 ∈ X) (hh1X : h1 ∈ X) (hh2X : h2 ∈ X) (haX : a ∈ X)
    (hh0mat : LinearMap.toMatrix f f (h0 : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (diagSignMat (0 : Fin 3)))
    (hh1mat : LinearMap.toMatrix f f (h1 : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (diagSignMat (1 : Fin 3)))
    (hh2mat : LinearMap.toMatrix f f (h2 : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (diagSignMat (2 : Fin 3)))
    (hamat : LinearMap.toMatrix f f (a : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (h3BlockMat α)) :
    X = basisClosure f (h3Mats α) := by
  have hle : basisClosure f (h3Mats α) ≤ X := by
    rw [basisClosure, Subgroup.closure_le]
    rintro g hg
    simp only [Set.mem_setOf_eq] at hg
    rw [h3Mats, Set.mem_image] at hg
    obtain ⟨M, hM, hMto⟩ := hg
    rw [h3BlockMats] at hM
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hM
    rcases hM with rfl | rfl | rfl | rfl
    · exact (eq_of_toMatrix_eq f (by rw [← hMto, ← hh0mat]) : g = h0) ▸ hh0X
    · exact (eq_of_toMatrix_eq f (by rw [← hMto, ← hh1mat]) : g = h1) ▸ hh1X
    · exact (eq_of_toMatrix_eq f (by rw [← hMto, ← hh2mat]) : g = h2) ▸ hh2X
    · exact (eq_of_toMatrix_eq f (by rw [← hMto, ← hamat]) : g = a) ▸ haX
  have hcard' : Nat.card (basisClosure f (h3Mats α)) = 120 :=
    PrimModel.card_basisClosure_h3Mats hp f hα
  exact (@Subgroup.eq_of_le_of_card_ge (W ≃ₗ[ZMod p] W) _ (basisClosure f (h3Mats α)) X
    (rh3_fintype_X f X).finite hle (by rw [hcard', hcard])).symm

private theorem rh3_span_y {r0 r1 r2 : W} {X : Subgroup (W ≃ₗ[ZMod p] W)} {r : W}
    (hvli : LinearIndependent (ZMod p) (![r0, r1, r2] : Fin 3 → W))
    (hvV : ∀ i, (![r0, r1, r2] : Fin 3 → W) i ∈ HardMathSupport.Kantor79.commutatorSpace X)
    (hrV : r ∈ HardMathSupport.Kantor79.commutatorSpace X)
    (hXdim : Module.finrank (ZMod p) (HardMathSupport.Kantor79.commutatorSpace X) = 3) :
    ∃ y : Fin 3 → ZMod p, (∑ i, y i • (![r0, r1, r2] : Fin 3 → W) i) = r := by
  let v : Fin 3 → W := ![r0, r1, r2]
  have hvli' : LinearIndependent (ZMod p) v := by simpa [v] using hvli
  have hspan : Submodule.span (ZMod p) (Set.range v) =
      HardMathSupport.Kantor79.commutatorSpace X := by
    refine Submodule.eq_of_le_of_finrank_le ?_ ?_
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      simpa [v] using hvV i
    · rw [finrank_span_eq_card hvli', hXdim]
      simp
  have hrspan : r ∈ Submodule.span (ZMod p) (Set.range v) := by rw [hspan]; exact hrV
  obtain ⟨y, hy⟩ := (Submodule.mem_span_range_iff_exists_fun (ZMod p)).mp hrspan
  exact ⟨y, by simpa [v] using hy⟩

omit [Module.Finite (ZMod p) W] in
private theorem rh3_frame_zeros (hp : p ≠ 2) {X : Subgroup (W ≃ₗ[ZMod p] W)}
    {r0 r1 r2 r : W} {φ0 φ1 φ2 ψ : Module.Dual (ZMod p) W}
    (hφ0 : φ0 r0 = 2) (hφ1 : φ1 r1 = 2) (hφ2 : φ2 r2 = 2) (hψ : ψ r = 2)
    (h0X : Module.reflection hφ0 ∈ X) (h1X : Module.reflection hφ1 ∈ X)
    (h2X : Module.reflection hφ2 ∈ X) (haX : Module.reflection hψ ∈ X)
    (hc01 : Commute (Module.reflection hφ0) (Module.reflection hφ1))
    (hc02 : Commute (Module.reflection hφ0) (Module.reflection hφ2))
    (hc12 : Commute (Module.reflection hφ1) (Module.reflection hφ2))
    (hne01 : Module.reflection hφ0 ≠ Module.reflection hφ1)
    (hne02 : Module.reflection hφ0 ≠ Module.reflection hφ2)
    (hne12 : Module.reflection hφ1 ≠ Module.reflection hφ2) :
    φ0 r1 = 0 ∧ φ0 r2 = 0 ∧ φ1 r0 = 0 ∧ φ1 r2 = 0 ∧ φ2 r0 = 0 ∧ φ2 r1 = 0 ∧
      r0 ∈ HardMathSupport.Kantor79.commutatorSpace X ∧
      r1 ∈ HardMathSupport.Kantor79.commutatorSpace X ∧
      r2 ∈ HardMathSupport.Kantor79.commutatorSpace X ∧
      r ∈ HardMathSupport.Kantor79.commutatorSpace X := by
  refine ⟨apply_eq_zero_of_commute hp hφ0 hφ1 hc01 hne01,
    apply_eq_zero_of_commute hp hφ0 hφ2 hc02 hne02,
    apply_eq_zero_of_commute hp hφ1 hφ0 hc01.symm hne01.symm,
    apply_eq_zero_of_commute hp hφ1 hφ2 hc12 hne12,
    apply_eq_zero_of_commute hp hφ2 hφ0 hc02.symm hne02.symm,
    apply_eq_zero_of_commute hp hφ2 hφ1 hc12.symm hne12.symm,
    mem_commutatorSpace_of_reflection_mem hp hφ0 h0X,
    mem_commutatorSpace_of_reflection_mem hp hφ1 h1X,
    mem_commutatorSpace_of_reflection_mem hp hφ2 h2X,
    mem_commutatorSpace_of_reflection_mem hp hψ haX⟩

omit [Module.Finite (ZMod p) W] in
private theorem rh3_li (hp : p ≠ 2) {r0 r1 r2 : W}
    {φ0 φ1 φ2 : Module.Dual (ZMod p) W}
    (hφ0 : φ0 r0 = 2) (hφ1 : φ1 r1 = 2) (hφ2 : φ2 r2 = 2)
    (hz01 : φ0 r1 = 0) (hz02 : φ0 r2 = 0) (hz10 : φ1 r0 = 0) (hz12 : φ1 r2 = 0)
    (hz20 : φ2 r0 = 0) (hz21 : φ2 r1 = 0) :
    LinearIndependent (ZMod p) (![r0, r1, r2] : Fin 3 → W) := by
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  refine rh3_linearIndependent_of_det (u := ![r0, r1, r2]) (φ := ![φ0, φ1, φ2]) ?_
  have hmat : (Matrix.of fun i j =>
      (![φ0, φ1, φ2] : Fin 3 → Module.Dual (ZMod p) W) i
        ((![r0, r1, r2] : Fin 3 → W) j)) =
      Matrix.diagonal (fun _ : Fin 3 => (2 : ZMod p)) := by
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [hφ0, hφ1, hφ2, hz01, hz02, hz10, hz12, hz20, hz21]
  rw [hmat, Matrix.det_diagonal]
  simp only [Fin.prod_univ_three]
  exact mul_ne_zero (mul_ne_zero h2ne h2ne) h2ne

omit [Module.Finite (ZMod p) W] in
private theorem rh3_phi_values {r0 r1 r2 r : W}
    {φ0 φ1 φ2 : Module.Dual (ZMod p) W} {y : Fin 3 → ZMod p}
    (hy : (∑ i, y i • (![r0, r1, r2] : Fin 3 → W) i) = r)
    (hφ0 : φ0 r0 = 2) (hφ1 : φ1 r1 = 2) (hφ2 : φ2 r2 = 2)
    (hz01 : φ0 r1 = 0) (hz02 : φ0 r2 = 0) (hz10 : φ1 r0 = 0) (hz12 : φ1 r2 = 0)
    (hz20 : φ2 r0 = 0) (hz21 : φ2 r1 = 0) :
    φ0 r = 2 * y 0 ∧ φ1 r = 2 * y 1 ∧ φ2 r = 2 * y 2 := by
  have hz0 : ∀ j : Fin 3, j ≠ 0 → φ0 ((![r0, r1, r2] : Fin 3 → W) j) = 0 := by
    intro j hj; fin_cases j
    · exact absurd rfl hj
    · simpa using hz01
    · simpa using hz02
  have hz1 : ∀ j : Fin 3, j ≠ 1 → φ1 ((![r0, r1, r2] : Fin 3 → W) j) = 0 := by
    intro j hj; fin_cases j
    · simpa using hz10
    · exact absurd rfl hj
    · simpa using hz12
  have hz2 : ∀ j : Fin 3, j ≠ 2 → φ2 ((![r0, r1, r2] : Fin 3 → W) j) = 0 := by
    intro j hj; fin_cases j
    · simpa using hz20
    · simpa using hz21
    · exact absurd rfl hj
  exact ⟨rh3_phi_r (φ := φ0) (v := ![r0, r1, r2]) hy 0 (c := 2) (by simpa using hφ0) hz0,
    rh3_phi_r (φ := φ1) (v := ![r0, r1, r2]) hy 1 (c := 2) (by simpa using hφ1) hz1,
    rh3_phi_r (φ := φ2) (v := ![r0, r1, r2]) hy 2 (c := 2) (by simpa using hφ2) hz2⟩

omit [Module.Finite (ZMod p) W] in
private theorem rh3_orders (hp : p ≠ 2) (hp5 : p ≠ 5) {r0 r1 r2 r : W}
    {φ0 φ1 φ2 ψ : Module.Dual (ZMod p) W} (hφ0 : φ0 r0 = 2) (hφ1 : φ1 r1 = 2)
    (hφ2 : φ2 r2 = 2) (hψ : ψ r = 2)
    (h0a : orderOf (Module.reflection hφ0 * Module.reflection hψ) = 5)
    (h1a : orderOf (Module.reflection hφ1 * Module.reflection hψ) = 5)
    (h2a : orderOf (Module.reflection hφ2 * Module.reflection hψ) = 3) :
    (φ0 r * ψ r0) ^ 2 - 3 * (φ0 r * ψ r0) + 1 = 0 ∧
      (φ1 r * ψ r1) ^ 2 - 3 * (φ1 r * ψ r1) + 1 = 0 ∧ φ2 r * ψ r2 = 1 :=
  ⟨apply_mul_apply_sq_sub_of_orderOf_eq_five hp hp5 hφ0 hψ h0a,
    apply_mul_apply_sq_sub_of_orderOf_eq_five hp hp5 hφ1 hψ h1a,
    apply_mul_apply_eq_one_of_orderOf_eq_three hp hφ2 hψ h2a⟩

omit [Module.Finite (ZMod p) W] in
private theorem rh3_scalar_data {r r0 r1 r2 : W}
    {φ0 φ1 φ2 ψ : Module.Dual (ZMod p) W} {y : Fin 3 → ZMod p}
    (hφ0r : φ0 r = 2 * y 0) (hφ1r : φ1 r = 2 * y 1) (hφ2r : φ2 r = 2 * y 2)
    (hsum : y 0 * ψ r0 + y 1 * ψ r1 + y 2 * ψ r2 = 2)
    (hp0 : (φ0 r * ψ r0) ^ 2 - 3 * (φ0 r * ψ r0) + 1 = 0)
    (hp1 : (φ1 r * ψ r1) ^ 2 - 3 * (φ1 r * ψ r1) + 1 = 0)
    (hp2 : φ2 r * ψ r2 = 1) :
    ∃ α : ZMod p, α ^ 2 = α + 1 ∧ y 0 ≠ 0 ∧ y 1 ≠ 0 ∧ y 2 ≠ 0 ∧
      ψ r0 ≠ 0 ∧ ψ r1 ≠ 0 ∧ ψ r2 ≠ 0 ∧
      (2 * y 0 * ψ r0 = 2 - α) ∧ (2 * y 1 * ψ r1 = 1 + α) ∧
      (2 * y 2 * ψ r2 = 1) ∧ α - 2 ≠ 0 := by
  let x : Fin 3 → ZMod p := ![ψ r0, ψ r1, ψ r2]
  let c : Fin 3 → ZMod p := fun i => (![φ0, φ1, φ2] i) r * x i
  have hci : ∀ i, c i = 2 * y i * x i := by
    intro i; fin_cases i
    · simp [c, hφ0r]
    · simp [c, hφ1r]
    · simp [c, hφ2r]
  have hc0 : c 0 ^ 2 - 3 * c 0 + 1 = 0 := by simpa [c, x] using hp0
  have hc1 : c 1 ^ 2 - 3 * c 1 + 1 = 0 := by simpa [c, x] using hp1
  have hc2 : c 2 = 1 := by simpa [c, x] using hp2
  have hx0 : x 0 = ψ r0 := rfl
  have hx1 : x 1 = ψ r1 := rfl
  have hx2 : x 2 = ψ r2 := rfl
  have hsumc : c 0 + c 1 + c 2 = 4 := by
    rw [hci 0, hci 1, hci 2, hx0, hx1, hx2]
    linear_combination 2 * hsum
  obtain ⟨hαsq, hc1α, hc0ne, hc1ne, hα2ne⟩ := rh3_alpha_of hc0 hc1 hc2 hsumc
  let α : ZMod p := 2 - c 0
  have hα : α ^ 2 = α + 1 := hαsq
  have hc0α : c 0 = 2 - α := by show c 0 = 2 - (2 - c 0); ring
  have hα2 : α - 2 ≠ 0 := by
    have h : α - 2 = -c 0 := by show (2 - c 0) - 2 = -c 0; ring
    rw [h]; exact neg_ne_zero.mpr hc0ne
  obtain ⟨hy0, hx0⟩ := rh3_mul_ne_zero_of_eq_two (hci 0) hc0ne
  obtain ⟨hy1, hx1⟩ := rh3_mul_ne_zero_of_eq_two (hci 1) hc1ne
  obtain ⟨hy2, hx2⟩ := rh3_mul_ne_zero_of_eq_two (hci 2) (by rw [hc2]; exact one_ne_zero)
  refine ⟨α, hα, hy0, hy1, hy2, ?_, ?_, ?_, ?_, ?_, ?_, hα2⟩
  · simpa [x] using hx0
  · simpa [x] using hx1
  · simpa [x] using hx2
  · simpa [x] using (hci 0).symm.trans hc0α
  · simpa [x] using (hci 1).symm.trans hc1α
  · simpa [x] using (hci 2).symm.trans hc2

omit [Module.Finite (ZMod p) W] in
private theorem rh3_coroot_functions {f : Module.Basis (Fin 4) (ZMod p) W}
    {e : Fin 3 → W} {s : Fin 3 → ZMod p} {φ0 φ1 φ2 : Module.Dual (ZMod p) W}
    (hf : ∀ i : Fin 3, f (Fin.castSucc i) = e i)
    (hφ0e0 : φ0 (e 0) = s 0 * 2) (hφ0e1 : φ0 (e 1) = 0) (hφ0e2 : φ0 (e 2) = 0)
    (hφ1e0 : φ1 (e 0) = 0) (hφ1e1 : φ1 (e 1) = s 1 * 2) (hφ1e2 : φ1 (e 2) = 0)
    (hφ2e0 : φ2 (e 0) = 0) (hφ2e1 : φ2 (e 1) = 0) (hφ2e2 : φ2 (e 2) = s 2 * 2)
    (hφ0w : φ0 (f (Fin.last 3)) = 0) (hφ1w : φ1 (f (Fin.last 3)) = 0)
    (hφ2w : φ2 (f (Fin.last 3)) = 0) :
    ((fun k => φ0 (f k)) = (Pi.single (Fin.castSucc (0 : Fin 3)) (s 0 * 2) : Fin 4 → ZMod p)) ∧
      ((fun k => φ1 (f k)) = (Pi.single (Fin.castSucc (1 : Fin 3)) (s 1 * 2) : Fin 4 → ZMod p)) ∧
      ((fun k => φ2 (f k)) = (Pi.single (Fin.castSucc (2 : Fin 3)) (s 2 * 2) : Fin 4 → ZMod p)) :=
    by
  refine ⟨rh3_coroot_single f 0 (by rw [hf 0]; exact hφ0e0) ?_,
    rh3_coroot_single f 1 (by rw [hf 1]; exact hφ1e1) ?_,
    rh3_coroot_single f 2 (by rw [hf 2]; exact hφ2e2) ?_⟩
  · intro j hj
    induction j using Fin.lastCases with
    | last => simpa using hφ0w
    | cast j =>
        fin_cases j
        · exact absurd rfl hj
        · show φ0 (f (Fin.castSucc 1)) = 0
          rw [hf 1]; exact hφ0e1
        · show φ0 (f (Fin.castSucc 2)) = 0
          rw [hf 2]; exact hφ0e2
  · intro j hj
    induction j using Fin.lastCases with
    | last => simpa using hφ1w
    | cast j =>
        fin_cases j
        · show φ1 (f (Fin.castSucc 0)) = 0
          rw [hf 0]; exact hφ1e0
        · exact absurd rfl hj
        · show φ1 (f (Fin.castSucc 2)) = 0
          rw [hf 2]; exact hφ1e2
  · intro j hj
    induction j using Fin.lastCases with
    | last => simpa using hφ2w
    | cast j =>
        fin_cases j
        · show φ2 (f (Fin.castSucc 0)) = 0
          rw [hf 0]; exact hφ2e0
        · show φ2 (f (Fin.castSucc 1)) = 0
          rw [hf 1]; exact hφ2e1
        · exact absurd rfl hj

omit [Module.Finite (ZMod p) W] in
private theorem rh3_root_functions {f : Module.Basis (Fin 4) (ZMod p) W}
    {e : Fin 3 → W} {s : Fin 3 → ZMod p} {r0 r1 r2 : W}
    (hf : ∀ i : Fin 3, f (Fin.castSucc i) = e i)
    (he0 : e 0 = s 0 • r0) (he1 : e 1 = s 1 • r1) (he2 : e 2 = s 2 • r2)
    (hs : ∀ i, s i ≠ 0) :
    ((fun k => f.repr r0 k) =
        (Pi.single (Fin.castSucc (0 : Fin 3)) ((s 0)⁻¹) : Fin 4 → ZMod p)) ∧
      ((fun k => f.repr r1 k) =
        (Pi.single (Fin.castSucc (1 : Fin 3)) ((s 1)⁻¹) : Fin 4 → ZMod p)) ∧
      ((fun k => f.repr r2 k) =
        (Pi.single (Fin.castSucc (2 : Fin 3)) ((s 2)⁻¹) : Fin 4 → ZMod p)) ∧
      ((s 0)⁻¹ * (s 0 * 2) = 2) ∧ ((s 1)⁻¹ * (s 1 * 2) = 2) ∧ ((s 2)⁻¹ * (s 2 * 2) = 2) := by
  have hr0 : r0 = (s 0)⁻¹ • f (Fin.castSucc (0 : Fin 3)) := by
    rw [show f (Fin.castSucc (0 : Fin 3)) = e 0 from hf 0,
      show e 0 = s 0 • r0 from he0, smul_smul, inv_mul_cancel₀ (hs 0), one_smul]
  have hr1 : r1 = (s 1)⁻¹ • f (Fin.castSucc (1 : Fin 3)) := by
    rw [show f (Fin.castSucc (1 : Fin 3)) = e 1 from hf 1,
      show e 1 = s 1 • r1 from he1, smul_smul, inv_mul_cancel₀ (hs 1), one_smul]
  have hr2 : r2 = (s 2)⁻¹ • f (Fin.castSucc (2 : Fin 3)) := by
    rw [show f (Fin.castSucc (2 : Fin 3)) = e 2 from hf 2,
      show e 2 = s 2 • r2 from he2, smul_smul, inv_mul_cancel₀ (hs 2), one_smul]
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hr0]; exact rh3_repr_smul_self f (Fin.castSucc (0 : Fin 3)) ((s 0)⁻¹)
  · rw [hr1]; exact rh3_repr_smul_self f (Fin.castSucc (1 : Fin 3)) ((s 1)⁻¹)
  · rw [hr2]; exact rh3_repr_smul_self f (Fin.castSucc (2 : Fin 3)) ((s 2)⁻¹)
  · rw [← mul_assoc, inv_mul_cancel₀ (hs 0), one_mul]
  · rw [← mul_assoc, inv_mul_cancel₀ (hs 1), one_mul]
  · rw [← mul_assoc, inv_mul_cancel₀ (hs 2), one_mul]

omit [Module.Finite (ZMod p) W] in
private theorem rh3_repr_r {f : Module.Basis (Fin 4) (ZMod p) W}
    {r0 r1 r2 r : W} {y : Fin 3 → ZMod p} {α : ZMod p}
    (hy : y 0 • r0 + y 1 • r1 + y 2 • r2 = r) (hα2 : α - 2 ≠ 0)
    (hf0 : f 0 = (y 0 * (α - 2)⁻¹) • r0) (hf1 : f 1 = y 1 • r1)
    (hf2 : f 2 = y 2 • r2) :
    (fun k => f.repr r k) = (![α - 2, 1, 1, 0] : Fin 4 → ZMod p) := by
  have hr : r = ∑ i, (![α - 2, 1, 1, 0] : Fin 4 → ZMod p) i • f i := by
    rw [← hy, Fin.sum_univ_four]
    rw [show (![α - 2, 1, 1, 0] : Fin 4 → ZMod p) 0 = α - 2 from rfl,
      show (![α - 2, 1, 1, 0] : Fin 4 → ZMod p) 1 = 1 from rfl,
      show (![α - 2, 1, 1, 0] : Fin 4 → ZMod p) 2 = 1 from rfl,
      show (![α - 2, 1, 1, 0] : Fin 4 → ZMod p) 3 = 0 from rfl,
      one_smul, zero_smul, add_zero]
    rw [hf0, hf1, hf2, smul_smul, rh3_scale_comm (α - 2) (y 0) hα2]
    simp
  exact rh3_repr_eq_of_sum f hr

omit [Module.Finite (ZMod p) W] in
private theorem rh3_psi_f {f : Module.Basis (Fin 4) (ZMod p) W} {α : ZMod p}
    {ψ : Module.Dual (ZMod p) W}
    (hψ0 : ψ (f (Fin.castSucc (0 : Fin 3))) = -(2 : ZMod p)⁻¹)
    (hψ1 : ψ (f (Fin.castSucc (1 : Fin 3))) = (1 + α) * (2 : ZMod p)⁻¹)
    (hψ2 : ψ (f (Fin.castSucc (2 : Fin 3))) = (2 : ZMod p)⁻¹)
    (hψw : ψ (f (Fin.last 3)) = 0) :
    (fun k => ψ (f k)) =
      (![-(2 : ZMod p)⁻¹, (1 + α) * (2 : ZMod p)⁻¹, (2 : ZMod p)⁻¹, 0] : Fin 4 → ZMod p) := by
  have hd0 : (![-(2 : ZMod p)⁻¹, (1 + α) * (2 : ZMod p)⁻¹, (2 : ZMod p)⁻¹, 0] : Fin 4 → ZMod p)
      (Fin.castSucc (0 : Fin 3)) = -(2 : ZMod p)⁻¹ := rfl
  have hd1 : (![-(2 : ZMod p)⁻¹, (1 + α) * (2 : ZMod p)⁻¹, (2 : ZMod p)⁻¹, 0] : Fin 4 → ZMod p)
      (Fin.castSucc (1 : Fin 3)) = (1 + α) * (2 : ZMod p)⁻¹ := rfl
  have hd2 : (![-(2 : ZMod p)⁻¹, (1 + α) * (2 : ZMod p)⁻¹, (2 : ZMod p)⁻¹, 0] : Fin 4 → ZMod p)
      (Fin.castSucc (2 : Fin 3)) = (2 : ZMod p)⁻¹ := rfl
  have hd3 : (![-(2 : ZMod p)⁻¹, (1 + α) * (2 : ZMod p)⁻¹, (2 : ZMod p)⁻¹, 0] : Fin 4 → ZMod p)
      (Fin.last 3) = 0 := rfl
  funext k
  induction k using Fin.lastCases with
  | last => rw [hd3]; exact hψw
  | cast j =>
      fin_cases j
      · show ψ (f (Fin.castSucc (0 : Fin 3))) =
            (![-(2 : ZMod p)⁻¹, (1 + α) * (2 : ZMod p)⁻¹, (2 : ZMod p)⁻¹, 0] : Fin 4 → ZMod p)
              (Fin.castSucc (0 : Fin 3))
        rw [hd0]; exact hψ0
      · show ψ (f (Fin.castSucc (1 : Fin 3))) =
            (![-(2 : ZMod p)⁻¹, (1 + α) * (2 : ZMod p)⁻¹, (2 : ZMod p)⁻¹, 0] : Fin 4 → ZMod p)
              (Fin.castSucc (1 : Fin 3))
        rw [hd1]; exact hψ1
      · show ψ (f (Fin.castSucc (2 : Fin 3))) =
            (![-(2 : ZMod p)⁻¹, (1 + α) * (2 : ZMod p)⁻¹, (2 : ZMod p)⁻¹, 0] : Fin 4 → ZMod p)
              (Fin.castSucc (2 : Fin 3))
        rw [hd2]; exact hψ2

omit [Module.Finite (ZMod p) W] in
private theorem rh3_matrix_h0 {f : Module.Basis (Fin 4) (ZMod p) W}
    {h0 : W ≃ₗ[ZMod p] W} {r0 : W} {φ0 : Module.Dual (ZMod p) W} {s0 : ZMod p}
    (hφ0 : φ0 r0 = 2) (h0eq : h0 = Module.reflection hφ0) (hcd0 : s0⁻¹ * (s0 * 2) = 2)
    (hr0 : (fun k => f.repr r0 k) =
      (Pi.single (Fin.castSucc (0 : Fin 3)) s0⁻¹ : Fin 4 → ZMod p))
    (hφf0 : (fun k => φ0 (f k)) =
      (Pi.single (Fin.castSucc (0 : Fin 3)) (s0 * 2) : Fin 4 → ZMod p)) :
    LinearMap.toMatrix f f (h0 : W →ₗ[ZMod p] W) = Matrix.blockSucc (diagSignMat (0 : Fin 3)) := by
  rw [h0eq]
  exact rh3_toMatrix_reflection_diagSignMat (f := f) hφ0 (i := 0) hcd0
    (fun j => congrFun hr0 j) (fun j => congrFun hφf0 j)

omit [Module.Finite (ZMod p) W] in
private theorem rh3_matrix_h1 {f : Module.Basis (Fin 4) (ZMod p) W}
    {h1 : W ≃ₗ[ZMod p] W} {r1 : W} {φ1 : Module.Dual (ZMod p) W} {s1 : ZMod p}
    (hφ1 : φ1 r1 = 2) (h1eq : h1 = Module.reflection hφ1) (hcd1 : s1⁻¹ * (s1 * 2) = 2)
    (hr1 : (fun k => f.repr r1 k) =
      (Pi.single (Fin.castSucc (1 : Fin 3)) s1⁻¹ : Fin 4 → ZMod p))
    (hφf1 : (fun k => φ1 (f k)) =
      (Pi.single (Fin.castSucc (1 : Fin 3)) (s1 * 2) : Fin 4 → ZMod p)) :
    LinearMap.toMatrix f f (h1 : W →ₗ[ZMod p] W) = Matrix.blockSucc (diagSignMat (1 : Fin 3)) := by
  rw [h1eq]
  exact rh3_toMatrix_reflection_diagSignMat (f := f) hφ1 (i := 1) hcd1
    (fun j => congrFun hr1 j) (fun j => congrFun hφf1 j)

omit [Module.Finite (ZMod p) W] in
private theorem rh3_matrix_h2 {f : Module.Basis (Fin 4) (ZMod p) W}
    {h2 : W ≃ₗ[ZMod p] W} {r2 : W} {φ2 : Module.Dual (ZMod p) W} {s2 : ZMod p}
    (hφ2 : φ2 r2 = 2) (h2eq : h2 = Module.reflection hφ2) (hcd2 : s2⁻¹ * (s2 * 2) = 2)
    (hr2 : (fun k => f.repr r2 k) =
      (Pi.single (Fin.castSucc (2 : Fin 3)) s2⁻¹ : Fin 4 → ZMod p))
    (hφf2 : (fun k => φ2 (f k)) =
      (Pi.single (Fin.castSucc (2 : Fin 3)) (s2 * 2) : Fin 4 → ZMod p)) :
    LinearMap.toMatrix f f (h2 : W →ₗ[ZMod p] W) = Matrix.blockSucc (diagSignMat (2 : Fin 3)) := by
  rw [h2eq]
  exact rh3_toMatrix_reflection_diagSignMat (f := f) hφ2 (i := 2) hcd2
    (fun j => congrFun hr2 j) (fun j => congrFun hφf2 j)

omit [Module.Finite (ZMod p) W] in
private theorem rh3_matrix_a {f : Module.Basis (Fin 4) (ZMod p) W}
    {a : W ≃ₗ[ZMod p] W} {r : W} {ψ : Module.Dual (ZMod p) W} {α : ZMod p}
    (hψ : ψ r = 2) (haeq : a = Module.reflection hψ) (hα : α ^ 2 = α + 1)
    (h2ne : (2 : ZMod p) ≠ 0)
    (hrepr_r : (fun k => f.repr r k) = (![α - 2, 1, 1, 0] : Fin 4 → ZMod p))
    (hψf : (fun k => ψ (f k)) =
      (![-(2 : ZMod p)⁻¹, (1 + α) * (2 : ZMod p)⁻¹, (2 : ZMod p)⁻¹, 0] : Fin 4 → ZMod p)) :
    LinearMap.toMatrix f f (a : W →ₗ[ZMod p] W) = Matrix.blockSucc (h3BlockMat α) := by
  rw [haeq]
  exact rh3_toMatrix_reflection_h3BlockMat (f := f) hψ hα h2ne
    (fun i => congrFun hrepr_r i) (fun i => congrFun hψf i)

private theorem rh3_setup (hp : p ≠ 2) {X : Subgroup (W ≃ₗ[ZMod p] W)} (hF : H3Frame p X) :
    ∃ (h0 h1 h2 a : W ≃ₗ[ZMod p] W) (r0 r1 r2 r : W)
      (φ0 φ1 φ2 ψ : Module.Dual (ZMod p) W)
      (hφ0 : φ0 r0 = 2) (hφ1 : φ1 r1 = 2) (hφ2 : φ2 r2 = 2) (hψ : ψ r = 2),
      h0 ∈ X ∧ h1 ∈ X ∧ h2 ∈ X ∧ a ∈ X ∧
      h0 = Module.reflection hφ0 ∧ h1 = Module.reflection hφ1 ∧
      h2 = Module.reflection hφ2 ∧ a = Module.reflection hψ ∧
      φ0 r1 = 0 ∧ φ0 r2 = 0 ∧ φ1 r0 = 0 ∧ φ1 r2 = 0 ∧ φ2 r0 = 0 ∧ φ2 r1 = 0 ∧
      r0 ∈ HardMathSupport.Kantor79.commutatorSpace X ∧
      r1 ∈ HardMathSupport.Kantor79.commutatorSpace X ∧
      r2 ∈ HardMathSupport.Kantor79.commutatorSpace X ∧
      r ∈ HardMathSupport.Kantor79.commutatorSpace X ∧
      orderOf (h0 * a) = 5 ∧ orderOf (h1 * a) = 5 ∧ orderOf (h2 * a) = 3 := by
  obtain ⟨h0, hh0, h1, hh1, h2, hh2, a, ha, h0r, h1r, h2r, har, hne01, hne02, hne12,
    hc01, hc02, hc12, h0a, h1a, h2a⟩ := hF
  obtain ⟨r0, φ0, hφ0, h0eq⟩ := (isRefl_iff hp h0).mp h0r
  obtain ⟨r1, φ1, hφ1, h1eq⟩ := (isRefl_iff hp h1).mp h1r
  obtain ⟨r2, φ2, hφ2, h2eq⟩ := (isRefl_iff hp h2).mp h2r
  obtain ⟨r, ψ, hψ, haeq⟩ := (isRefl_iff hp a).mp har
  have h0X : Module.reflection hφ0 ∈ X := by rw [← h0eq]; exact hh0
  have h1X : Module.reflection hφ1 ∈ X := by rw [← h1eq]; exact hh1
  have h2X : Module.reflection hφ2 ∈ X := by rw [← h2eq]; exact hh2
  have haX : Module.reflection hψ ∈ X := by rw [← haeq]; exact ha
  have hc01' : Commute (Module.reflection hφ0) (Module.reflection hφ1) := by
    rw [← h0eq, ← h1eq]; exact hc01
  have hc02' : Commute (Module.reflection hφ0) (Module.reflection hφ2) := by
    rw [← h0eq, ← h2eq]; exact hc02
  have hc12' : Commute (Module.reflection hφ1) (Module.reflection hφ2) := by
    rw [← h1eq, ← h2eq]; exact hc12
  have hne01' : Module.reflection hφ0 ≠ Module.reflection hφ1 := by
    intro h; exact hne01 (by rw [h0eq, h1eq, h])
  have hne02' : Module.reflection hφ0 ≠ Module.reflection hφ2 := by
    intro h; exact hne02 (by rw [h0eq, h2eq, h])
  have hne12' : Module.reflection hφ1 ≠ Module.reflection hφ2 := by
    intro h; exact hne12 (by rw [h1eq, h2eq, h])
  obtain ⟨hz01, hz02, hz10, hz12, hz20, hz21, hr0V, hr1V, hr2V, hrV⟩ :=
    rh3_frame_zeros hp hφ0 hφ1 hφ2 hψ h0X h1X h2X haX hc01' hc02' hc12' hne01' hne02' hne12'
  exact ⟨h0, h1, h2, a, r0, r1, r2, r, φ0, φ1, φ2, ψ, hφ0, hφ1, hφ2, hψ,
    hh0, hh1, hh2, ha, h0eq, h1eq, h2eq, haeq, hz01, hz02, hz10, hz12, hz20, hz21,
    hr0V, hr1V, hr2V, hrV, h0a, h1a, h2a⟩

private theorem rh3_scalars (hp : p ≠ 2) (hp5 : p ≠ 5)
    {X : Subgroup (W ≃ₗ[ZMod p] W)} (hX : SplitSupport X 3)
    {r0 r1 r2 r : W} {φ0 φ1 φ2 ψ : Module.Dual (ZMod p) W}
    (hφ0 : φ0 r0 = 2) (hφ1 : φ1 r1 = 2) (hφ2 : φ2 r2 = 2) (hψ : ψ r = 2)
    (hz01 : φ0 r1 = 0) (hz02 : φ0 r2 = 0) (hz10 : φ1 r0 = 0) (hz12 : φ1 r2 = 0)
    (hz20 : φ2 r0 = 0) (hz21 : φ2 r1 = 0)
    (hr0V : r0 ∈ HardMathSupport.Kantor79.commutatorSpace X)
    (hr1V : r1 ∈ HardMathSupport.Kantor79.commutatorSpace X)
    (hr2V : r2 ∈ HardMathSupport.Kantor79.commutatorSpace X)
    (hrV : r ∈ HardMathSupport.Kantor79.commutatorSpace X)
    (h0a : orderOf (Module.reflection hφ0 * Module.reflection hψ) = 5)
    (h1a : orderOf (Module.reflection hφ1 * Module.reflection hψ) = 5)
    (h2a : orderOf (Module.reflection hφ2 * Module.reflection hψ) = 3) :
    ∃ (y : Fin 3 → ZMod p) (α : ZMod p) (s : Fin 3 → ZMod p),
      (2 * y 0 * ψ r0 = 2 - α) ∧ (2 * y 1 * ψ r1 = 1 + α) ∧ (2 * y 2 * ψ r2 = 1) ∧
      (∀ i, s i ≠ 0) ∧ s 0 = y 0 * (α - 2)⁻¹ ∧ s 1 = y 1 ∧ s 2 = y 2 ∧
      α ^ 2 = α + 1 ∧ (y 0 • r0 + y 1 • r1 + y 2 • r2 = r) ∧ α - 2 ≠ 0 ∧
      (∀ i, (![r0, r1, r2] : Fin 3 → W) i ∈ HardMathSupport.Kantor79.commutatorSpace X) := by
  have hvli : LinearIndependent (ZMod p) (![r0, r1, r2] : Fin 3 → W) :=
    rh3_li hp hφ0 hφ1 hφ2 hz01 hz02 hz10 hz12 hz20 hz21
  have hvV : ∀ i, (![r0, r1, r2] : Fin 3 → W) i ∈
      HardMathSupport.Kantor79.commutatorSpace X := by
    intro i; fin_cases i
    · exact hr0V
    · exact hr1V
    · exact hr2V
  obtain ⟨y, hy⟩ := rh3_span_y (r0 := r0) (r1 := r1) (r2 := r2) (X := X) (r := r)
    hvli hvV hrV hX.2.1
  let v : Fin 3 → W := ![r0, r1, r2]
  have hyv : (∑ i, y i • v i) = r := by simpa [v] using hy
  have hy' : y 0 • r0 + y 1 • r1 + y 2 • r2 = r := by
    simpa [v, Fin.sum_univ_three] using hyv
  obtain ⟨hφ0r, hφ1r, hφ2r⟩ :=
    rh3_phi_values hy hφ0 hφ1 hφ2 hz01 hz02 hz10 hz12 hz20 hz21
  have hsum : y 0 * ψ r0 + y 1 * ψ r1 + y 2 * ψ r2 = 2 := by
    have h := hψ
    rw [← hyv, rh3_dual_sum] at h
    simpa [v, Fin.sum_univ_three] using h
  obtain ⟨hp0, hp1, hp2⟩ := rh3_orders hp hp5 hφ0 hφ1 hφ2 hψ h0a h1a h2a
  obtain ⟨α, hα, hy0, hy1, hy2, -, -, -, h20, h21, h22, hα2⟩ :=
    rh3_scalar_data hφ0r hφ1r hφ2r hsum hp0 hp1 hp2
  refine ⟨y, α, ![y 0 * (α - 2)⁻¹, y 1, y 2], h20, h21, h22, ?_, rfl, rfl, rfl, hα, hy', hα2,
    hvV⟩
  intro i; fin_cases i
  · show y 0 * (α - 2)⁻¹ ≠ 0
    exact mul_ne_zero hy0 (inv_ne_zero hα2)
  · simpa using hy1
  · simpa using hy2

private theorem rh3_basis (hW : Module.finrank (ZMod p) W = 4)
    {X : Subgroup (W ≃ₗ[ZMod p] W)} (hX : SplitSupport X 3) {e : Fin 3 → W}
    (hvli : LinearIndependent (ZMod p) e)
    (hvV : ∀ i, e i ∈ HardMathSupport.Kantor79.commutatorSpace X) :
    ∃ f : Module.Basis (Fin 4) (ZMod p) W,
      f 0 = e 0 ∧ f 1 = e 1 ∧ f 2 = e 2 ∧ (∀ i : Fin 3, f i.castSucc = e i) ∧
      f (Fin.last 3) ∈ centralizerSpace X ∧
      (∀ i : Fin 3, f i.castSucc ∈ HardMathSupport.Kantor79.commutatorSpace X) := by
  obtain ⟨f, hf, hflast⟩ := exists_basis_snoc_of_splitSupport hX (by rw [hW]) hvli hvV
  have hf0 : f 0 = e 0 := by have h := hf 0; rw [Fin.castSucc_zero] at h; simpa using h
  have hf1 : f 1 = e 1 := by have h := hf 1; rw [Fin.castSucc_one] at h; simpa using h
  have hf2 : f 2 = e 2 := by
    have h := hf 2
    rw [show (Fin.castSucc (2 : Fin 3)) = (2 : Fin 4) from rfl] at h
    simpa using h
  have hfV : ∀ i : Fin 3, f i.castSucc ∈ HardMathSupport.Kantor79.commutatorSpace X :=
    fun i => by rw [hf i]; exact hvV i
  exact ⟨f, hf0, hf1, hf2, hf, hflast, hfV⟩

omit [Module.Finite (ZMod p) W] in
private theorem rh3_e_data {v : Fin 3 → W} {s : Fin 3 → ZMod p} {X : Subgroup (W ≃ₗ[ZMod p] W)}
    (hvli : LinearIndependent (ZMod p) v)
    (hvV : ∀ i, v i ∈ HardMathSupport.Kantor79.commutatorSpace X) (hs : ∀ i, s i ≠ 0) :
    LinearIndependent (ZMod p) (fun i => s i • v i) ∧
      (∀ i, s i • v i ∈ HardMathSupport.Kantor79.commutatorSpace X) :=
  ⟨rh3_linearIndependent_smul hvli hs, fun i => Submodule.smul_mem _ (s i) (hvV i)⟩

omit [Module.Finite (ZMod p) W] in
private theorem rh3_pair_data {α : ZMod p} {y : Fin 3 → ZMod p} {s : Fin 3 → ZMod p}
    {e : Fin 3 → W} {r0 r1 r2 : W} {φ0 φ1 φ2 ψ : Module.Dual (ZMod p) W}
    (he0 : e 0 = s 0 • r0) (he1 : e 1 = s 1 • r1) (he2 : e 2 = s 2 • r2)
    (hs0 : s 0 = y 0 * (α - 2)⁻¹) (hs1 : s 1 = y 1) (hs2 : s 2 = y 2)
    (hφ0 : φ0 r0 = 2) (hφ1 : φ1 r1 = 2) (hφ2 : φ2 r2 = 2)
    (hz01 : φ0 r1 = 0) (hz02 : φ0 r2 = 0) (hz10 : φ1 r0 = 0) (hz12 : φ1 r2 = 0)
    (hz20 : φ2 r0 = 0) (hz21 : φ2 r1 = 0)
    (h20 : 2 * y 0 * ψ r0 = 2 - α) (h21 : 2 * y 1 * ψ r1 = 1 + α)
    (h22 : 2 * y 2 * ψ r2 = 1) (hα2 : α - 2 ≠ 0) (h2ne : (2 : ZMod p) ≠ 0) :
    φ0 (e 0) = s 0 * 2 ∧ φ0 (e 1) = 0 ∧ φ0 (e 2) = 0 ∧
      φ1 (e 0) = 0 ∧ φ1 (e 1) = s 1 * 2 ∧ φ1 (e 2) = 0 ∧
      φ2 (e 0) = 0 ∧ φ2 (e 1) = 0 ∧ φ2 (e 2) = s 2 * 2 ∧
      ψ (e 0) = -(2 : ZMod p)⁻¹ ∧ ψ (e 1) = (1 + α) * (2 : ZMod p)⁻¹ ∧
      ψ (e 2) = (2 : ZMod p)⁻¹ := by
  have hφ0e0 : φ0 (e 0) = s 0 * 2 := by rw [he0, map_smul, smul_eq_mul, hφ0]
  have hφ0e1 : φ0 (e 1) = 0 := by rw [he1, map_smul, smul_eq_mul, hz01, mul_zero]
  have hφ0e2 : φ0 (e 2) = 0 := by rw [he2, map_smul, smul_eq_mul, hz02, mul_zero]
  have hφ1e0 : φ1 (e 0) = 0 := by rw [he0, map_smul, smul_eq_mul, hz10, mul_zero]
  have hφ1e1 : φ1 (e 1) = s 1 * 2 := by rw [he1, map_smul, smul_eq_mul, hφ1]
  have hφ1e2 : φ1 (e 2) = 0 := by rw [he2, map_smul, smul_eq_mul, hz12, mul_zero]
  have hφ2e0 : φ2 (e 0) = 0 := by rw [he0, map_smul, smul_eq_mul, hz20, mul_zero]
  have hφ2e1 : φ2 (e 1) = 0 := by rw [he1, map_smul, smul_eq_mul, hz21, mul_zero]
  have hφ2e2 : φ2 (e 2) = s 2 * 2 := by rw [he2, map_smul, smul_eq_mul, hφ2]
  have hψe0 : ψ (e 0) = -(2 : ZMod p)⁻¹ := by
    rw [he0, hs0, map_smul, smul_eq_mul]
    exact rh3_coroot_zero (α := α) (y := y 0) (x := ψ r0) h2ne hα2 h20
  have hψe1 : ψ (e 1) = (1 + α) * (2 : ZMod p)⁻¹ := by
    rw [he1, hs1, map_smul, smul_eq_mul]
    exact rh3_coroot_one (α := α) (y := y 1) (x := ψ r1) h2ne h21
  have hψe2 : ψ (e 2) = (2 : ZMod p)⁻¹ := by
    rw [he2, hs2, map_smul, smul_eq_mul]
    exact rh3_coroot_two (y := y 2) (x := ψ r2) h2ne h22
  exact ⟨hφ0e0, hφ0e1, hφ0e2, hφ1e0, hφ1e1, hφ1e2, hφ2e0, hφ2e1, hφ2e2,
    hψe0, hψe1, hψe2⟩

omit [Module.Finite (ZMod p) W] in
private theorem rh3_conclude (hp : p ≠ 2) {X : Subgroup (W ≃ₗ[ZMod p] W)}
    (hcard : Nat.card X = 120) {f : Module.Basis (Fin 4) (ZMod p) W}
    {h0 h1 h2 a : W ≃ₗ[ZMod p] W} {α : ZMod p} (hα : α ^ 2 = α + 1)
    (hh0X : h0 ∈ X) (hh1X : h1 ∈ X) (hh2X : h2 ∈ X) (haX : a ∈ X)
    (hm0 : LinearMap.toMatrix f f (h0 : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (diagSignMat (0 : Fin 3)))
    (hm1 : LinearMap.toMatrix f f (h1 : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (diagSignMat (1 : Fin 3)))
    (hm2 : LinearMap.toMatrix f f (h2 : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (diagSignMat (2 : Fin 3)))
    (hma : LinearMap.toMatrix f f (a : W →ₗ[ZMod p] W) = Matrix.blockSucc (h3BlockMat α)) :
    X = basisClosure f (h3Mats α) :=
  rh3_final hp hcard hα hh0X hh1X hh2X haX hm0 hm1 hm2 hma

private theorem rh3_exists (hp : p ≠ 2) (hp5 : p ≠ 5) (hW : Module.finrank (ZMod p) W = 4)
    {X : Subgroup (W ≃ₗ[ZMod p] W)} (hX : SplitSupport X 3) (hcard : Nat.card X = 120)
    (hF : H3Frame p X) :
    ∃ (α : ZMod p) (f : Module.Basis (Fin 4) (ZMod p) W),
      α ^ 2 = α + 1 ∧ X = basisClosure f (h3Mats α) := by
  classical
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨h0, h1, h2, a, r0, r1, r2, r, φ0, φ1, φ2, ψ, hφ0, hφ1, hφ2, hψ, hh0, hh1, hh2,
    ha, h0eq, h1eq, h2eq, haeq, hz01, hz02, hz10, hz12, hz20, hz21, hr0V, hr1V, hr2V, hrV,
    h0a, h1a, h2a⟩ := rh3_setup hp hF
  obtain ⟨y, α, s, h20, h21, h22, hs, hs0, hs1, hs2, hα, hy', hα2, hvV⟩ :=
    rh3_scalars hp hp5 hX hφ0 hφ1 hφ2 hψ hz01 hz02 hz10 hz12 hz20 hz21
      hr0V hr1V hr2V hrV (by rw [← h0eq, ← haeq]; exact h0a)
      (by rw [← h1eq, ← haeq]; exact h1a) (by rw [← h2eq, ← haeq]; exact h2a)
  let v : Fin 3 → W := ![r0, r1, r2]
  let e : Fin 3 → W := fun i => s i • v i
  have hvli : LinearIndependent (ZMod p) v :=
    by simpa [v] using rh3_li hp hφ0 hφ1 hφ2 hz01 hz02 hz10 hz12 hz20 hz21
  obtain ⟨he, heV⟩ := rh3_e_data hvli (by simpa [v] using hvV) hs
  obtain ⟨f, hf0, hf1, hf2, hf, hflast, hfV⟩ := rh3_basis hW hX he heV
  obtain ⟨hr0, hr1, hr2, hcd0, hcd1, hcd2⟩ :=
    rh3_root_functions (e := e) (s := s) (r0 := r0) (r1 := r1) (r2 := r2)
      hf (by rfl) (by rfl) (by rfl) hs
  obtain ⟨hφ0e0, hφ0e1, hφ0e2, hφ1e0, hφ1e1, hφ1e2, hφ2e0, hφ2e1, hφ2e2,
    hψe0, hψe1, hψe2⟩ :=
    rh3_pair_data (e := e) (s := s) (r0 := r0) (r1 := r1) (r2 := r2)
      (by rfl) (by rfl) (by rfl) hs0 hs1 hs2 hφ0 hφ1 hφ2 hz01 hz02 hz10 hz12 hz20
      hz21 h20 h21 h22 hα2 h2ne
  obtain ⟨hφf0, hφf1, hφf2⟩ :=
    rh3_coroot_functions (e := e) (s := s) hf hφ0e0 hφ0e1 hφ0e2 hφ1e0 hφ1e1 hφ1e2 hφ2e0 hφ2e1
      hφ2e2 (apply_eq_zero_of_reflection_mem hp hφ0 (by rw [← h0eq]; exact hh0) hflast)
      (apply_eq_zero_of_reflection_mem hp hφ1 (by rw [← h1eq]; exact hh1) hflast)
      (apply_eq_zero_of_reflection_mem hp hφ2 (by rw [← h2eq]; exact hh2) hflast)
  have hψw : ψ (f (Fin.last 3)) = 0 :=
    apply_eq_zero_of_reflection_mem hp hψ (by rw [← haeq]; exact ha) hflast
  have hψf := rh3_psi_f (by rw [hf 0]; exact hψe0) (by rw [hf 1]; exact hψe1)
    (by rw [hf 2]; exact hψe2) hψw
  have hf0' : f 0 = (y 0 * (α - 2)⁻¹) • r0 := by
    rw [hf0, show v 0 = r0 from rfl, hs0]
  have hf1' : f 1 = y 1 • r1 := by rw [hf1, show v 1 = r1 from rfl, hs1]
  have hf2' : f 2 = y 2 • r2 := by rw [hf2, show v 2 = r2 from rfl, hs2]
  have hrepr_r := rh3_repr_r hy' hα2 hf0' hf1' hf2'
  exact ⟨α, f, hα, rh3_conclude hp hcard hα hh0 hh1 hh2 ha
    (rh3_matrix_h0 hφ0 h0eq hcd0 hr0 hφf0)
    (rh3_matrix_h1 hφ1 h1eq hcd1 hr1 hφf1)
    (rh3_matrix_h2 hφ2 h2eq hcd2 hr2 hφf2)
    (rh3_matrix_a hψ haeq hα h2ne hrepr_r hψf)⟩

theorem exists_basis_eq_h3Mats_of_h3Frame (hp : p ≠ 2) (hp5 : p ≠ 5)
    (hW : Module.finrank (ZMod p) W = 4) {X : Subgroup (W ≃ₗ[ZMod p] W)} (hX : SplitSupport X 3)
    (hcard : Nat.card X = 120) (hF : H3Frame p X) :
    ∃ (α : ZMod p) (f : Module.Basis (Fin 4) (ZMod p) W),
      α ^ 2 = α + 1 ∧ X = basisClosure f (h3Mats α) := by
  exact rh3_exists hp hp5 hW hX hcard hF

end CFSG.StandardType.ZS

end
