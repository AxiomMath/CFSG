module

public import CFSG.LocalAnalysis.StandardType.ZS.ReflFrame
public import CFSG.LocalAnalysis.StandardType.ZS.PrimExtMatrices
import CFSG.LocalAnalysis.StandardType.ZS.ExcMatricesRefl
import CFSG.LocalAnalysis.StandardType.ZS.ImpExtF4Refl
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtBond
import CFSG.LocalAnalysis.StandardType.ZS.PrimExtModelJ34
import CFSG.LocalAnalysis.StandardType.ZS.ReflProductOrder
import CFSG.LocalAnalysis.StandardType.ZS.RootMatrix

public section

namespace CFSG.StandardType.ZS

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

variable {p : ℕ} [Fact p.Prime] {W : Type} [AddCommGroup W] [Module (ZMod p) W]

section Matrices

variable {K : Type} [Field K] {V : Type} [AddCommGroup V] [Module K V]

private theorem rj34_diagSignMat_toMatrix {n : ℕ} (f : Module.Basis (Fin n) K V) {r : V}
    {φ : Module.Dual K V} (hφ : φ r = 2) (i : Fin n)
    (hr : (fun k => f.repr r k) = Pi.single i 1)
    (hκ : (fun k => φ (f k)) = Pi.single i 2) :
    LinearMap.toMatrix f f (Module.reflection hφ : V →ₗ[K] V) = diagSignMat i := by
  rw [toMatrix_reflection f hφ, hr, hκ, ← diagSignMat_eq_one_sub_vecMulVec]

private theorem rj34_pijMat_toMatrix {n : ℕ} (f : Module.Basis (Fin n) K V) {r : V}
    {φ : Module.Dual K V} (hφ : φ r = 2) {i j : Fin n} (hij : i ≠ j) {c : K} (hc : c ≠ 0)
    (hr : (fun k => f.repr r k) = c⁻¹ • (Pi.single i 1 - Pi.single j 1))
    (hκ : (fun k => φ (f k)) = c • (Pi.single i 1 - Pi.single j 1)) :
    LinearMap.toMatrix f f (Module.reflection hφ : V →ₗ[K] V) = pijMat i j 1 := by
  rw [toMatrix_reflection f hφ, hr, hκ, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul,
    smul_smul, inv_mul_cancel₀ hc, one_smul]
  rw [pijMat_eq_one_sub_vecMulVec (K := K) hij one_ne_zero]
  simp

private theorem rj34_blockSucc_sub_vecMulVec {n : ℕ} (v w : Fin (n + 1) → K)
    (hv : v (Fin.last n) = 0) (hw : w (Fin.last n) = 0) :
    (1 : Matrix (Fin (n + 1)) (Fin (n + 1)) K) - Matrix.vecMulVec v w =
      Matrix.blockSucc ((1 : Matrix (Fin n) (Fin n) K) -
        Matrix.vecMulVec (fun i : Fin n => v i.castSucc) (fun i : Fin n => w i.castSucc)) := by
  ext i j
  induction i using Fin.lastCases with
  | last =>
    induction j using Fin.lastCases with
    | last => simp [Matrix.vecMulVec_apply, Matrix.sub_apply, hv, hw]
    | cast j => simp [Matrix.vecMulVec_apply, Matrix.sub_apply, hv,
        (Fin.castSucc_lt_last j).ne']
  | cast i =>
    induction j using Fin.lastCases with
    | last => simp [Matrix.vecMulVec_apply, Matrix.sub_apply, hw,
        (Fin.castSucc_lt_last i).ne]
    | cast j => simp [Matrix.vecMulVec_apply, Matrix.sub_apply, Matrix.one_apply,
        Fin.castSucc_inj]

private theorem rj34_j34BlockMat_eq {β : K} (h2 : (2 : K) ≠ 0) (hβ0 : β ≠ 0) :
    j34BlockMat β = 1 - (2 : K)⁻¹ • Matrix.vecMulVec (![1, -2 * β, -1] : Fin 3 → K)
      (![1, -β⁻¹, -1] : Fin 3 → K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [j34BlockMat, Matrix.sub_apply, Matrix.smul_apply] <;>
    field_simp [h2, hβ0] <;> ring

private theorem rj34_blockSucc_vecMulVec_one_zero_one :
    Matrix.blockSucc ((1 : Matrix (Fin 3) (Fin 3) K) -
        Matrix.vecMulVec (![1, 0, 1] : Fin 3 → K) (![1, 0, 1] : Fin 3 → K)) =
      (1 : Matrix (Fin 4) (Fin 4) K) -
        Matrix.vecMulVec (![1, 0, 1, 0] : Fin 4 → K) (![1, 0, 1, 0] : Fin 4 → K) := by
  have hv : (fun i : Fin 3 => (![1, 0, 1, 0] : Fin 4 → K) i.castSucc) =
      (![1, 0, 1] : Fin 3 → K) := by
    funext i; fin_cases i <;> rfl
  rw [rj34_blockSucc_sub_vecMulVec (![1, 0, 1, 0] : Fin 4 → K)
    (![1, 0, 1, 0] : Fin 4 → K) (by simp) (by simp), hv]

private theorem rj34_word_matrix :
    (pijMat (1 : Fin 3) 2 1 * pijMat (0 : Fin 3) 1 1) * diagSignMat (0 : Fin 3) *
        (pijMat (1 : Fin 3) 2 1 * pijMat (0 : Fin 3) 1 1) ^ 2 *
        (pijMat (0 : Fin 3) 1 1 * pijMat (1 : Fin 3) 2 1 * pijMat (0 : Fin 3) 1 1) *
        ((pijMat (1 : Fin 3) 2 1 * pijMat (0 : Fin 3) 1 1) * diagSignMat (0 : Fin 3) *
          (pijMat (1 : Fin 3) 2 1 * pijMat (0 : Fin 3) 1 1) ^ 2) =
      (1 : Matrix (Fin 3) (Fin 3) K) -
        Matrix.vecMulVec (![1, 0, 1] : Fin 3 → K) (![1, 0, 1] : Fin 3 → K) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [pow_two, diagSignMat, pijMat, Matrix.mul_apply, Matrix.sub_apply,
      Fin.sum_univ_three]

private theorem rj34_toMatrix_j34BlockMat {β y0 : K} (h2 : (2 : K) ≠ 0) (hβ0 : β ≠ 0)
    (hy0 : y0 ≠ 0) (f : Module.Basis (Fin 4) K V) {r : V} {φ : Module.Dual K V}
    (hφ : φ r = 2)
    (hr : (fun k => f.repr r k) = y0 • (![1, -2 * β, -1, 0] : Fin 4 → K))
    (hκ : (fun k => φ (f k)) = y0⁻¹ • ((2 : K)⁻¹ • (![1, -β⁻¹, -1, 0] : Fin 4 → K))) :
    LinearMap.toMatrix f f (Module.reflection hφ : V →ₗ[K] V) =
      Matrix.blockSucc (j34BlockMat β) := by
  have h3 : j34BlockMat β = 1 - (2 : K)⁻¹ • Matrix.vecMulVec (![1, -2 * β, -1] : Fin 3 → K)
      (![1, -β⁻¹, -1] : Fin 3 → K) := rj34_j34BlockMat_eq h2 hβ0
  have hv : (fun i : Fin 3 => ((2 : K)⁻¹ • (![1, -2 * β, -1, 0] : Fin 4 → K)) i.castSucc) =
      (2 : K)⁻¹ • (![1, -2 * β, -1] : Fin 3 → K) := by
    funext i; fin_cases i <;> rfl
  have hw : (fun i : Fin 3 => (![1, -β⁻¹, -1, 0] : Fin 4 → K) i.castSucc) =
      (![1, -β⁻¹, -1] : Fin 3 → K) := by
    funext i; fin_cases i <;> rfl
  rw [toMatrix_reflection f hφ, hr, hκ, Matrix.smul_vecMulVec, Matrix.vecMulVec_smul, smul_smul,
    mul_inv_cancel₀ hy0, one_smul, Matrix.vecMulVec_smul, ← Matrix.smul_vecMulVec,
    rj34_blockSucc_sub_vecMulVec ((2 : K)⁻¹ • (![1, -2 * β, -1, 0] : Fin 4 → K))
      (![1, -β⁻¹, -1, 0] : Fin 4 → K) (by simp) (by simp), hv, hw, Matrix.smul_vecMulVec, h3]

private theorem rj34_repr_self {n : ℕ} (f : Module.Basis (Fin n) K V) (i : Fin n) :
    (fun k => f.repr (f i) k) = Pi.single i 1 := by
  funext k
  rw [Module.Basis.repr_self]
  simp [Pi.single_apply, Finsupp.single_apply, eq_comm]

private theorem rj34_repr_smul_sub {n : ℕ} (f : Module.Basis (Fin n) K V) {i j : Fin n}
    (c : K) : (fun k => f.repr (c • (f i - f j)) k) =
      c • (Pi.single i 1 - Pi.single j 1) := by
  funext k
  rw [map_smul, map_sub, Finsupp.smul_apply, Finsupp.sub_apply, smul_eq_mul,
    congrFun (rj34_repr_self f i) k, congrFun (rj34_repr_self f j) k]
  simp [Pi.smul_apply, Pi.sub_apply, smul_eq_mul]

end Matrices

section RingArith

variable {R : Type} [CommRing R]

private theorem rj34_ring_neg_two_mul (x y : R) : -2 * x * y = y * (-2 * x) := by ring

end RingArith

section Generic

private theorem rj34_dual_sum {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) W)
    (φ : Module.Dual (ZMod p) W) (c : Fin n → ZMod p) :
    φ (∑ i, c i • f i) = ∑ i, c i * φ (f i) := by
  simp [map_sum, map_smul, smul_eq_mul]

private theorem rj34_dual_eq_of_basis {n : ℕ} (f : Module.Basis (Fin n) (ZMod p) W)
    (φ : Module.Dual (ZMod p) W) (g : Fin n → ZMod p) (hg : ∀ i, φ (f i) = g i) :
    φ = ∑ i, g i • f.coord i := by
  apply LinearMap.ext
  intro v
  have hv : v ∈ Submodule.span (ZMod p) (Set.range f) := by rw [f.span_eq]; trivial
  induction hv using Submodule.span_induction with
  | mem w hw =>
    obtain ⟨i, rfl⟩ := hw
    rw [hg i, LinearMap.sum_apply, Finset.sum_eq_single i]
    · simp [Module.Basis.coord_apply]
    · intro j _ hji; simp [Module.Basis.coord_apply, hji]
    · intro hi; simp at hi
  | zero => simp
  | add a b _ _ ha hb => rw [map_add, ha, hb]; simp only [map_add]
  | smul c a _ ha => rw [map_smul, ha]; simp only [map_smul]

private theorem rj34_coroot_diag {φ : Module.Dual (ZMod p) W}
    (f : Module.Basis (Fin 4) (ZMod p) W)
    (h0 : φ (f 0) = 2) (h1 : φ (f 1) = 0) (h2 : φ (f 2) = 0)
    (h3 : φ (f (Fin.last 3)) = 0) :
    (fun k => φ (f k)) = Pi.single (0 : Fin 4) 2 := by
  funext k
  induction k using Fin.lastCases with
  | last => simpa [Pi.single_apply] using h3
  | cast j =>
    fin_cases j
    · simpa [Pi.single_apply, Fin.castSucc_zero] using h0
    · simpa [Pi.single_apply, Fin.castSucc_one] using h1
    · simpa [Pi.single_apply] using h2

private theorem rj34_coroot_pij_01 {φ : Module.Dual (ZMod p) W}
    (f : Module.Basis (Fin 4) (ZMod p) W) (c : ZMod p)
    (h0 : φ (f 0) = c * (1 - 0)) (h1 : φ (f 1) = c * (0 - 1))
    (h2 : φ (f 2) = c * (0 - 0)) (h3 : φ (f (Fin.last 3)) = 0) :
    (fun k => φ (f k)) = c • (Pi.single (0 : Fin 4) 1 - Pi.single (1 : Fin 4) 1) := by
  funext k
  induction k using Fin.lastCases with
  | last => simpa [Pi.smul_apply, Pi.sub_apply, Pi.single_apply] using h3
  | cast j =>
    fin_cases j
    · simpa [Pi.smul_apply, Pi.sub_apply, Pi.single_apply, Fin.castSucc_zero] using h0
    · simpa [Pi.smul_apply, Pi.sub_apply, Pi.single_apply, Fin.castSucc_one] using h1
    · simpa [Pi.smul_apply, Pi.sub_apply, Pi.single_apply] using h2

private theorem rj34_coroot_pij_12 {φ : Module.Dual (ZMod p) W}
    (f : Module.Basis (Fin 4) (ZMod p) W) (c : ZMod p)
    (h0 : φ (f 0) = c * (0 - 0)) (h1 : φ (f 1) = c * (1 - 0))
    (h2 : φ (f 2) = c * (0 - 1)) (h3 : φ (f (Fin.last 3)) = 0) :
    (fun k => φ (f k)) = c • (Pi.single (1 : Fin 4) 1 - Pi.single (2 : Fin 4) 1) := by
  funext k
  induction k using Fin.lastCases with
  | last => simpa [Pi.smul_apply, Pi.sub_apply, Pi.single_apply] using h3
  | cast j =>
    fin_cases j
    · simpa [Pi.smul_apply, Pi.sub_apply, Pi.single_apply, Fin.castSucc_zero] using h0
    · simpa [Pi.smul_apply, Pi.sub_apply, Pi.single_apply, Fin.castSucc_one] using h1
    · simpa [Pi.smul_apply, Pi.sub_apply, Pi.single_apply] using h2

private theorem rj34_repr_last_eq_zero {X : Subgroup (W ≃ₗ[ZMod p] W)} (hX : SplitSupport X 3)
    {f : Module.Basis (Fin 4) (ZMod p) W}
    (hf : ∀ i : Fin 3, f i.castSucc ∈ HardMathSupport.Kantor79.commutatorSpace X)
    (hlast : f (Fin.last 3) ∈ centralizerSpace X) {r : W}
    (hr : r ∈ HardMathSupport.Kantor79.commutatorSpace X) : f.repr r (Fin.last 3) = 0 := by
  have hsum := f.sum_repr r
  rw [Fin.sum_univ_castSucc] at hsum
  have hmemV : (∑ i : Fin 3, f.repr r i.castSucc • f i.castSucc) ∈
      HardMathSupport.Kantor79.commutatorSpace X :=
    Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (hf i)
  have hmem : f.repr r (Fin.last 3) • f (Fin.last 3) ∈
      HardMathSupport.Kantor79.commutatorSpace X := by
    have heq : f.repr r (Fin.last 3) • f (Fin.last 3) =
        r - ∑ i : Fin 3, f.repr r i.castSucc • f i.castSucc := by
      rw [eq_sub_iff_add_eq, add_comm]; exact hsum
    rw [heq]; exact sub_mem hr hmemV
  have hmemC : f.repr r (Fin.last 3) • f (Fin.last 3) ∈ centralizerSpace X :=
    Submodule.smul_mem _ _ hlast
  have hzero : f.repr r (Fin.last 3) • f (Fin.last 3) = 0 := by
    have hmem0 : f.repr r (Fin.last 3) • f (Fin.last 3) ∈
        (⊥ : Submodule (ZMod p) W) :=
      hX.1.inf_eq_bot ▸ Submodule.mem_inf.mpr ⟨hmem, hmemC⟩
    simpa using hmem0
  exact (smul_eq_zero.mp hzero).resolve_right (f.ne_zero (Fin.last 3))

private noncomputable def rj34_toMatHom (f : Module.Basis (Fin 4) (ZMod p) W) :
    (W ≃ₗ[ZMod p] W) →* Matrix (Fin 4) (Fin 4) (ZMod p) where
  toFun g := LinearMap.toMatrix f f (g : W →ₗ[ZMod p] W)
  map_one' := by rw [LinearEquiv.coe_toLinearMap_one]; exact LinearMap.toMatrix_one f
  map_mul' g h := by rw [LinearEquiv.coe_toLinearMap_mul, LinearMap.toMatrix_mul]

end Generic

section FieldAlg

variable {K : Type} [Field K]

private theorem rj34_cross_of {y0 y1 x0 x1 : K}
    (hA : 2 * y0 * x0 = 1) (hB : x1 * y1 = 1) (hcross : (y0 - y1) * (x0 - x1) = 1) :
    2 * (y0 * x1 + y1 * x0) = 1 := by
  linear_combination (-2) * hcross + hA + (2) * hB

private theorem rj34_cross_eq {c y0 y1 x0 x1 : K} (hc : c ≠ 0)
    (h : (c * (y0 - y1)) * (c⁻¹ * (x0 - x1)) = 1) : (y0 - y1) * (x0 - x1) = 1 := by
  field_simp [hc] at h ⊢
  linear_combination h

private theorem rj34_beta_of {y0 y1 x0 x1 : K}
    (hy0 : y0 ≠ 0) (hA : 2 * y0 * x0 = 1) (hB : x1 * y1 = 1)
    (hC : 2 * (y0 * x1 + y1 * x0) = 1) :
    2 * (-(2 * y0)⁻¹ * y1) ^ 2 + (-(2 * y0)⁻¹ * y1) + 1 = 0 := by
  have h2 : (2 : K) ≠ 0 := by
    intro h; rw [h, zero_mul, zero_mul] at hA; exact one_ne_zero hA.symm
  field_simp [hy0, h2] at hA hB hC ⊢
  linear_combination (y0 * y1) * hC - (2 * y0 ^ 2) * hB - (y1 ^ 2) * hA

private theorem rj34_y1_of_sum' {y0 y1 y2 x0 x1 x2 : K}
    (hA : 2 * y0 * x0 = 1) (hx2 : x2 = -x0) (hy2 : y2 = -y0)
    (hsum : x0 * y0 + x1 * y1 + x2 * y2 = 2) : x1 * y1 = 1 := by
  rw [hx2, hy2] at hsum
  linear_combination hsum - hA

private theorem rj34_x0_of {y0 x0 : K} (hA : 2 * y0 * x0 = 1) : x0 = (2 * y0)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  linear_combination hA

private theorem rj34_x1_of {y1 x1 : K} (hB : x1 * y1 = 1) : x1 = (y1)⁻¹ := by
  apply eq_inv_of_mul_eq_one_right
  linear_combination hB

private theorem rj34_y1_of_beta {y0 y1 : K} (hy0 : y0 ≠ 0) (h2 : (2 : K) ≠ 0) :
    -2 * (-(2 * y0)⁻¹ * y1) * y0 = y1 := by
  field_simp [hy0, h2]

private theorem rj34_x0_eq {y0 : K} (hy0 : y0 ≠ 0) (h2 : (2 : K) ≠ 0) :
    (2 * y0)⁻¹ = y0⁻¹ * 2⁻¹ := by
  field_simp [hy0, h2]

private theorem rj34_x2_eq {y0 : K} (hy0 : y0 ≠ 0) (h2 : (2 : K) ≠ 0) :
    -(2 * y0)⁻¹ = y0⁻¹ * (2⁻¹ * (-1)) := by
  field_simp [hy0, h2]

private theorem rj34_x1_eq {y0 y1 β : K} (hy0 : y0 ≠ 0) (hβ0 : β ≠ 0) (h2 : (2 : K) ≠ 0)
    (hy1 : y1 = -2 * β * y0) : y1⁻¹ = y0⁻¹ * (2⁻¹ * (-β⁻¹)) := by
  rw [hy1]; field_simp [hy0, hβ0, h2]

end FieldAlg

section Sums

private theorem rj34_sum_single2_single1 :
    (∑ i : Fin 4, (Pi.single (0 : Fin 4) (2 : ZMod p) : Fin 4 → ZMod p) i *
      ((Pi.single (0 : Fin 4) (1 : ZMod p) : Fin 4 → ZMod p)) i) = 2 := by
  simp [Pi.single_apply]

private theorem rj34_sum_u4_sq :
    (∑ i : Fin 4, (![1, 0, 1, 0] : Fin 4 → ZMod p) i * ![1, 0, 1, 0] i) = 2 := by
  simp [Fin.sum_univ_four]; norm_num

private theorem rj34_sum_single2_u4 :
    (∑ i : Fin 4, (Pi.single (0 : Fin 4) (2 : ZMod p) : Fin 4 → ZMod p) i *
      (![1, 0, 1, 0] : Fin 4 → ZMod p) i) = 2 := by
  simp [Pi.single_apply]

private theorem rj34_sum_u4_single1 :
    (∑ i : Fin 4, (![1, 0, 1, 0] : Fin 4 → ZMod p) i *
      (Pi.single (0 : Fin 4) (1 : ZMod p) : Fin 4 → ZMod p) i) = 1 := by
  simp [Pi.single_apply]

private theorem rj34_sum_u4_smul_f (f : Module.Basis (Fin 4) (ZMod p) W) :
    (∑ i : Fin 4, (![1, 0, 1, 0] : Fin 4 → ZMod p) i • f i) = f 0 + f 2 := by
  simp [Fin.sum_univ_four]

private theorem rj34_sum_u4_coord_apply (f : Module.Basis (Fin 4) (ZMod p) W) (r : W) :
    (∑ i : Fin 4, (![1, 0, 1, 0] : Fin 4 → ZMod p) i • f.coord i) r =
      f.repr r 0 + f.repr r 2 := by
  simp [Module.Basis.coord_apply, Fin.sum_univ_four]

end Sums

variable [Module.Finite (ZMod p) W]

omit [Module.Finite (ZMod p) W] in
@[instance_reducible]
private noncomputable def rj34_fintype_X (f : Module.Basis (Fin 4) (ZMod p) W)
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

omit [Module.Finite (ZMod p) W] in
private theorem rj34_t_word {s0 s1 s2 a : W ≃ₗ[ZMod p] W}
    (hcomm : Commute a (s2 * s1 * s0 * (s2 * s1)⁻¹ * (s1 * s2 * s1) *
      (s2 * s1 * s0 * (s2 * s1)⁻¹)⁻¹))
    (h12 : orderOf (s1 * s2) = 3) (hs0r : IsRefl p s0) (hs1r : IsRefl p s1)
    (hs2r : IsRefl p s2) :
    ∃ t : W ≃ₗ[ZMod p] W, Commute a t ∧
      t = (s2 * s1 * s0 * (s2 * s1) ^ 2) * (s1 * s2 * s1) *
        (s2 * s1 * s0 * (s2 * s1) ^ 2) := by
  let w : W ≃ₗ[ZMod p] W := s2 * s1
  let σ : W ≃ₗ[ZMod p] W := w * s0 * w⁻¹
  let τ : W ≃ₗ[ZMod p] W := s1 * s2 * s1
  let t : W ≃ₗ[ZMod p] W := σ * τ * σ⁻¹
  have hcommt : Commute a t := hcomm
  have hw3 : w ^ 3 = 1 := by
    have hord : orderOf w = 3 := by
      have hw_inv : w = (s1 * s2)⁻¹ := by
        dsimp only [w]
        rw [mul_inv_rev, inv_eq_of_mul_eq_one_right hs2r.1, inv_eq_of_mul_eq_one_right hs1r.1]
      rw [hw_inv, orderOf_inv]; exact h12
    rw [← hord]; exact pow_orderOf_eq_one w
  have hwinv : w⁻¹ = w ^ 2 := by
    have h : w * w ^ 2 = 1 := by rw [← pow_succ', hw3]
    exact inv_eq_of_mul_eq_one_right h
  have hσeq : σ = w * s0 * w ^ 2 := by dsimp only [σ]; rw [hwinv]
  have hσsq : σ * σ = 1 := by
    rw [hσeq]
    calc (w * s0 * w ^ 2) * (w * s0 * w ^ 2)
        = w * s0 * (w ^ 2 * w) * s0 * w ^ 2 := by group
      _ = w * s0 * w ^ 3 * s0 * w ^ 2 := by rw [← pow_succ w 2]
      _ = w * (s0 * s0) * w ^ 2 := by rw [hw3]; group
      _ = w * w ^ 2 := by rw [hs0r.1]; group
      _ = w ^ 3 := by rw [← pow_succ' w 2]
      _ = 1 := hw3
  have hσinv : σ⁻¹ = σ := inv_eq_of_mul_eq_one_right hσsq
  have hword : t = (s2 * s1 * s0 * (s2 * s1) ^ 2) * (s1 * s2 * s1) *
      (s2 * s1 * s0 * (s2 * s1) ^ 2) := by
    rw [show t = (w * s0 * w ^ 2) * τ * (w * s0 * w ^ 2) from by
      dsimp only [t]; rw [hσinv, hσeq]]
  exact ⟨t, hcommt, hword⟩

omit [Module.Finite (ZMod p) W] in
private theorem rj34_t_matrix {f : Module.Basis (Fin 4) (ZMod p) W} {s0 s1 s2 t : W ≃ₗ[ZMod p] W}
    (hs0mat : LinearMap.toMatrix f f (s0 : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (diagSignMat (0 : Fin 3)))
    (hs1mat : LinearMap.toMatrix f f (s1 : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (pijMat (0 : Fin 3) 1 1))
    (hs2mat : LinearMap.toMatrix f f (s2 : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (pijMat (1 : Fin 3) 2 1))
    (hword : t = (s2 * s1 * s0 * (s2 * s1) ^ 2) * (s1 * s2 * s1) *
      (s2 * s1 * s0 * (s2 * s1) ^ 2)) :
    LinearMap.toMatrix f f (t : W →ₗ[ZMod p] W) =
      1 - Matrix.vecMulVec (![1, 0, 1, 0] : Fin 4 → ZMod p) ![1, 0, 1, 0] := by
  have hS0' : rj34_toMatHom f s0 =
      Matrix.blockSuccMonoidHom (ZMod p) 3 (diagSignMat (0 : Fin 3)) := by
    show LinearMap.toMatrix f f (s0 : W →ₗ[ZMod p] W) = _
    rw [hs0mat, Matrix.blockSuccMonoidHom_apply]
  have hS1' : rj34_toMatHom f s1 =
      Matrix.blockSuccMonoidHom (ZMod p) 3 (pijMat (0 : Fin 3) 1 1) := by
    show LinearMap.toMatrix f f (s1 : W →ₗ[ZMod p] W) = _
    rw [hs1mat, Matrix.blockSuccMonoidHom_apply]
  have hS2' : rj34_toMatHom f s2 =
      Matrix.blockSuccMonoidHom (ZMod p) 3 (pijMat (1 : Fin 3) 2 1) := by
    show LinearMap.toMatrix f f (s2 : W →ₗ[ZMod p] W) = _
    rw [hs2mat, Matrix.blockSuccMonoidHom_apply]
  have hMhom : Matrix.blockSuccMonoidHom (ZMod p) 3
      ((1 : Matrix (Fin 3) (Fin 3) (ZMod p)) -
        Matrix.vecMulVec (![1, 0, 1] : Fin 3 → ZMod p) ![1, 0, 1]) =
      1 - Matrix.vecMulVec (![1, 0, 1, 0] : Fin 4 → ZMod p) ![1, 0, 1, 0] := by
    rw [Matrix.blockSuccMonoidHom_apply, rj34_blockSucc_vecMulVec_one_zero_one]
  show rj34_toMatHom f t = _
  rw [← hMhom, ← rj34_word_matrix, hword]
  simp only [map_mul, map_pow, hS0', hS1', hS2']

omit [Module.Finite (ZMod p) W] in
private theorem rj34_t_relations (hp : p ≠ 2) {f : Module.Basis (Fin 4) (ZMod p) W}
    {s0 t a : W ≃ₗ[ZMod p] W} {r : W} {ψ : Module.Dual (ZMod p) W}
    (hψ : ψ r = 2) (haeq : a = Module.reflection hψ) (h0a : orderOf (s0 * a) = 3)
    (hcommt : Commute a t)
    (hs0mat : LinearMap.toMatrix f f (s0 : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (diagSignMat (0 : Fin 3)))
    (htmat : LinearMap.toMatrix f f (t : W →ₗ[ZMod p] W) =
      1 - Matrix.vecMulVec (![1, 0, 1, 0] : Fin 4 → ZMod p) ![1, 0, 1, 0]) :
    ψ (f 2) = -ψ (f 0) ∧ f.repr r 2 = -f.repr r 0 := by
  have hs0t4 : orderOf (s0 * t) = 4 := by
    refine FFourCoord.orderOf_mul_eq_four_of_toMatrix (p := p) hp f
      (x := s0) (r := t) (v := Pi.single (0 : Fin 4) (1 : ZMod p))
      (w := Pi.single (0 : Fin 4) (2 : ZMod p))
      (ρ := ![1, 0, 1, 0]) (κ := ![1, 0, 1, 0]) ?_ ?_ htmat ?_ ?_
    · rw [hs0mat, blockSucc_diagSignMat]
      exact diagSignMat_eq_one_sub_vecMulVec (0 : Fin 4)
    · exact rj34_sum_single2_single1
    · exact rj34_sum_u4_sq
    · rw [rj34_sum_single2_u4, rj34_sum_u4_single1]; norm_num
  obtain ⟨hρt, ht_refl⟩ := FFourCoord.eq_reflection_of_toMatrix f htmat rj34_sum_u4_sq
  have hne_at : a ≠ t := by
    intro h; rw [h] at h0a; omega
  have hne : Module.reflection hψ ≠ Module.reflection hρt := by
    intro h; exact hne_at (by rw [haeq, ht_refl, h])
  have hcommr : Commute (Module.reflection hψ) (Module.reflection hρt) := by
    rw [← haeq, ← ht_refl]; exact hcommt
  have hψrt : ψ (∑ i : Fin 4, (![1, 0, 1, 0] : Fin 4 → ZMod p) i • f i) = 0 :=
    apply_eq_zero_of_commute hp hψ hρt hcommr hne
  have hφtr : (∑ i : Fin 4, (![1, 0, 1, 0] : Fin 4 → ZMod p) i • f.coord i) r = 0 :=
    apply_eq_zero_of_commute hp hρt hψ hcommr.symm hne.symm
  have hx2 : ψ (f 2) = -ψ (f 0) := by
    have h := hψrt
    rw [rj34_sum_u4_smul_f f, map_add] at h
    exact eq_neg_iff_add_eq_zero.mpr ((add_comm (ψ (f 2)) (ψ (f 0))).trans h)
  have hy2 : f.repr r 2 = -f.repr r 0 := by
    have h := hφtr
    rw [rj34_sum_u4_coord_apply f r] at h
    exact eq_neg_iff_add_eq_zero.mpr
      ((add_comm ((f.repr r) 2) ((f.repr r) 0)).trans h)
  exact ⟨hx2, hy2⟩

omit [Module.Finite (ZMod p) W] in
private theorem rj34_scalars_phi0 {f : Module.Basis (Fin 4) (ZMod p) W} {r : W}
    {φ0 : Module.Dual (ZMod p) W}
    (hκ0 : (fun k => φ0 (f k)) = Pi.single (0 : Fin 4) 2) :
    φ0 r = 2 * f.repr r 0 := by
  have h := rj34_dual_eq_of_basis f φ0 (Pi.single (0 : Fin 4) 2) (fun i => congrFun hκ0 i)
  rw [h, Fin.sum_univ_four]
  simp [LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]

omit [Module.Finite (ZMod p) W] in
private theorem rj34_scalars_phi1 {f : Module.Basis (Fin 4) (ZMod p) W} {r0 r : W}
    {φ1 : Module.Dual (ZMod p) W}
    (hκ1 : (fun k => φ1 (f k)) = φ1 r0 • (Pi.single (0 : Fin 4) 1 - Pi.single (1 : Fin 4) 1)) :
    φ1 r = φ1 r0 * (f.repr r 0 - f.repr r 1) := by
  have h := rj34_dual_eq_of_basis f φ1
    (φ1 r0 • (Pi.single (0 : Fin 4) 1 - Pi.single (1 : Fin 4) 1))
    (fun i => congrFun hκ1 i)
  conv_lhs => rw [h]
  rw [Fin.sum_univ_four]
  simp [Pi.smul_apply, Pi.sub_apply,
    LinearMap.smul_apply, Module.Basis.coord_apply, smul_eq_mul]
  ring_nf

omit [Module.Finite (ZMod p) W] in
private theorem rj34_scalars_psi1 {f : Module.Basis (Fin 4) (ZMod p) W} {r0 r1 e0 e1 : W}
    {φ1 ψ : Module.Dual (ZMod p) W}
    (hre1 : e0 - e1 = φ1 r0 • r1) (ha10ne : φ1 r0 ≠ 0)
    (hf0 : f 0 = e0) (hf1 : f 1 = e1) :
    ψ r1 = (φ1 r0)⁻¹ * (ψ (f 0) - ψ (f 1)) := by
  have hre : r1 = (φ1 r0)⁻¹ • (e0 - e1) := by
    rw [hre1, smul_smul, inv_mul_cancel₀ ha10ne, one_smul]
  rw [hre, map_smul, map_sub, smul_eq_mul, show e0 = f 0 from hf0.symm,
    show e1 = f 1 from hf1.symm]

omit [Module.Finite (ZMod p) W] in
private theorem rj34_scalars (hp : p ≠ 2) {f : Module.Basis (Fin 4) (ZMod p) W}
    {r0 r1 r : W} {φ0 φ1 ψ : Module.Dual (ZMod p) W} {s0 s1 a : W ≃ₗ[ZMod p] W} {e0 e1 : W}
    (hκ0 : (fun k => φ0 (f k)) = Pi.single (0 : Fin 4) 2)
    (hκ1 : (fun k => φ1 (f k)) = φ1 r0 • (Pi.single (0 : Fin 4) 1 - Pi.single (1 : Fin 4) 1))
    (hψ : ψ r = 2) (haeq : a = Module.reflection hψ)
    (hφ0 : φ0 r0 = 2) (hφ1 : φ1 r1 = 2)
    (hs0eq : s0 = Module.reflection hφ0) (hs1eq : s1 = Module.reflection hφ1)
    (h0a : orderOf (s0 * a) = 3) (h1a : orderOf (s1 * a) = 3)
    (ha10ne : φ1 r0 ≠ 0) (hre1 : e0 - e1 = φ1 r0 • r1) (he0 : e0 = r0)
    (hf0 : f 0 = e0) (hf1 : f 1 = e1) (hr_last : f.repr r 3 = 0) :
    2 * f.repr r 0 * ψ (f 0) = 1 ∧
      (ψ (f 0) * f.repr r 0 + ψ (f 1) * f.repr r 1 + ψ (f 2) * f.repr r 2 = 2) ∧
      (f.repr r 0 - f.repr r 1) * (ψ (f 0) - ψ (f 1)) = 1 ∧
      f.repr r 0 ≠ 0 := by
  have hφ0r : φ0 r = 2 * f.repr r 0 := rj34_scalars_phi0 hκ0
  have hφ1r : φ1 r = φ1 r0 * (f.repr r 0 - f.repr r 1) := rj34_scalars_phi1 hκ1
  have hψr1 : ψ r1 = (φ1 r0)⁻¹ * (ψ (f 0) - ψ (f 1)) := rj34_scalars_psi1 hre1 ha10ne hf0 hf1
  have h2xy : 2 * f.repr r 0 * ψ (f 0) = 1 := by
    have h := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφ0 hψ
      (by rw [← hs0eq, ← haeq]; exact h0a)
    rw [he0.symm.trans hf0.symm] at h
    rwa [hφ0r] at h
  have hsum : ψ (f 0) * f.repr r 0 + ψ (f 1) * f.repr r 1 +
      ψ (f 2) * f.repr r 2 = 2 := by
    have h := hψ
    rw [← f.sum_repr r, rj34_dual_sum] at h
    rw [Fin.sum_univ_castSucc, show f.repr r (Fin.last 3) = 0 from hr_last, zero_mul,
      add_zero, Fin.sum_univ_three] at h
    rw [Fin.castSucc_zero, Fin.castSucc_one,
      show (Fin.castSucc (2 : Fin 3) : Fin 4) = 2 from rfl] at h
    simpa only [mul_comm] using h
  have hcross : (f.repr r 0 - f.repr r 1) * (ψ (f 0) - ψ (f 1)) = 1 := by
    have h := apply_mul_apply_eq_one_of_orderOf_eq_three hp hφ1 hψ
      (by rw [← hs1eq, ← haeq]; exact h1a)
    rw [hφ1r, hψr1] at h
    exact rj34_cross_eq ha10ne h
  have hy0ne : f.repr r 0 ≠ 0 := by
    intro h; rw [h, mul_zero, zero_mul] at h2xy; exact one_ne_zero h2xy.symm
  exact ⟨h2xy, hsum, hcross, hy0ne⟩

omit [Module.Finite (ZMod p) W] in
private theorem rj34_beta {f : Module.Basis (Fin 4) (ZMod p) W} {r : W}
    {ψ : Module.Dual (ZMod p) W}
    (h2xy : 2 * f.repr r 0 * ψ (f 0) = 1)
    (hsum : ψ (f 0) * f.repr r 0 + ψ (f 1) * f.repr r 1 + ψ (f 2) * f.repr r 2 = 2)
    (hcross : (f.repr r 0 - f.repr r 1) * (ψ (f 0) - ψ (f 1)) = 1)
    (hx2 : ψ (f 2) = -ψ (f 0)) (hy2 : f.repr r 2 = -f.repr r 0)
    (h2ne : (2 : ZMod p) ≠ 0) :
    ∃ β : ZMod p, 2 * β ^ 2 + β + 1 = 0 ∧ β ≠ 0 ∧ f.repr r 0 ≠ 0 ∧
      f.repr r 1 = -2 * β * f.repr r 0 ∧ ψ (f 0) = (2 * f.repr r 0)⁻¹ ∧
      ψ (f 1) = (f.repr r 1)⁻¹ := by
  have hy0ne : f.repr r 0 ≠ 0 := by
    intro h; rw [h, mul_zero, zero_mul] at h2xy; exact one_ne_zero h2xy.symm
  have hB : ψ (f 1) * f.repr r 1 = 1 := rj34_y1_of_sum' h2xy hx2 hy2 hsum
  have hC : 2 * (f.repr r 0 * ψ (f 1) + f.repr r 1 * ψ (f 0)) = 1 :=
    rj34_cross_of h2xy hB hcross
  let β : ZMod p := -(2 * f.repr r 0)⁻¹ * f.repr r 1
  have hβ : 2 * β ^ 2 + β + 1 = 0 := by
    dsimp only [β]
    exact rj34_beta_of hy0ne h2xy hB hC
  have hβ0 : β ≠ 0 := by
    intro h; rw [h] at hβ; norm_num at hβ
  have hy1eq : f.repr r 1 = -2 * β * f.repr r 0 := by
    dsimp only [β]
    exact (rj34_y1_of_beta (K := ZMod p) hy0ne h2ne).symm
  exact ⟨β, hβ, hβ0, hy0ne, hy1eq, rj34_x0_of h2xy, rj34_x1_of hB⟩

omit [Module.Finite (ZMod p) W] in
private theorem rj34_coords {f : Module.Basis (Fin 4) (ZMod p) W} {r : W}
    {ψ : Module.Dual (ZMod p) W} {β : ZMod p}
    (h2ne : (2 : ZMod p) ≠ 0) (hy0ne : f.repr r 0 ≠ 0) (hβ0 : β ≠ 0)
    (hy1eq : f.repr r 1 = -2 * β * f.repr r 0) (hy2 : f.repr r 2 = -f.repr r 0)
    (hx0' : ψ (f 0) = (2 * f.repr r 0)⁻¹) (hx1' : ψ (f 1) = (f.repr r 1)⁻¹)
    (hx2 : ψ (f 2) = -ψ (f 0)) (hψw : ψ (f 3) = 0) (hr_last : f.repr r 3 = 0) :
    (fun k => f.repr r k) = f.repr r 0 • (![1, -2 * β, -1, 0] : Fin 4 → ZMod p) ∧
      (fun k => ψ (f k)) = (f.repr r 0)⁻¹ •
        ((2 : ZMod p)⁻¹ • (![1, -β⁻¹, -1, 0] : Fin 4 → ZMod p)) := by
  have hr : (fun k => f.repr r k) =
      f.repr r 0 • (![1, -2 * β, -1, 0] : Fin 4 → ZMod p) := by
    funext k
    fin_cases k
    · simp [Pi.smul_apply]
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact hy1eq.trans (rj34_ring_neg_two_mul β (f.repr r 0))
    · simp only [Pi.smul_apply, smul_eq_mul]
      exact hy2.trans ((mul_neg_one (f.repr r 0)).symm)
    · simpa [Pi.smul_apply] using hr_last
  have hκ : (fun k => ψ (f k)) = (f.repr r 0)⁻¹ • ((2 : ZMod p)⁻¹ •
      (![1, -β⁻¹, -1, 0] : Fin 4 → ZMod p)) := by
    funext k
    fin_cases k
    · change ψ (f (0 : Fin 4)) =
        ((f.repr r 0)⁻¹ • ((2 : ZMod p)⁻¹ • ![1, -β⁻¹, -1, 0])) (0 : Fin 4)
      rw [hx0']
      simp only [Pi.smul_apply, Matrix.cons_val_zero, mul_one, smul_eq_mul]
      exact rj34_x0_eq hy0ne h2ne
    · change ψ (f (1 : Fin 4)) = _
      rw [hx1']; exact rj34_x1_eq hy0ne hβ0 h2ne hy1eq
    · change ψ (f (2 : Fin 4)) =
        ((f.repr r 0)⁻¹ • ((2 : ZMod p)⁻¹ • ![1, -β⁻¹, -1, 0])) (2 : Fin 4)
      rw [hx2, hx0']
      simp only [Pi.smul_apply, Matrix.cons_val, smul_eq_mul]
      exact rj34_x2_eq hy0ne h2ne
    · simpa [Pi.smul_apply] using hψw
  exact ⟨hr, hκ⟩

omit [Module.Finite (ZMod p) W] in
private theorem rj34_final (hp : p ≠ 2) {X : Subgroup (W ≃ₗ[ZMod p] W)}
    (hcard : Nat.card X = 336) {f : Module.Basis (Fin 4) (ZMod p) W}
    {s0 s1 s2 a : W ≃ₗ[ZMod p] W} {r : W} {ψ : Module.Dual (ZMod p) W} {β : ZMod p}
    (h2ne : (2 : ZMod p) ≠ 0) (hβ : 2 * β ^ 2 + β + 1 = 0) (hs0X : s0 ∈ X) (hs1X : s1 ∈ X)
    (hs2X : s2 ∈ X) (haX : a ∈ X) (hψ : ψ r = 2) (haeq : a = Module.reflection hψ)
    (hs0mat : LinearMap.toMatrix f f (s0 : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (diagSignMat (0 : Fin 3)))
    (hs1mat : LinearMap.toMatrix f f (s1 : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (pijMat (0 : Fin 3) 1 1))
    (hs2mat : LinearMap.toMatrix f f (s2 : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (pijMat (1 : Fin 3) 2 1))
    (hr : (fun k => f.repr r k) = f.repr r 0 • (![1, -2 * β, -1, 0] : Fin 4 → ZMod p))
    (hκ : (fun k => ψ (f k)) = (f.repr r 0)⁻¹ •
      ((2 : ZMod p)⁻¹ • (![1, -β⁻¹, -1, 0] : Fin 4 → ZMod p)))
    (hy0ne : f.repr r 0 ≠ 0) (hβ0 : β ≠ 0) :
    X = basisClosure f (j34Mats β) := by
  have hmat_a : LinearMap.toMatrix f f (Module.reflection hψ : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (j34BlockMat β) :=
    rj34_toMatrix_j34BlockMat h2ne hβ0 hy0ne f hψ hr hκ
  have hmat_a' : LinearMap.toMatrix f f (a : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (j34BlockMat β) := by rw [haeq]; exact hmat_a
  have hle : basisClosure f (j34Mats β) ≤ X := by
    rw [basisClosure, Subgroup.closure_le]
    rintro g hg
    rw [j34Mats] at hg
    rcases hg with ⟨M, hM, hMto⟩
    rw [j34BlockMats] at hM
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hM
    rcases hM with rfl | rfl | rfl | rfl
    · exact (eq_of_toMatrix_eq f (by rw [← hMto, ← hs0mat]) : g = s0) ▸ hs0X
    · exact (eq_of_toMatrix_eq f (by rw [← hMto, ← hs1mat]) : g = s1) ▸ hs1X
    · exact (eq_of_toMatrix_eq f (by rw [← hMto, ← hs2mat]) : g = s2) ▸ hs2X
    · exact (eq_of_toMatrix_eq f (by rw [← hMto, ← hmat_a']) : g = a) ▸ haX
  have hcard' : Nat.card (basisClosure f (j34Mats β)) = 336 :=
    PrimModel.card_basisClosure_j34Mats hp f hβ
  exact (@Subgroup.eq_of_le_of_card_ge (W ≃ₗ[ZMod p] W) _ (basisClosure f (j34Mats β)) X
    (rj34_fintype_X f X).finite hle (by rw [hcard', hcard])).symm

omit [Module.Finite (ZMod p) W] in
private theorem rj34_pair_data {r0 r1 r2 e0 e1 e2 : W}
    {φ0 φ1 φ2 : Module.Dual (ZMod p) W}
    (he0 : e0 = r0) (he1 : e1 = r0 - φ1 r0 • r1) (he2 : e2 = e1 - φ2 e1 • r2)
    (hφ0 : φ0 r0 = 2) (hφ1 : φ1 r1 = 2) (hφ2 : φ2 r2 = 2)
    (h02 : φ0 r2 = 0 ∧ φ2 r0 = 0) (h12 : φ1 r2 * φ2 r1 = 1)
    (h01 : φ0 r1 * φ1 r0 = 2) (ha10ne : φ1 r0 ≠ 0) (hφ2r1ne : φ2 r1 ≠ 0) :
    φ0 e0 = 2 ∧ φ1 e0 = φ1 r0 ∧ φ2 e0 = 0 ∧
      φ0 e1 = 0 ∧ φ1 e1 = -φ1 r0 ∧ φ2 e1 = -φ1 r0 * φ2 r1 ∧
      φ0 e2 = 0 ∧ φ1 e2 = 0 ∧ φ2 e2 = -φ2 e1 ∧
      φ2 e1 ≠ 0 ∧ -φ1 r0 * φ2 r1 ≠ 0 := by
  have hφ0e0 : φ0 e0 = 2 := by rw [he0]; exact hφ0
  have hφ1e0 : φ1 e0 = φ1 r0 := by rw [he0]
  have hφ2e0 : φ2 e0 = 0 := by rw [he0]; exact h02.2
  have hφ0e1 : φ0 e1 = 0 := by
    rw [he1, map_sub, map_smul, hφ0, smul_eq_mul, mul_comm (φ1 r0) (φ0 r1), h01]
    exact sub_self 2
  have hφ1e1 : φ1 e1 = -φ1 r0 := by
    rw [he1, map_sub, map_smul, hφ1, smul_eq_mul]
    exact by ring
  have hφ2e1 : φ2 e1 = -φ1 r0 * φ2 r1 := by
    rw [he1, map_sub, map_smul, h02.2, smul_eq_mul]
    exact by ring
  have hφ0e2 : φ0 e2 = 0 := by
    rw [he2, map_sub, map_smul, hφ0e1, h02.1, smul_eq_mul, mul_zero]
    exact sub_self 0
  have hφ1e2 : φ1 e2 = 0 := by
    rw [he2, map_sub, map_smul, hφ1e1, hφ2e1, smul_eq_mul, mul_assoc,
      mul_comm (φ2 r1) (φ1 r2), h12, mul_one]
    exact sub_self (-φ1 r0)
  have hφ2e2 : φ2 e2 = -φ2 e1 := by
    rw [he2, map_sub, map_smul, hφ2, smul_eq_mul]
    exact by ring
  have hcne : φ2 e1 ≠ 0 := by
    rw [hφ2e1]; exact mul_ne_zero (neg_ne_zero.mpr ha10ne) hφ2r1ne
  have hcne' : -φ1 r0 * φ2 r1 ≠ 0 := by rw [← hφ2e1]; exact hcne
  exact ⟨hφ0e0, hφ1e0, hφ2e0, hφ0e1, hφ1e1, hφ2e1, hφ0e2, hφ1e2, hφ2e2, hcne, hcne'⟩
private theorem rj34_setup (hp : p ≠ 2) {X : Subgroup (W ≃ₗ[ZMod p] W)} (hF : J34Frame p X) :
    ∃ (s0 s1 s2 a : W ≃ₗ[ZMod p] W) (r0 r1 r2 r : W) (φ0 φ1 φ2 ψ : Module.Dual (ZMod p) W)
      (hφ0 : φ0 r0 = 2) (hφ1 : φ1 r1 = 2) (hφ2 : φ2 r2 = 2) (hψ : ψ r = 2),
      s0 ∈ X ∧ s1 ∈ X ∧ s2 ∈ X ∧ a ∈ X ∧ s0 = Module.reflection hφ0 ∧
      s1 = Module.reflection hφ1 ∧ s2 = Module.reflection hφ2 ∧ a = Module.reflection hψ ∧
      φ0 r2 = 0 ∧ φ2 r0 = 0 ∧ φ1 r2 * φ2 r1 = 1 ∧ φ0 r1 * φ1 r0 = 2 ∧
      φ1 r0 ≠ 0 ∧ φ2 r1 ≠ 0 ∧
      r0 ∈ HardMathSupport.Kantor79.commutatorSpace X ∧
      r1 ∈ HardMathSupport.Kantor79.commutatorSpace X ∧
      r2 ∈ HardMathSupport.Kantor79.commutatorSpace X ∧
      IsRefl p s0 ∧ IsRefl p s1 ∧ IsRefl p s2 ∧
      orderOf (s0 * a) = 3 ∧ orderOf (s1 * a) = 3 ∧ orderOf (s1 * s2) = 3 ∧
      Commute a (s2 * s1 * s0 * (s2 * s1)⁻¹ * (s1 * s2 * s1) *
        (s2 * s1 * s0 * (s2 * s1)⁻¹)⁻¹) := by
  obtain ⟨s0, hs0X, s1, hs1X, s2, hs2X, a, haX, hs0r, hs1r, hs2r, har,
    h01, h12, h02, h0a, h1a, hcomm⟩ := hF
  obtain ⟨r0, φ0, hφ0, hs0eq⟩ := (isRefl_iff hp s0).mp hs0r
  obtain ⟨r1, φ1, hφ1, hs1eq⟩ := (isRefl_iff hp s1).mp hs1r
  obtain ⟨r2, φ2, hφ2, hs2eq⟩ := (isRefl_iff hp s2).mp hs2r
  obtain ⟨r, ψ, hψ, haeq⟩ := (isRefl_iff hp a).mp har
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hs0X' : Module.reflection hφ0 ∈ X := by rw [← hs0eq]; exact hs0X
  have hs1X' : Module.reflection hφ1 ∈ X := by rw [← hs1eq]; exact hs1X
  have hs2X' : Module.reflection hφ2 ∈ X := by rw [← hs2eq]; exact hs2X
  have h02' := eq_zero_of_orderOf_eq_two hp hφ0 hφ2 (by rw [← hs0eq, ← hs2eq]; exact h02)
  have h12' : φ1 r2 * φ2 r1 = 1 :=
    apply_mul_apply_eq_one_of_orderOf_eq_three hp hφ1 hφ2 (by rw [← hs1eq, ← hs2eq]; exact h12)
  have h01' : φ0 r1 * φ1 r0 = 2 :=
    apply_mul_apply_eq_two_of_orderOf_eq_four hp hφ0 hφ1 (by rw [← hs0eq, ← hs1eq]; exact h01)
  have hφ2r1ne : φ2 r1 ≠ 0 := fun h => by rw [h, mul_zero] at h12'; exact one_ne_zero h12'.symm
  have ha10ne : φ1 r0 ≠ 0 := fun h => by rw [h, mul_zero] at h01'; exact h2ne h01'.symm
  have hr0V := mem_commutatorSpace_of_reflection_mem hp hφ0 hs0X'
  have hr1V := mem_commutatorSpace_of_reflection_mem hp hφ1 hs1X'
  have hr2V := mem_commutatorSpace_of_reflection_mem hp hφ2 hs2X'
  exact ⟨s0, s1, s2, a, r0, r1, r2, r, φ0, φ1, φ2, ψ, hφ0, hφ1, hφ2, hψ,
    hs0X, hs1X, hs2X, haX, hs0eq, hs1eq, hs2eq, haeq, h02'.1, h02'.2, h12', h01',
    ha10ne, hφ2r1ne, hr0V, hr1V, hr2V, hs0r, hs1r, hs2r, h0a, h1a, h12, hcomm⟩

omit [Module.Finite (ZMod p) W] in
private theorem rj34_li {e0 e1 e2 : W} {φ0 φ1 φ2 : Module.Dual (ZMod p) W} {c d : ZMod p}
    (hφ0e0 : φ0 e0 = 2) (hφ0e1 : φ0 e1 = 0) (hφ0e2 : φ0 e2 = 0)
    (hφ1e0 : φ1 e0 = c) (hφ1e1 : φ1 e1 = -c) (hφ1e2 : φ1 e2 = 0)
    (hφ2e0 : φ2 e0 = 0) (hφ2e1 : φ2 e1 = d) (hφ2e2 : φ2 e2 = -φ2 e1)
    (h2ne : (2 : ZMod p) ≠ 0) (hc : c ≠ 0) (hd : d ≠ 0) :
    LinearIndependent (ZMod p) ![e0, e1, e2] := by
  let v : Fin 3 → W := ![e0, e1, e2]
  have hv : LinearIndependent (ZMod p) v := by
    rw [Fintype.linearIndependent_iff]
    intro g hg
    have h0 := congrArg φ0 hg
    have h1 := congrArg φ1 hg
    have h2 := congrArg φ2 hg
    simp only [map_add, map_smul, smul_eq_mul, map_zero, Fin.sum_univ_three,
      show v 0 = e0 from rfl, show v 1 = e1 from rfl, show v 2 = e2 from rfl,
      hφ0e0, hφ0e1, hφ0e2, hφ1e0, hφ1e1, hφ1e2, hφ2e0, hφ2e1, hφ2e2,
      mul_zero, add_zero, zero_add] at h0 h1 h2
    have hg0 : g 0 = 0 := (mul_eq_zero.mp h0).resolve_right h2ne
    have hg1 : g 1 = 0 := by
      have h := h1; rw [hg0, zero_mul, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_right (neg_ne_zero.mpr hc)
    have hg2 : g 2 = 0 := by
      have h := h2; rw [hg1, zero_mul, zero_add] at h
      exact (mul_eq_zero.mp h).resolve_right (neg_ne_zero.mpr hd)
    intro i; fin_cases i
    · exact hg0
    · exact hg1
    · exact hg2
  simpa only [v] using hv

private theorem rj34_basis (hW : Module.finrank (ZMod p) W = 4)
    {X : Subgroup (W ≃ₗ[ZMod p] W)} (hX : SplitSupport X 3) {e0 e1 e2 : W}
    (hvli : LinearIndependent (ZMod p) ![e0, e1, e2])
    (hvV : ∀ i, ![e0, e1, e2] i ∈ HardMathSupport.Kantor79.commutatorSpace X) :
    ∃ f : Module.Basis (Fin 4) (ZMod p) W,
      f 0 = e0 ∧ f 1 = e1 ∧ f 2 = e2 ∧
      f (Fin.last 3) ∈ centralizerSpace X ∧
      (∀ i : Fin 3, f i.castSucc ∈ HardMathSupport.Kantor79.commutatorSpace X) := by
  obtain ⟨f, hf, hflast⟩ := exists_basis_snoc_of_splitSupport hX (by rw [hW]) hvli hvV
  have hf0 : f 0 = e0 := by
    have h := hf 0; rw [Fin.castSucc_zero] at h; simpa using h
  have hf1 : f 1 = e1 := by
    have h := hf 1; rw [Fin.castSucc_one] at h; simpa using h
  have hf2 : f 2 = e2 := by
    have h := hf 2; rw [show (Fin.castSucc (2 : Fin 3)) = (2 : Fin 4) from rfl] at h
    simpa using h
  have hfV : ∀ i : Fin 3, f i.castSucc ∈ HardMathSupport.Kantor79.commutatorSpace X :=
    fun i => by rw [hf i]; exact hvV i
  exact ⟨f, hf0, hf1, hf2, hflast, hfV⟩

omit [Module.Finite (ZMod p) W] in
private theorem rj34_matrix_s0 (hp : p ≠ 2) {X : Subgroup (W ≃ₗ[ZMod p] W)}
    {f : Module.Basis (Fin 4) (ZMod p) W} {s0 : W ≃ₗ[ZMod p] W}
    {e0 e1 e2 : W} {φ0 : Module.Dual (ZMod p) W}
    (hφ0e0 : φ0 e0 = 2) (hφ0e1 : φ0 e1 = 0) (hφ0e2 : φ0 e2 = 0)
    (hs0eq : s0 = Module.reflection hφ0e0) (hs0X' : Module.reflection hφ0e0 ∈ X)
    (hflast : f (Fin.last 3) ∈ centralizerSpace X)
    (hf0 : f 0 = e0) (hf1 : f 1 = e1) (hf2 : f 2 = e2) :
    (fun k => φ0 (f k)) = Pi.single (0 : Fin 4) 2 ∧
      LinearMap.toMatrix f f (s0 : W →ₗ[ZMod p] W) =
        Matrix.blockSucc (diagSignMat (0 : Fin 3)) := by
  have hrepr0 : (fun k => f.repr e0 k) = Pi.single (0 : Fin 4) 1 := by
    rw [show e0 = f 0 from hf0.symm]; exact rj34_repr_self f 0
  have hφ0w : φ0 (f 3) = 0 := apply_eq_zero_of_reflection_mem hp hφ0e0 hs0X' hflast
  have hκ0 : (fun k => φ0 (f k)) = Pi.single (0 : Fin 4) 2 :=
    rj34_coroot_diag f (by rw [hf0]; exact hφ0e0) (by rw [hf1]; exact hφ0e1)
      (by rw [hf2]; exact hφ0e2) hφ0w
  refine ⟨hκ0, ?_⟩
  rw [hs0eq, rj34_diagSignMat_toMatrix f (r := e0) hφ0e0 0 hrepr0 hκ0]
  exact (blockSucc_diagSignMat (K := ZMod p) (i := (0 : Fin 3))).symm

omit [Module.Finite (ZMod p) W] in
private theorem rj34_matrix_s1 (hp : p ≠ 2) {X : Subgroup (W ≃ₗ[ZMod p] W)}
    {f : Module.Basis (Fin 4) (ZMod p) W} {s1 : W ≃ₗ[ZMod p] W}
    {r1 e0 e1 e2 : W} {φ1 : Module.Dual (ZMod p) W} {c : ZMod p}
    (hφ1 : φ1 r1 = 2)
    (hs1eq : s1 = Module.reflection hφ1) (hs1X' : Module.reflection hφ1 ∈ X)
    (hflast : f (Fin.last 3) ∈ centralizerSpace X)
    (hf0 : f 0 = e0) (hf1 : f 1 = e1) (hf2 : f 2 = e2)
    (hφ1e0 : φ1 e0 = c) (hφ1e1 : φ1 e1 = -c) (hφ1e2 : φ1 e2 = 0)
    (hc : c ≠ 0) (hre1 : e0 - e1 = c • r1) :
    (fun k => φ1 (f k)) = c • (Pi.single (0 : Fin 4) 1 - Pi.single (1 : Fin 4) 1) ∧
      LinearMap.toMatrix f f (s1 : W →ₗ[ZMod p] W) =
        Matrix.blockSucc (pijMat (0 : Fin 3) 1 1) := by
  have hre : r1 = c⁻¹ • (e0 - e1) := by
    rw [hre1, smul_smul, inv_mul_cancel₀ hc, one_smul]
  have hrepr1 : (fun k => f.repr r1 k) =
      c⁻¹ • (Pi.single (0 : Fin 4) 1 - Pi.single (1 : Fin 4) 1) := by
    rw [hre, show e0 = f 0 from hf0.symm, show e1 = f 1 from hf1.symm]
    exact rj34_repr_smul_sub f (i := (0 : Fin 4)) (j := (1 : Fin 4)) (c := c⁻¹)
  have hφ1w : φ1 (f 3) = 0 := apply_eq_zero_of_reflection_mem hp hφ1 hs1X' hflast
  have hκ1 : (fun k => φ1 (f k)) =
      c • (Pi.single (0 : Fin 4) 1 - Pi.single (1 : Fin 4) 1) :=
    rj34_coroot_pij_01 f c
      (by rw [hf0, hφ1e0]; ring)
      (by rw [hf1, hφ1e1]; ring)
      (by rw [hf2, hφ1e2]; ring) hφ1w
  refine ⟨hκ1, ?_⟩
  rw [hs1eq, rj34_pijMat_toMatrix f (r := r1) hφ1 (by decide) hc hrepr1 hκ1]
  exact (blockSucc_pijMat (K := ZMod p) (i := (0 : Fin 3)) (j := (1 : Fin 3)) 1).symm

omit [Module.Finite (ZMod p) W] in
private theorem rj34_matrix_s2 (hp : p ≠ 2) {X : Subgroup (W ≃ₗ[ZMod p] W)}
    {f : Module.Basis (Fin 4) (ZMod p) W} {s2 : W ≃ₗ[ZMod p] W}
    {r2 e0 e1 e2 : W} {φ2 : Module.Dual (ZMod p) W}
    (hφ2 : φ2 r2 = 2)
    (hs2eq : s2 = Module.reflection hφ2) (hs2X' : Module.reflection hφ2 ∈ X)
    (hflast : f (Fin.last 3) ∈ centralizerSpace X)
    (hf0 : f 0 = e0) (hf1 : f 1 = e1) (hf2 : f 2 = e2)
    (hφ2e0 : φ2 e0 = 0) (hφ2e1 : φ2 e1 ≠ 0) (hφ2e2 : φ2 e2 = -φ2 e1)
    (hre2 : e1 - e2 = φ2 e1 • r2) :
    (fun k => φ2 (f k)) = φ2 e1 • (Pi.single (1 : Fin 4) 1 - Pi.single (2 : Fin 4) 1) ∧
      LinearMap.toMatrix f f (s2 : W →ₗ[ZMod p] W) =
        Matrix.blockSucc (pijMat (1 : Fin 3) 2 1) := by
  have hre : r2 = (φ2 e1)⁻¹ • (f 1 - f 2) := by
    rw [show f 1 - f 2 = e1 - e2 from by rw [hf1, hf2], hre2, smul_smul,
      inv_mul_cancel₀ hφ2e1, one_smul]
  have hrepr2 : (fun k => f.repr r2 k) =
      (φ2 e1)⁻¹ • (Pi.single (1 : Fin 4) 1 - Pi.single (2 : Fin 4) 1) := by
    rw [hre]
    exact rj34_repr_smul_sub f (i := (1 : Fin 4)) (j := (2 : Fin 4)) (c := (φ2 e1)⁻¹)
  have hφ2w : φ2 (f 3) = 0 := apply_eq_zero_of_reflection_mem hp hφ2 hs2X' hflast
  have hκ2 : (fun k => φ2 (f k)) =
      φ2 e1 • (Pi.single (1 : Fin 4) 1 - Pi.single (2 : Fin 4) 1) :=
    rj34_coroot_pij_12 f (φ2 e1)
      (by rw [hf0, hφ2e0]; ring)
      (by rw [hf1]; ring)
      (by rw [hf2, hφ2e2]; ring) hφ2w
  refine ⟨hκ2, ?_⟩
  rw [hs2eq, rj34_pijMat_toMatrix f (r := r2) hφ2 (by decide) hφ2e1 hrepr2 hκ2]
  exact (blockSucc_pijMat (K := ZMod p) (i := (1 : Fin 3)) (j := (2 : Fin 3)) 1).symm

omit [Module.Finite (ZMod p) W] in
private theorem rj34_conclude (hp : p ≠ 2) {X : Subgroup (W ≃ₗ[ZMod p] W)}
    (hcard : Nat.card X = 336) {f : Module.Basis (Fin 4) (ZMod p) W}
    {s0 s1 s2 a : W ≃ₗ[ZMod p] W} {r r0 r1 : W}
    {φ0 φ1 ψ : Module.Dual (ZMod p) W}
    (h2ne : (2 : ZMod p) ≠ 0) (hs0X : s0 ∈ X) (hs1X : s1 ∈ X) (hs2X : s2 ∈ X) (haX : a ∈ X)
    (hφ0 : φ0 r0 = 2) (hφ1 : φ1 r1 = 2) (hψ : ψ r = 2) (haeq : a = Module.reflection hψ)
    (hs0eq : s0 = Module.reflection hφ0) (hs1eq : s1 = Module.reflection hφ1)
    (h0a : orderOf (s0 * a) = 3) (h1a : orderOf (s1 * a) = 3)
    (h12 : orderOf (s1 * s2) = 3)
    (hcomm : Commute a (s2 * s1 * s0 * (s2 * s1)⁻¹ * (s1 * s2 * s1) *
      (s2 * s1 * s0 * (s2 * s1)⁻¹)⁻¹))
    (hs0r : IsRefl p s0) (hs1r : IsRefl p s1) (hs2r : IsRefl p s2)
    (ha10ne : φ1 r0 ≠ 0) (hre1 : r0 - (r0 - φ1 r0 • r1) = φ1 r0 • r1)
    (hf0 : f 0 = r0) (hf1 : f 1 = r0 - φ1 r0 • r1)
    (hψw : ψ (f 3) = 0) (hr_last : f.repr r 3 = 0)
    (hs0mat : LinearMap.toMatrix f f (s0 : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (diagSignMat (0 : Fin 3)))
    (hs1mat : LinearMap.toMatrix f f (s1 : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (pijMat (0 : Fin 3) 1 1))
    (hs2mat : LinearMap.toMatrix f f (s2 : W →ₗ[ZMod p] W) =
      Matrix.blockSucc (pijMat (1 : Fin 3) 2 1))
    (hκ0 : (fun k => φ0 (f k)) = Pi.single (0 : Fin 4) 2)
    (hκ1 : (fun k => φ1 (f k)) =
      φ1 r0 • (Pi.single (0 : Fin 4) 1 - Pi.single (1 : Fin 4) 1)) :
    ∃ (β : ZMod p) (f : Module.Basis (Fin 4) (ZMod p) W),
      2 * β ^ 2 + β + 1 = 0 ∧ X = basisClosure f (j34Mats β) := by
  obtain ⟨t, hcommt, hword⟩ := rj34_t_word hcomm h12 hs0r hs1r hs2r
  have htmat := rj34_t_matrix hs0mat hs1mat hs2mat hword
  obtain ⟨hx2, hy2⟩ := rj34_t_relations hp hψ haeq h0a hcommt hs0mat htmat
  obtain ⟨h2xy, hsum, hcross, hy0ne⟩ :=
    rj34_scalars hp hκ0 hκ1 hψ haeq hφ0 hφ1 hs0eq hs1eq h0a h1a ha10ne hre1 rfl hf0 hf1 hr_last
  obtain ⟨β, hβ, hβ0, hy0ne, hy1eq, hx0', hx1'⟩ := rj34_beta h2xy hsum hcross hx2 hy2 h2ne
  obtain ⟨hr, hκ⟩ := rj34_coords h2ne hy0ne hβ0 hy1eq hy2 hx0' hx1' hx2 hψw hr_last
  exact ⟨β, f, hβ, rj34_final hp hcard h2ne hβ hs0X hs1X hs2X haX hψ haeq hs0mat hs1mat hs2mat
    hr hκ hy0ne hβ0⟩

private theorem rj34_exists (hp : p ≠ 2) (hW : Module.finrank (ZMod p) W = 4)
    {X : Subgroup (W ≃ₗ[ZMod p] W)} (hX : SplitSupport X 3) (hcard : Nat.card X = 336)
    (hF : J34Frame p X) :
    ∃ (β : ZMod p) (f : Module.Basis (Fin 4) (ZMod p) W),
      2 * β ^ 2 + β + 1 = 0 ∧ X = basisClosure f (j34Mats β) := by
  classical
  have h2ne : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  obtain ⟨s0, s1, s2, a, r0, r1, r2, r, φ0, φ1, φ2, ψ, hφ0, hφ1, hφ2, hψ, hs0X, hs1X,
    hs2X, haX, hs0eq, hs1eq, hs2eq, haeq, h0r2, h2r0, h12', h01', ha10ne, hφ2r1ne, hr0V,
    hr1V, hr2V, hs0r, hs1r, hs2r, h0a, h1a, h12, hcomm⟩ := rj34_setup hp hF
  let e0 : W := r0
  let e1 : W := r0 - φ1 r0 • r1
  let e2 : W := e1 - φ2 e1 • r2
  obtain ⟨hφ0e0, hφ1e0, hφ2e0, hφ0e1, hφ1e1, hφ2e1, hφ0e2, hφ1e2, hφ2e2, hcne, hcne'⟩ :=
    rj34_pair_data (e0 := e0) (e1 := e1) (e2 := e2) rfl rfl rfl hφ0 hφ1 hφ2 ⟨h0r2, h2r0⟩
      h12' h01' ha10ne hφ2r1ne
  have he1V : e1 ∈ HardMathSupport.Kantor79.commutatorSpace X := by
    dsimp only [e1]; exact sub_mem hr0V (Submodule.smul_mem _ _ hr1V)
  have he2V : e2 ∈ HardMathSupport.Kantor79.commutatorSpace X := by
    dsimp only [e2]; exact sub_mem he1V (Submodule.smul_mem _ _ hr2V)
  have hvli : LinearIndependent (ZMod p) ![e0, e1, e2] :=
    rj34_li (d := -φ1 r0 * φ2 r1) hφ0e0 hφ0e1 hφ0e2 hφ1e0 hφ1e1 hφ1e2 hφ2e0 hφ2e1 hφ2e2
      h2ne ha10ne hcne'
  have hvV : ∀ i, ![e0, e1, e2] i ∈ HardMathSupport.Kantor79.commutatorSpace X := by
    intro i; fin_cases i
    · exact hr0V
    · exact he1V
    · exact he2V
  obtain ⟨f, hf0, hf1, hf2, hflast, hfV⟩ := rj34_basis hW hX hvli hvV
  have hre1 : e0 - e1 = φ1 r0 • r1 := by dsimp only [e0, e1]; abel
  have hre2 : e1 - e2 = φ2 e1 • r2 := by dsimp only [e1, e2]; abel
  obtain ⟨hκ0, hs0mat⟩ := rj34_matrix_s0 hp hφ0e0 hφ0e1 hφ0e2 hs0eq (hs0eq ▸ hs0X) hflast
    hf0 hf1 hf2
  obtain ⟨hκ1, hs1mat⟩ := rj34_matrix_s1 hp hφ1 hs1eq (hs1eq ▸ hs1X) hflast hf0 hf1 hf2
    hφ1e0 hφ1e1 hφ1e2 ha10ne hre1
  obtain ⟨hκ2, hs2mat⟩ := rj34_matrix_s2 hp hφ2 hs2eq (hs2eq ▸ hs2X) hflast hf0 hf1 hf2
    hφ2e0 hcne hφ2e2 hre2
  have hrV : r ∈ HardMathSupport.Kantor79.commutatorSpace X :=
    mem_commutatorSpace_of_reflection_mem hp hψ (haeq ▸ haX)
  have hψw : ψ (f 3) = 0 := apply_eq_zero_of_reflection_mem hp hψ (haeq ▸ haX) hflast
  have hr_last : f.repr r 3 = 0 := rj34_repr_last_eq_zero hX hfV hflast hrV
  exact rj34_conclude hp hcard h2ne hs0X hs1X hs2X haX hφ0 hφ1 hψ haeq hs0eq hs1eq h0a h1a
    h12 hcomm hs0r hs1r hs2r ha10ne hre1 hf0 hf1 hψw hr_last hs0mat hs1mat hs2mat hκ0 hκ1

theorem exists_basis_eq_j34Mats_of_j34Frame (hp : p ≠ 2)
    (hW : Module.finrank (ZMod p) W = 4) {X : Subgroup (W ≃ₗ[ZMod p] W)} (hX : SplitSupport X 3)
    (hcard : Nat.card X = 336) (hF : J34Frame p X) :
    ∃ (β : ZMod p) (f : Module.Basis (Fin 4) (ZMod p) W),
      2 * β ^ 2 + β + 1 = 0 ∧ X = basisClosure f (j34Mats β) := by
  exact rj34_exists hp hW hX hcard hF
end CFSG.StandardType.ZS

end
