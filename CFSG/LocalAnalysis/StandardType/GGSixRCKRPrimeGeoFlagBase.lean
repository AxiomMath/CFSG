module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeGeoFlag
public import Mathlib.Algebra.Module.LinearMap.DivisionRing

public section

namespace CFSG.StandardType.RCKRP

open CFSG.StandardType.ClassicalPosition
open scoped Matrix

private def rckRPgb_dot {ι F : Type} [Fintype ι] [Field F] (φ : ι → F) :
    (ι → F) →ₗ[F] F where
  toFun m := φ ⬝ᵥ m
  map_add' x y := by simp [dotProduct_add]
  map_smul' a x := by simp [dotProduct_smul]

@[simp] private theorem rckRPgb_dot_apply {ι F : Type} [Fintype ι] [Field F]
    (φ m : ι → F) : rckRPgb_dot φ m = φ ⬝ᵥ m := rfl

private theorem rckRPgb_dot_ne_zero {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {φ : ι → F} (hφ : φ ≠ 0) : rckRPgb_dot φ ≠ 0 := by
  intro h
  obtain ⟨i, hi⟩ := Function.ne_iff.mp hφ
  have h0 := congrArg (fun f : (ι → F) →ₗ[F] F => f (Pi.single i 1)) h
  simp only [rckRPgb_dot_apply, LinearMap.zero_apply, dotProduct_single_one] at h0
  exact hi h0

private theorem rckRPgb_one_add_mul_one_add {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {N : F → Matrix ι ι F} (hNadd : ∀ c d, N (c + d) = N c + N d)
    (hNmul : ∀ c d, N c * N d = 0) (c d : F) :
    (1 + N c) * (1 + N d) = 1 + N (c + d) := by
  calc (1 + N c) * (1 + N d)
      = 1 + N c + (1 + N c) * N d := by rw [Matrix.mul_add, Matrix.mul_one]
    _ = 1 + N c + (N d + N c * N d) := by rw [Matrix.add_mul, Matrix.one_mul]
    _ = 1 + N c + N d := by rw [hNmul c d, add_zero]
    _ = 1 + N (c + d) := by rw [hNadd]; abel

private theorem rckRPgb_one_add_mul_one_add_neg {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] {N : F → Matrix ι ι F} (hN0 : N 0 = 0)
    (hNadd : ∀ c d, N (c + d) = N c + N d) (hNmul : ∀ c d, N c * N d = 0) (c : F) :
    (1 + N c) * (1 + N (-c)) = 1 := by
  rw [rckRPgb_one_add_mul_one_add hNadd hNmul, add_neg_cancel, hN0, add_zero]

private theorem rckRPgb_mem_closure_iff {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {P : F → Prop} {N : F → Matrix ι ι F}
    (hP0 : P 0) (hPadd : ∀ c d, P c → P d → P (c + d))
    (hPneg : ∀ c, P c → P (-c))
    (hN0 : N 0 = 0) (hNadd : ∀ c d, N (c + d) = N c + N d)
    (hNmul : ∀ c d, N c * N d = 0) {x : GL ι F} :
    x ∈ Subgroup.closure {g : GL ι F | ∃ c, P c ∧ (g : Matrix ι ι F) = 1 + N c} ↔
      ∃ c, P c ∧ (x : Matrix ι ι F) = 1 + N c := by
  constructor
  · intro hx
    refine Subgroup.closure_induction
      (p := fun (y : GL ι F) _ => ∃ c, P c ∧ (y : Matrix ι ι F) = 1 + N c) ?_ ?_ ?_ ?_ hx
    · rintro g ⟨c, hcP, hc⟩
      exact ⟨c, hcP, hc⟩
    · exact ⟨0, hP0, by simp [hN0]⟩
    · rintro y z _ _ ⟨c, hcP, hc⟩ ⟨d, hdP, hd⟩
      exact ⟨c + d, hPadd c d hcP hdP, by
        rw [Units.val_mul, hc, hd, rckRPgb_one_add_mul_one_add hNadd hNmul]⟩
    · rintro y _ ⟨c, hcP, hc⟩
      exact ⟨-c, hPneg c hcP, by
        refine Units.inv_eq_of_mul_eq_one_right ?_
        rw [hc, rckRPgb_one_add_mul_one_add_neg hN0 hNadd hNmul]⟩
  · rintro ⟨c, hcP, hx⟩
    exact Subgroup.subset_closure ⟨c, hcP, hx⟩

private theorem rckRPgb_coe_ne_one {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {N : F → Matrix ι ι F} (hN0 : N 0 = 0) {x : GL ι F} {c : F}
    (hx : (x : Matrix ι ι F) = 1 + N c) (hx1 : x ≠ 1) : c ≠ 0 := by
  rintro rfl
  refine hx1 (Units.ext ?_)
  simp [hx, hN0]

private theorem rckRPgb_smul_vecMulVec_mulVec {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] (c : F) (v φ m : ι → F) :
    (c • Matrix.vecMulVec v φ) *ᵥ m = c • ((φ ⬝ᵥ m) • v) := by
  rw [Matrix.smul_mulVec, Matrix.vecMulVec_mulVec]
  simp [smul_smul]

private theorem rckRPgb_toLin_vecMulVec {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (v φ : ι → F) :
    Matrix.toLin' (Matrix.vecMulVec v φ) = (rckRPgb_dot φ).smulRight v := by
  apply LinearMap.ext
  intro m
  rw [Matrix.toLin'_apply, LinearMap.smulRight_apply, rckRPgb_dot_apply,
    Matrix.vecMulVec_mulVec]
  simp

private theorem rckRPgb_range_vecMulVec {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (v φ : ι → F) (hφ : φ ≠ 0) :
    LinearMap.range (Matrix.toLin' (Matrix.vecMulVec v φ)) =
      Submodule.span F ({v} : Set (ι → F)) := by
  rw [rckRPgb_toLin_vecMulVec]
  exact LinearMap.range_smulRight_apply (rckRPgb_dot_ne_zero hφ) v

private theorem rckRPgb_range_smul_vecMulVec {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {v φ : ι → F} {c : F} (hφ : φ ≠ 0) (hc : c ≠ 0) :
    LinearMap.range (Matrix.toLin' (c • Matrix.vecMulVec v φ)) =
      Submodule.span F ({v} : Set (ι → F)) := by
  have hsmul : Matrix.toLin' (c • Matrix.vecMulVec v φ)
      = c • Matrix.toLin' (Matrix.vecMulVec v φ) := LinearEquiv.map_smul _ c _
  rw [hsmul, LinearMap.range_smul _ c hc, rckRPgb_range_vecMulVec v φ hφ]

private theorem rckRPgb_ker_smul_vecMulVec {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {v φ : ι → F} {c : F} (hc : c ≠ 0) (hv : v ≠ 0) :
    LinearMap.ker (Matrix.toLin' (c • Matrix.vecMulVec v φ)) = (rckRPgb_dot φ).ker := by
  ext m
  rw [LinearMap.mem_ker, LinearMap.mem_ker, Matrix.toLin'_apply,
    rckRPgb_smul_vecMulVec_mulVec, rckRPgb_dot_apply]
  constructor
  · intro h
    rcases smul_eq_zero.mp h with hc0 | h
    · exact absurd hc0 hc
    · rcases smul_eq_zero.mp h with hφ0 | hv0
      · exact hφ0
      · exact absurd hv0 hv
  · intro h
    rw [h, zero_smul, smul_zero]

private theorem rckRPgb_pair_mulVec {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (v w a b : ι → F) (α β : F) (m : ι → F) :
    (α • Matrix.vecMulVec v a + β • Matrix.vecMulVec w b) *ᵥ m =
      (α * (a ⬝ᵥ m)) • v + (β * (b ⬝ᵥ m)) • w := by
  rw [Matrix.add_mulVec, Matrix.smul_mulVec, Matrix.smul_mulVec,
    Matrix.vecMulVec_mulVec, Matrix.vecMulVec_mulVec]
  simp [smul_smul, mul_comm, mul_left_comm, mul_assoc]

private theorem rckRPgb_exists_coeff_v {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {a b : ι → F} {i j : ι} (hd : a i * b j - a j * b i ≠ 0) :
    ∃ m : ι → F, a ⬝ᵥ m = 1 ∧ b ⬝ᵥ m = 0 := by
  refine ⟨(b j / (a i * b j - a j * b i)) • Pi.single i 1 +
    (-b i / (a i * b j - a j * b i)) • Pi.single j 1, ?_, ?_⟩
  · have hd' : b j * a i - a j * b i ≠ 0 := by simpa [mul_comm] using hd
    simp only [dotProduct_add, dotProduct_smul, dotProduct_single_one,
      smul_eq_mul]
    field_simp [hd']
    ring
  · have hd' : b j * a i - a j * b i ≠ 0 := by simpa [mul_comm] using hd
    simp only [dotProduct_add, dotProduct_smul, dotProduct_single_one,
      smul_eq_mul]
    field_simp [hd']
    ring

private theorem rckRPgb_exists_coeff_w {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {a b : ι → F} {i j : ι} (hd : a i * b j - a j * b i ≠ 0) :
    ∃ m : ι → F, a ⬝ᵥ m = 0 ∧ b ⬝ᵥ m = 1 := by
  refine ⟨(-a j / (a i * b j - a j * b i)) • Pi.single i 1 +
    (a i / (a i * b j - a j * b i)) • Pi.single j 1, ?_, ?_⟩
  · have hd' : b j * a i - a j * b i ≠ 0 := by simpa [mul_comm] using hd
    simp only [dotProduct_add, dotProduct_smul, dotProduct_single_one,
      smul_eq_mul]
    field_simp [hd']
    ring
  · have hd' : b j * a i - a j * b i ≠ 0 := by simpa [mul_comm] using hd
    simp only [dotProduct_add, dotProduct_smul, dotProduct_single_one,
      smul_eq_mul]
    field_simp [hd']
    ring

private theorem rckRPgb_range_pair_smul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {v w a b : ι → F} {α β : F} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hminor : ∃ i j, a i * b j - a j * b i ≠ 0) :
    LinearMap.range (Matrix.toLin' (α • Matrix.vecMulVec v a + β • Matrix.vecMulVec w b)) =
      Submodule.span F ({v, w} : Set (ι → F)) := by
  apply le_antisymm
  · rintro y ⟨m, rfl⟩
    rw [Matrix.toLin'_apply, rckRPgb_pair_mulVec]
    exact Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  · rw [Submodule.span_le]
    rintro x (rfl | rfl)
    · obtain ⟨i, j, hd⟩ := hminor
      obtain ⟨m, hm1, hm2⟩ := rckRPgb_exists_coeff_v hd
      refine ⟨α⁻¹ • m, ?_⟩
      rw [Matrix.toLin'_apply, rckRPgb_pair_mulVec]
      have h1 : a ⬝ᵥ (α⁻¹ • m) = α⁻¹ := by
        rw [dotProduct_smul, hm1, smul_eq_mul, mul_one]
      have h2 : b ⬝ᵥ (α⁻¹ • m) = 0 := by
        rw [dotProduct_smul, hm2, smul_zero]
      rw [h1, h2, mul_zero, mul_inv_cancel₀ hα, one_smul, zero_smul, add_zero]
    · obtain ⟨i, j, hd⟩ := hminor
      obtain ⟨m, hm1, hm2⟩ := rckRPgb_exists_coeff_w hd
      refine ⟨β⁻¹ • m, ?_⟩
      rw [Matrix.toLin'_apply, rckRPgb_pair_mulVec]
      have h1 : a ⬝ᵥ (β⁻¹ • m) = 0 := by
        rw [dotProduct_smul, hm1, smul_zero]
      have h2 : b ⬝ᵥ (β⁻¹ • m) = β⁻¹ := by
        rw [dotProduct_smul, hm2, smul_eq_mul, mul_one]
      rw [h1, h2, mul_zero, mul_inv_cancel₀ hβ, one_smul, zero_smul, zero_add]

private theorem rckRPgb_ker_pair_smul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {v w a b : ι → F} {α β : F} (hα : α ≠ 0) (hβ : β ≠ 0)
    (hli : LinearIndependent F ![v, w]) :
    LinearMap.ker (Matrix.toLin' (α • Matrix.vecMulVec v a + β • Matrix.vecMulVec w b)) =
      (rckRPgb_dot a).ker ⊓ (rckRPgb_dot b).ker := by
  ext m
  rw [LinearMap.mem_ker, Submodule.mem_inf, LinearMap.mem_ker, LinearMap.mem_ker,
    Matrix.toLin'_apply, rckRPgb_pair_mulVec, rckRPgb_dot_apply, rckRPgb_dot_apply]
  constructor
  · intro h
    obtain ⟨h1, h2⟩ := hli.eq_zero_of_pair (by simpa using h)
    exact ⟨(mul_eq_zero.mp h1).resolve_left hα, (mul_eq_zero.mp h2).resolve_left hβ⟩
  · rintro ⟨h1, h2⟩
    rw [h1, h2, mul_zero, mul_zero, zero_smul, zero_smul, add_zero]

private theorem rckRPgb_exists_minor_of_ne_smul {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] {a b : ι → F} (ha : a ≠ 0) (h : ∀ lam : F, b ≠ lam • a) :
    ∃ i j, a i * b j - a j * b i ≠ 0 := by
  obtain ⟨i, hi⟩ := Function.ne_iff.mp ha
  by_contra hc
  push Not at hc
  refine h (b i / a i) ?_
  funext j
  have hij : a i * b j = a j * b i := sub_eq_zero.mp (hc i j)
  rw [Pi.smul_apply, smul_eq_mul, div_mul_eq_mul_div, eq_div_iff hi]
  calc b j * a i = a i * b j := mul_comm _ _
    _ = a j * b i := hij
    _ = b i * a j := mul_comm _ _

private theorem rckRPgb_matTransv_mul_zero {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {v φ : ι → F} (hvφ : φ ⬝ᵥ v = 0) (c d : F) :
    (c • Matrix.vecMulVec v φ) * (d • Matrix.vecMulVec v φ) = 0 := by
  rw [smul_mul_smul, Matrix.vecMulVec_mul_vecMulVec, hvφ]
  simp

private theorem rckRPgb_matTransvGroup_mem {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {v φ : ι → F} (hvφ : φ ⬝ᵥ v = 0) {x : GL ι F} :
    x ∈ matTransvGroup v φ ↔
      ∃ c : F, (x : Matrix ι ι F) = 1 + c • Matrix.vecMulVec v φ := by
  have h := rckRPgb_mem_closure_iff (x := x) (P := fun _ => True)
    (N := fun c => c • Matrix.vecMulVec v φ)
    (by trivial) (by intro c d _ _; trivial) (by intro c _; trivial)
    (by simp) (by intro c d; rw [add_smul])
    (rckRPgb_matTransv_mul_zero hvφ)
  simpa [matTransvGroup] using h

private theorem rckRPgb_unitTransv_mul_zero {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {v a : ι → F} (ha : a ⬝ᵥ v = 0) (c d : F) :
    (c • Matrix.vecMulVec v a) * (d • Matrix.vecMulVec v a) = 0 := by
  rw [smul_mul_smul, Matrix.vecMulVec_mul_vecMulVec, ha]
  simp

private theorem rckRPgb_unitTransvGroup_mem {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {σ : F →+* F} {G : Matrix ι ι F} {v : ι → F}
    (hiso : Matrix.vecMul (fun i => σ (v i)) G ⬝ᵥ v = 0) {x : GL ι F} :
    x ∈ unitTransvGroup σ G v ↔ ∃ c : F, σ c = c ∧
      (x : Matrix ι ι F) = 1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) G) := by
  have h := rckRPgb_mem_closure_iff (x := x) (P := fun c => σ c = c)
    (N := fun c => c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) G))
    (by simp) (by intro c d hc hd; rw [map_add, hc, hd])
    (by intro c hc; rw [map_neg, hc])
    (by simp) (by intro c d; rw [add_smul])
    (rckRPgb_unitTransv_mul_zero hiso)
  simpa [unitTransvGroup] using h

private theorem rckRPgb_unitTransv_fun_ne_zero {ι F : Type} [Fintype ι] [DecidableEq ι]
    [Field F] {σ : F →+* F} (hσ : Function.Injective σ) {G : Matrix ι ι F}
    (hG : IsUnit G.det) {v : ι → F} (hv : v ≠ 0) :
    Matrix.vecMul (fun i => σ (v i)) G ≠ 0 := by
  have hinj : Function.Injective (fun x : ι → F => x ᵥ* G) :=
    Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det G).mpr hG)
  intro h
  have h1 : (fun i => σ (v i)) = 0 := hinj (by simpa using h)
  have hv0 : v = 0 := by
    funext i
    exact hσ (by simpa using congrFun h1 i)
  exact hv hv0

private theorem rckRPgb_altSiegel_mul_zero {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G : Matrix ι ι F} (hsymm : G.transpose = G)
    (halt : ∀ x : ι → F, x ⬝ᵥ G.mulVec x = 0) {v w : ι → F}
    (hvw : v ⬝ᵥ G.mulVec w = 0) (c d : F) :
    (c • (Matrix.vecMulVec v (G.mulVec w) + Matrix.vecMulVec w (G.mulVec v))) *
      (d • (Matrix.vecMulVec v (G.mulVec w) + Matrix.vecMulVec w (G.mulVec v))) = 0 := by
  have hvv : (G.mulVec v) ⬝ᵥ v = 0 := by
    rw [dotProduct_comm]; exact halt v
  have hww : (G.mulVec w) ⬝ᵥ w = 0 := by
    rw [dotProduct_comm]; exact halt w
  have hwv : (G.mulVec w) ⬝ᵥ v = 0 := by
    rw [dotProduct_comm]; exact hvw
  have hvw' : (G.mulVec v) ⬝ᵥ w = 0 := by
    rw [dotProduct_comm, ← hsymm, Matrix.dotProduct_transpose_mulVec]; exact hvw
  rw [smul_mul_smul, Matrix.add_mul, Matrix.mul_add, Matrix.mul_add,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
    hvv, hvw', hwv, hww]
  simp

private theorem rckRPgb_altSiegelGroup_mem {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G : Matrix ι ι F} (hsymm : G.transpose = G)
    (halt : ∀ x : ι → F, x ⬝ᵥ G.mulVec x = 0) {v w : ι → F}
    (hvw : v ⬝ᵥ G.mulVec w = 0) {x : GL ι F} :
    x ∈ altSiegelGroup G v w ↔ ∃ c : F,
      (x : Matrix ι ι F) = 1 + c • (Matrix.vecMulVec v (G.mulVec w) +
        Matrix.vecMulVec w (G.mulVec v)) := by
  have h := rckRPgb_mem_closure_iff (x := x) (P := fun _ => True)
    (N := fun c => c • (Matrix.vecMulVec v (G.mulVec w) +
      Matrix.vecMulVec w (G.mulVec v)))
    (by trivial) (by intro c d _ _; trivial) (by intro c _; trivial)
    (by simp) (by intro c d; rw [add_smul])
    (rckRPgb_altSiegel_mul_zero hsymm halt hvw)
  simpa [altSiegelGroup] using h

private theorem rckRPgb_altSiegel_minor {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G : Matrix ι ι F} (hG : IsUnit G.det) {v w : ι → F}
    (hli : LinearIndependent F ![v, w]) :
    ∃ i j, (G.mulVec w) i * (G.mulVec v) j - (G.mulVec w) j * (G.mulVec v) i ≠ 0 := by
  have hinj : Function.Injective G.mulVec :=
    Matrix.mulVec_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det G).mpr hG)
  have hw : w ≠ 0 := by simpa using hli.ne_zero (1 : Fin 2)
  have ha : G.mulVec w ≠ 0 := by
    intro h
    exact hw (hinj (by simpa using h))
  have hne : ∀ lam : F, G.mulVec v ≠ lam • G.mulVec w := by
    intro lam h
    have h1 : G.mulVec v = G.mulVec (lam • w) := by
      rw [Matrix.mulVec_smul]; exact h
    have h2 : v = lam • w := hinj h1
    exact one_ne_zero (hli.eq_zero_of_pair' (s := 1) (t := lam) (by simpa using h2)).1
  exact rckRPgb_exists_minor_of_ne_smul ha hne

private theorem rckRPgb_unitPair_mul_zero {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {σ : F →+* F} {G : Matrix ι ι F} {v w : ι → F}
    (hvv : Matrix.vecMul (fun i => σ (v i)) G ⬝ᵥ v = 0)
    (hww : Matrix.vecMul (fun i => σ (w i)) G ⬝ᵥ w = 0)
    (hvw : Matrix.vecMul (fun i => σ (v i)) G ⬝ᵥ w = 0)
    (hwv : Matrix.vecMul (fun i => σ (w i)) G ⬝ᵥ v = 0) (c d : F) :
    (c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (w i)) G) -
        σ c • Matrix.vecMulVec w (Matrix.vecMul (fun i => σ (v i)) G)) *
      (d • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (w i)) G) -
        σ d • Matrix.vecMulVec w (Matrix.vecMul (fun i => σ (v i)) G)) = 0 := by
  rw [sub_mul, mul_sub, mul_sub, smul_mul_smul, smul_mul_smul, smul_mul_smul, smul_mul_smul,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
    Matrix.vecMulVec_mul_vecMulVec, Matrix.vecMulVec_mul_vecMulVec,
    hwv, hww, hvv, hvw]
  simp

private theorem rckRPgb_unitPairGroup_mem {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {σ : F →+* F} {G : Matrix ι ι F} {v w : ι → F}
    (hvv : Matrix.vecMul (fun i => σ (v i)) G ⬝ᵥ v = 0)
    (hww : Matrix.vecMul (fun i => σ (w i)) G ⬝ᵥ w = 0)
    (hvw : Matrix.vecMul (fun i => σ (v i)) G ⬝ᵥ w = 0)
    (hwv : Matrix.vecMul (fun i => σ (w i)) G ⬝ᵥ v = 0) {x : GL ι F} :
    x ∈ unitPairGroup σ G v w ↔ ∃ c : F,
      (x : Matrix ι ι F) = 1 + c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (w i)) G) -
        σ c • Matrix.vecMulVec w (Matrix.vecMul (fun i => σ (v i)) G) := by
  have h := rckRPgb_mem_closure_iff (x := x) (P := fun _ => True)
    (N := fun c => c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (w i)) G) -
      σ c • Matrix.vecMulVec w (Matrix.vecMul (fun i => σ (v i)) G))
    (by trivial) (by intro c d _ _; trivial) (by intro c _; trivial)
    (by simp) (by intro c d; rw [add_smul, map_add, add_smul]; abel)
    (rckRPgb_unitPair_mul_zero hvv hww hvw hwv)
  simpa [unitPairGroup, add_sub_assoc] using h

private theorem rckRPgb_sigma_eq_smul {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {σ : F →+* F} (hσ : Function.Injective σ) {v w : ι → F} (hv : v ≠ 0) {lam : F}
    (h : ∀ i, σ (v i) = lam * σ (w i)) : ∃ μ : F, v = μ • w := by
  obtain ⟨j, hj⟩ := Function.ne_iff.mp hv
  have hσvj : σ (v j) ≠ 0 := fun h0 => hj (hσ (by simpa using h0))
  by_cases hwj : w j = 0
  · exact absurd (by simpa [hwj] using h j) hσvj
  · have hσwj : σ (w j) ≠ 0 := fun h0 => hwj (hσ (by simpa using h0))
    refine ⟨v j / w j, ?_⟩
    have hlam : lam = σ (v j) / σ (w j) := by
      rw [eq_div_iff hσwj]
      exact (h j).symm
    funext i
    apply hσ
    rw [h i, Pi.smul_apply, smul_eq_mul, map_mul, map_div₀, hlam]

private theorem rckRPgb_unitPair_minor {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {σ : F →+* F} (hσ : Function.Injective σ) {G : Matrix ι ι F} (hG : IsUnit G.det)
    {v w : ι → F} (hli : LinearIndependent F ![v, w]) :
    ∃ i j, Matrix.vecMul (fun i => σ (w i)) G i * Matrix.vecMul (fun i => σ (v i)) G j -
        Matrix.vecMul (fun i => σ (w i)) G j * Matrix.vecMul (fun i => σ (v i)) G i ≠ 0 := by
  have hinj : Function.Injective (fun x : ι → F => x ᵥ* G) :=
    Matrix.vecMul_injective_of_isUnit ((Matrix.isUnit_iff_isUnit_det G).mpr hG)
  have hw : w ≠ 0 := by simpa using hli.ne_zero (1 : Fin 2)
  have hv : v ≠ 0 := by simpa using hli.ne_zero (0 : Fin 2)
  have ha : (fun i => σ (w i)) ᵥ* G ≠ 0 := by
    intro h
    have h1 : (fun i => σ (w i)) = 0 := hinj (by simpa using h)
    have hw0 : w = 0 := by
      funext i
      exact hσ (by simpa using congrFun h1 i)
    exact hw hw0
  have hne : ∀ lam : F, (fun i => σ (v i)) ᵥ* G ≠ lam • ((fun i => σ (w i)) ᵥ* G) := by
    intro lam h
    have h1 : (fun i => σ (v i)) = lam • (fun i => σ (w i)) := by
      apply hinj
      simpa [Matrix.smul_vecMul] using h
    obtain ⟨μ, hμ⟩ := rckRPgb_sigma_eq_smul hσ hv (fun i => by simpa using congrFun h1 i)
    have hrel : (1 : F) • v = μ • w := by simpa using hμ
    exact one_ne_zero (hli.eq_zero_of_pair' (s := 1) (t := μ) hrel).1
  exact rckRPgb_exists_minor_of_ne_smul ha hne

private theorem rckRPgb_smul_pair_mulVec {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (v w a b : ι → F) (c : F) (m : ι → F) :
    (c • (Matrix.vecMulVec v a + Matrix.vecMulVec w b)) *ᵥ m
      = c • ((a ⬝ᵥ m) • v + (b ⬝ᵥ m) • w) := by
  rw [smul_add, rckRPgb_pair_mulVec]
  simp [smul_add, smul_smul]

private theorem rckRPgb_form_pair {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    {G : Matrix ι ι F} (m v w a b : ι → F) (c : F) :
    m ⬝ᵥ G.mulVec (c • ((a ⬝ᵥ m) • v + (b ⬝ᵥ m) • w))
      = c * ((a ⬝ᵥ m) * (m ⬝ᵥ G.mulVec v) + (b ⬝ᵥ m) * (m ⬝ᵥ G.mulVec w)) := by
  simp only [Matrix.mulVec_smul, Matrix.mulVec_add, dotProduct_add,
    dotProduct_smul, smul_eq_mul]

theorem glGeoFlag_matTransvGroup {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (B : Option ((ι → F) → (ι → F) → F)) {v φ : ι → F} (hv : v ≠ 0) (hφ : φ ≠ 0)
    (hvφ : φ ⬝ᵥ v = 0) : GLGeoFlag B (matTransvGroup v φ) := by
  refine ⟨Submodule.span F ({v} : Set (ι → F)), (rckRPgb_dot φ).ker, ?_, ?_, ?_⟩
  · rw [Submodule.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    change rckRPgb_dot φ v = 0
    rw [rckRPgb_dot_apply]
    exact hvφ
  · rintro x hx hx1
    obtain ⟨c, hc⟩ := rckRPgb_matTransvGroup_mem hvφ |>.mp hx
    have hc0 : c ≠ 0 :=
      rckRPgb_coe_ne_one (x := x) (N := fun c => c • Matrix.vecMulVec v φ) (by simp) hc hx1
    have hsub : (x : Matrix ι ι F) - 1 = c • Matrix.vecMulVec v φ := by
      rw [hc]; abel
    constructor
    · rw [hsub]
      exact rckRPgb_range_smul_vecMulVec hφ hc0
    · rw [hsub]
      exact rckRPgb_ker_smul_vecMulVec hc0 hv
  · intro b _
    right
    exact finrank_span_singleton hv

theorem glGeoFlag_altSiegelGroup {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F] [CharP F 2]
    {G : Matrix ι ι F} (hG : IsUnit G.det) (hsymm : G.transpose = G)
    (halt : ∀ x : ι → F, x ⬝ᵥ G.mulVec x = 0)
    {v w : ι → F} (hli : LinearIndependent F ![v, w]) (hvw : v ⬝ᵥ G.mulVec w = 0) :
    GLGeoFlag (some fun u u' => u ⬝ᵥ G.mulVec u') (altSiegelGroup G v w) := by
  refine ⟨Submodule.span F ({v, w} : Set (ι → F)),
    (rckRPgb_dot (G.mulVec w)).ker ⊓ (rckRPgb_dot (G.mulVec v)).ker, ?_, ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro y (hy | hy)
    · rw [hy]
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · change rckRPgb_dot (G.mulVec w) v = 0
        rw [rckRPgb_dot_apply, dotProduct_comm]
        exact hvw
      · change rckRPgb_dot (G.mulVec v) v = 0
        rw [rckRPgb_dot_apply, dotProduct_comm]
        exact halt v
    · rw [hy]
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · change rckRPgb_dot (G.mulVec w) w = 0
        rw [rckRPgb_dot_apply, dotProduct_comm]
        exact halt w
      · change rckRPgb_dot (G.mulVec v) w = 0
        rw [rckRPgb_dot_apply, dotProduct_comm, ← hsymm,
          Matrix.dotProduct_transpose_mulVec]
        exact hvw
  · rintro x hx hx1
    obtain ⟨c, hc⟩ := (rckRPgb_altSiegelGroup_mem hsymm halt hvw).mp hx
    have hc0 : c ≠ 0 :=
      rckRPgb_coe_ne_one (x := x)
        (N := fun c => c • (Matrix.vecMulVec v (G.mulVec w) +
          Matrix.vecMulVec w (G.mulVec v))) (by simp) hc hx1
    have hsub : (x : Matrix ι ι F) - 1 =
        c • (Matrix.vecMulVec v (G.mulVec w) + Matrix.vecMulVec w (G.mulVec v)) := by
      rw [hc]; abel
    constructor
    · rw [hsub, smul_add]
      exact rckRPgb_range_pair_smul (v := v) (w := w)
        (a := G.mulVec w) (b := G.mulVec v) (α := c) (β := c)
        hc0 hc0 (rckRPgb_altSiegel_minor hG hli)
    · rw [hsub, smul_add]
      exact rckRPgb_ker_pair_smul (v := v) (w := w)
        (a := G.mulVec w) (b := G.mulVec v) (α := c) (β := c)
        hc0 hc0 hli
  · intro b hb
    simp only [Option.mem_some_iff] at hb
    subst hb
    left
    rintro x hx m
    obtain ⟨c, hc⟩ := (rckRPgb_altSiegelGroup_mem hsymm halt hvw).mp hx
    have hsub : (x : Matrix ι ι F) - 1 =
        c • (Matrix.vecMulVec v (G.mulVec w) + Matrix.vecMulVec w (G.mulVec v)) := by
      rw [hc]; abel
    rw [hsub, rckRPgb_smul_pair_mulVec (v := v) (w := w)
      (a := G.mulVec w) (b := G.mulVec v) (c := c) (m := m)]
    change m ⬝ᵥ G.mulVec (c • ((G.mulVec w ⬝ᵥ m) • v +
      (G.mulVec v ⬝ᵥ m) • w)) = 0
    rw [rckRPgb_form_pair (G := G) (m := m) (v := v) (w := w)
      (a := G.mulVec w) (b := G.mulVec v) (c := c)]
    have hP : (G.mulVec w) ⬝ᵥ m = m ⬝ᵥ G.mulVec w := dotProduct_comm _ _
    have hQ : (G.mulVec v) ⬝ᵥ m = m ⬝ᵥ G.mulVec v := dotProduct_comm _ _
    rw [hP, hQ]
    have hmul : c * ((m ⬝ᵥ G.mulVec w) * (m ⬝ᵥ G.mulVec v) +
        (m ⬝ᵥ G.mulVec v) * (m ⬝ᵥ G.mulVec w)) =
        (2 * c) * ((m ⬝ᵥ G.mulVec w) * (m ⬝ᵥ G.mulVec v)) := by ring
    rw [hmul]
    have h2 : (2 : F) = 0 := CharP.cast_eq_zero F 2
    simp [h2]

theorem glGeoFlag_unitTransvGroup {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) {G : Matrix ι ι F} (hG : IsUnit G.det) {v : ι → F} (hv : v ≠ 0)
    (hiso : Matrix.vecMul (fun i => σ (v i)) G ⬝ᵥ v = 0) :
    GLGeoFlag none (unitTransvGroup σ G v) := by
  have hσ : Function.Injective σ := σ.injective
  have ha : Matrix.vecMul (fun i => σ (v i)) G ≠ 0 :=
    rckRPgb_unitTransv_fun_ne_zero hσ hG hv
  refine ⟨Submodule.span F ({v} : Set (ι → F)),
    (rckRPgb_dot (Matrix.vecMul (fun i => σ (v i)) G)).ker, ?_, ?_, ?_⟩
  · rw [Submodule.span_le]
    intro y hy
    rw [Set.mem_singleton_iff] at hy
    rw [hy]
    change rckRPgb_dot (Matrix.vecMul (fun i => σ (v i)) G) v = 0
    rw [rckRPgb_dot_apply]
    exact hiso
  · rintro x hx hx1
    obtain ⟨c, hcP, hc⟩ := rckRPgb_unitTransvGroup_mem hiso |>.mp hx
    have hc0 : c ≠ 0 :=
      rckRPgb_coe_ne_one (x := x)
        (N := fun c => c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) G))
        (by simp) hc hx1
    have hsub : (x : Matrix ι ι F) - 1 =
        c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (v i)) G) := by
      rw [hc]; abel
    constructor
    · rw [hsub]
      exact rckRPgb_range_smul_vecMulVec ha hc0
    · rw [hsub]
      exact rckRPgb_ker_smul_vecMulVec hc0 hv
  · intro b hb
    simp at hb

theorem glGeoFlag_unitPairGroup {ι F : Type} [Fintype ι] [DecidableEq ι] [Field F]
    (σ : F →+* F) {G : Matrix ι ι F} (hG : IsUnit G.det) {v w : ι → F}
    (hli : LinearIndependent F ![v, w])
    (hvv : Matrix.vecMul (fun i => σ (v i)) G ⬝ᵥ v = 0)
    (hww : Matrix.vecMul (fun i => σ (w i)) G ⬝ᵥ w = 0)
    (hvw : Matrix.vecMul (fun i => σ (v i)) G ⬝ᵥ w = 0)
    (hwv : Matrix.vecMul (fun i => σ (w i)) G ⬝ᵥ v = 0) :
    GLGeoFlag none (unitPairGroup σ G v w) := by
  have hσ : Function.Injective σ := σ.injective
  refine ⟨Submodule.span F ({v, w} : Set (ι → F)),
    (rckRPgb_dot (Matrix.vecMul (fun i => σ (w i)) G)).ker ⊓
      (rckRPgb_dot (Matrix.vecMul (fun i => σ (v i)) G)).ker, ?_, ?_, ?_⟩
  · rw [Submodule.span_le]
    rintro y (hy | hy)
    · rw [hy]
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · change rckRPgb_dot (Matrix.vecMul (fun i => σ (w i)) G) v = 0
        rw [rckRPgb_dot_apply]
        exact hwv
      · change rckRPgb_dot (Matrix.vecMul (fun i => σ (v i)) G) v = 0
        rw [rckRPgb_dot_apply]
        exact hvv
    · rw [hy]
      refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
      · change rckRPgb_dot (Matrix.vecMul (fun i => σ (w i)) G) w = 0
        rw [rckRPgb_dot_apply]
        exact hww
      · change rckRPgb_dot (Matrix.vecMul (fun i => σ (v i)) G) w = 0
        rw [rckRPgb_dot_apply]
        exact hvw
  · rintro x hx hx1
    obtain ⟨c, hc⟩ := (rckRPgb_unitPairGroup_mem hvv hww hvw hwv).mp hx
    have hc0 : c ≠ 0 := by
      rintro rfl
      refine hx1 (Units.ext ?_)
      rw [hc]
      simp
    have hσc : σ c ≠ 0 := fun h0 => hc0 (hσ (by simpa using h0))
    have hsub : (x : Matrix ι ι F) - 1 =
        c • Matrix.vecMulVec v (Matrix.vecMul (fun i => σ (w i)) G) -
          σ c • Matrix.vecMulVec w (Matrix.vecMul (fun i => σ (v i)) G) := by
      rw [hc]; abel
    constructor
    · rw [hsub, sub_eq_add_neg, ← neg_smul]
      exact rckRPgb_range_pair_smul (v := v) (w := w)
        (a := Matrix.vecMul (fun i => σ (w i)) G)
        (b := Matrix.vecMul (fun i => σ (v i)) G) (α := c) (β := -σ c)
        hc0 (neg_ne_zero.mpr hσc) (rckRPgb_unitPair_minor hσ hG hli)
    · rw [hsub, sub_eq_add_neg, ← neg_smul]
      exact rckRPgb_ker_pair_smul (v := v) (w := w)
        (a := Matrix.vecMul (fun i => σ (w i)) G)
        (b := Matrix.vecMul (fun i => σ (v i)) G) (α := c) (β := -σ c)
        hc0 (neg_ne_zero.mpr hσc) hli
  · intro b hb
    simp at hb

end CFSG.StandardType.RCKRP
