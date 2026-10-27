module

public import CFSG.LocalAnalysis.ComponentInitial.LinearHigherSylowNormalizer
public import Mathlib.Data.Fin.Tuple.Sort

public section

namespace CFSG.StandardType

namespace GGLinRad

open Matrix Subgroup CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type*} [Field F] {n : ℕ}

private theorem matrix_eq_zero_of_forall_mulVec_eq_zero {N : Matrix (Fin n) (Fin n) F}
    (hN : ∀ v, N *ᵥ v = 0) : N = 0 := by
  ext i j
  have h1 := congrFun (hN (Pi.single j 1)) i
  rwa [Matrix.mulVec_single_one, col_apply] at h1

private theorem det_one_sub_of_isNilpotent_aux {N : Matrix (Fin n) (Fin n) F}
    (hN : IsNilpotent N) : (1 - N).det = 1 := by
  have h1 : N.charpoly = Polynomial.X ^ Fintype.card (Fin n) :=
    sub_eq_zero.mp (Matrix.isNilpotent_charpoly_sub_pow_of_isNilpotent hN).eq_zero
  have h2 := Matrix.eval_charpoly N 1
  rw [h1, Polynomial.eval_pow, Polynomial.eval_X, one_pow, map_one] at h2
  exact h2.symm

private theorem det_one_add_of_sq_eq_zero {N : Matrix (Fin n) (Fin n) F} (hN : N * N = 0) :
    (1 + N).det = 1 := by
  have hNil : IsNilpotent (-N) := by
    refine ⟨2, ?_⟩
    rw [pow_two, neg_mul_neg, hN]
  have h := det_one_sub_of_isNilpotent_aux hNil
  simpa using h

private theorem vecMulVec_mulVec (w ℓ v : Fin n → F) :
    Matrix.vecMulVec w ℓ *ᵥ v = (ℓ ⬝ᵥ v) • w := by
  ext i
  simp only [Matrix.mulVec_apply, Matrix.row_apply, Matrix.vecMulVec_apply, dotProduct,
    Pi.smul_apply, smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro x _
  ring

private theorem vecMulVec_mul_vecMulVec (w ℓ : Fin n → F) :
    Matrix.vecMulVec w ℓ * Matrix.vecMulVec w ℓ = (ℓ ⬝ᵥ w) • Matrix.vecMulVec w ℓ := by
  ext i j
  simp only [Matrix.mul_apply, Matrix.vecMulVec_apply, dotProduct, Matrix.smul_apply,
    smul_eq_mul]
  rw [Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro k _
  ring

private theorem dotProductEquiv_symm_apply_dotProduct (φ : (Fin n → F) →ₗ[F] F)
    (v : Fin n → F) :
    ((dotProductEquiv F (Fin n)).symm φ) ⬝ᵥ v = φ v := by
  rw [← dotProductEquiv_apply_apply]
  simp

private theorem transvection_det {W : Submodule F (Fin n → F)} {w : Fin n → F}
    (φ : (Fin n → F) →ₗ[F] F) (hw : w ∈ W) (hφ : W ≤ LinearMap.ker φ) :
    (1 + Matrix.vecMulVec w ((dotProductEquiv F (Fin n)).symm φ)).det = 1 := by
  have hsq : Matrix.vecMulVec w ((dotProductEquiv F (Fin n)).symm φ) *
      Matrix.vecMulVec w ((dotProductEquiv F (Fin n)).symm φ) = 0 := by
    rw [vecMulVec_mul_vecMulVec, dotProductEquiv_symm_apply_dotProduct,
      LinearMap.mem_ker.mp (hφ hw), zero_smul]
  exact det_one_add_of_sq_eq_zero hsq

private noncomputable def transvection {W : Submodule F (Fin n → F)} (w : Fin n → F)
    (φ : (Fin n → F) →ₗ[F] F) (hw : w ∈ W) (hφ : W ≤ LinearMap.ker φ) :
    SpecialLinearGroup (Fin n) F :=
  ⟨1 + Matrix.vecMulVec w ((dotProductEquiv F (Fin n)).symm φ), transvection_det φ hw hφ⟩

private theorem coe_transvection {W : Submodule F (Fin n → F)} {w : Fin n → F}
    (φ : (Fin n → F) →ₗ[F] F) (hw : w ∈ W) (hφ : W ≤ LinearMap.ker φ) :
    (transvection w φ hw hφ : Matrix (Fin n) (Fin n) F) =
      1 + Matrix.vecMulVec w ((dotProductEquiv F (Fin n)).symm φ) := rfl

private theorem transvection_mulVec {W : Submodule F (Fin n → F)} {w : Fin n → F}
    (φ : (Fin n → F) →ₗ[F] F) (hw : w ∈ W) (hφ : W ≤ LinearMap.ker φ) (v : Fin n → F) :
    (transvection w φ hw hφ : Matrix (Fin n) (Fin n) F) *ᵥ v = v + φ v • w := by
  rw [coe_transvection, Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec,
    dotProductEquiv_symm_apply_dotProduct]

private theorem stabilizer_mulVec_mem {W : Submodule F (Fin n → F)}
    {g : SpecialLinearGroup (Fin n) F} (hg : g ∈ stabilizer W) {w : Fin n → F} (hw : w ∈ W) :
    (g : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W := by
  have hmap : W.map (mulVecLin (g : Matrix (Fin n) (Fin n) F)) = W := mem_stabilizer.mp hg
  rw [← hmap, Submodule.mem_map]
  exact ⟨w, hw, by rw [Matrix.mulVecLin_apply]⟩

private theorem one_add_pow_eq_one_add_natCast_mul {N : Matrix (Fin n) (Fin n) F}
    (hN : N * N = 0) (k : ℕ) :
    (1 + N) ^ k = 1 + (k : Matrix (Fin n) (Fin n) F) * N := by
  induction k with
  | zero => simp
  | succ k ih =>
    rw [pow_succ, ih, Nat.cast_succ]
    calc (1 + (k : Matrix (Fin n) (Fin n) F) * N) * (1 + N)
        = 1 + N + (k : Matrix (Fin n) (Fin n) F) * N +
            (k : Matrix (Fin n) (Fin n) F) * (N * N) := by noncomm_ring
      _ = 1 + ((k : Matrix (Fin n) (Fin n) F) + 1) * N := by
            rw [hN, mul_zero, add_zero]
            noncomm_ring

@[expose] def radical (W : Submodule F (Fin n → F)) : Subgroup (SpecialLinearGroup (Fin n) F) where
  carrier := {g | (∀ w ∈ W, (g : Matrix (Fin n) (Fin n) F) *ᵥ w = w) ∧
    ∀ v, (g : Matrix (Fin n) (Fin n) F) *ᵥ v - v ∈ W}
  one_mem' := ⟨fun w _ => by rw [SpecialLinearGroup.coe_one, Matrix.one_mulVec],
    fun v => by
      rw [SpecialLinearGroup.coe_one, Matrix.one_mulVec, sub_self]
      exact W.zero_mem⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun w hw => ?_, fun v => ?_⟩
    · rw [SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec, hh1 w hw, hg1 w hw]
    · rw [SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec]
      have h1 : (h : Matrix (Fin n) (Fin n) F) *ᵥ v - v ∈ W := hh2 v
      have h2 : (g : Matrix (Fin n) (Fin n) F) *ᵥ ((h : Matrix (Fin n) (Fin n) F) *ᵥ v) -
          ((h : Matrix (Fin n) (Fin n) F) *ᵥ v) ∈ W := hg2 _
      have h3 : (g : Matrix (Fin n) (Fin n) F) *ᵥ ((h : Matrix (Fin n) (Fin n) F) *ᵥ v) - v =
          ((g : Matrix (Fin n) (Fin n) F) *ᵥ ((h : Matrix (Fin n) (Fin n) F) *ᵥ v) -
            ((h : Matrix (Fin n) (Fin n) F) *ᵥ v)) +
          ((h : Matrix (Fin n) (Fin n) F) *ᵥ v - v) := by abel
      rw [h3]
      exact W.add_mem h2 h1
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    have hfix : ∀ x ∈ W,
        ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ x = x := by
      intro x hx
      calc ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ x
          = ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ
              ((g : Matrix (Fin n) (Fin n) F) *ᵥ x) := by rw [hg1 x hx]
        _ = (((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *
              (g : Matrix (Fin n) (Fin n) F)) *ᵥ x := by rw [Matrix.mulVec_mulVec]
        _ = x := by rw [coe_inv_mul_coe, Matrix.one_mulVec]
    refine ⟨hfix, fun v => ?_⟩
    have hv : (g : Matrix (Fin n) (Fin n) F) *ᵥ v - v ∈ W := hg2 v
    have hneg : ((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ v - v =
        -(((g⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ
          ((g : Matrix (Fin n) (Fin n) F) *ᵥ v - v)) := by
      rw [Matrix.mulVec_sub]
      rw [Matrix.mulVec_mulVec, coe_inv_mul_coe, Matrix.one_mulVec]
      abel
    rw [hneg, hfix _ hv]
    exact W.neg_mem hv

theorem mem_radical {W : Submodule F (Fin n → F)} {g : SpecialLinearGroup (Fin n) F} :
    g ∈ radical W ↔ (∀ w ∈ W, (g : Matrix (Fin n) (Fin n) F) *ᵥ w = w) ∧
      ∀ v, (g : Matrix (Fin n) (Fin n) F) *ᵥ v - v ∈ W :=
  Iff.rfl

private theorem transvection_mem_radical {W : Submodule F (Fin n → F)} {w : Fin n → F}
    (hw : w ∈ W) (φ : (Fin n → F) →ₗ[F] F) (hφ : W ≤ LinearMap.ker φ) :
    transvection w φ hw hφ ∈ radical W := by
  refine mem_radical.mpr ⟨?_, ?_⟩
  · intro w' hw'
    rw [coe_transvection, Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec,
      dotProductEquiv_symm_apply_dotProduct, LinearMap.mem_ker.mp (hφ hw'), zero_smul, add_zero]
  · intro v
    rw [coe_transvection, Matrix.add_mulVec, Matrix.one_mulVec, vecMulVec_mulVec,
      dotProductEquiv_symm_apply_dotProduct]
    have h : v + φ v • w - v = φ v • w := by abel
    rw [h]
    exact W.smul_mem _ hw

theorem radical_le_stabilizer (W : Submodule F (Fin n → F)) : radical W ≤ stabilizer W := by
  intro g hg
  rw [mem_stabilizer]
  refine le_antisymm ?_ ?_
  · rintro _ ⟨w, hw, rfl⟩
    rw [Matrix.mulVecLin_apply, (mem_radical.mp hg).1 w hw]
    exact hw
  · intro w hw
    exact ⟨w, hw, by rw [Matrix.mulVecLin_apply, (mem_radical.mp hg).1 w hw]⟩

private theorem radical_conj_mem {W : Submodule F (Fin n → F)}
    {s u : SpecialLinearGroup (Fin n) F} (hs : s ∈ stabilizer W) (hu : u ∈ radical W) :
    s * u * s⁻¹ ∈ radical W := by
  obtain ⟨hu1, hu2⟩ := mem_radical.mp hu
  have hsinv : s⁻¹ ∈ stabilizer W := (stabilizer W).inv_mem hs
  refine mem_radical.mpr ⟨?_, ?_⟩
  · intro w hw
    have h1 : (↑(s⁻¹) : Matrix (Fin n) (Fin n) F) *ᵥ w ∈ W := stabilizer_mulVec_mem hsinv hw
    have h2 : (↑u : Matrix (Fin n) (Fin n) F) *ᵥ
        ((↑(s⁻¹) : Matrix (Fin n) (Fin n) F) *ᵥ w) =
        (↑(s⁻¹) : Matrix (Fin n) (Fin n) F) *ᵥ w := hu1 _ h1
    have h3 : (↑s : Matrix (Fin n) (Fin n) F) *ᵥ
        ((↑(s⁻¹) : Matrix (Fin n) (Fin n) F) *ᵥ w) = w := by
      rw [Matrix.mulVec_mulVec, ← SpecialLinearGroup.coe_mul, mul_inv_cancel,
        SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    rw [SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul, ← Matrix.mulVec_mulVec,
      ← Matrix.mulVec_mulVec, h2, h3]
  · intro v
    have hw : (↑u : Matrix (Fin n) (Fin n) F) *ᵥ
        ((↑(s⁻¹) : Matrix (Fin n) (Fin n) F) *ᵥ v) -
        (↑(s⁻¹) : Matrix (Fin n) (Fin n) F) *ᵥ v ∈ W := hu2 _
    have hg : (↑s : Matrix (Fin n) (Fin n) F) *ᵥ
        ((↑u : Matrix (Fin n) (Fin n) F) *ᵥ ((↑(s⁻¹) : Matrix (Fin n) (Fin n) F) *ᵥ v) -
          (↑(s⁻¹) : Matrix (Fin n) (Fin n) F) *ᵥ v) ∈ W := stabilizer_mulVec_mem hs hw
    have hAx : (↑s : Matrix (Fin n) (Fin n) F) *ᵥ
        ((↑(s⁻¹) : Matrix (Fin n) (Fin n) F) *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, ← SpecialLinearGroup.coe_mul, mul_inv_cancel,
        SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    have heq : (s * u * s⁻¹) *ᵥ v - v =
        (↑s : Matrix (Fin n) (Fin n) F) *ᵥ
          ((↑u : Matrix (Fin n) (Fin n) F) *ᵥ ((↑(s⁻¹) : Matrix (Fin n) (Fin n) F) *ᵥ v) -
            (↑(s⁻¹) : Matrix (Fin n) (Fin n) F) *ᵥ v) := by
      rw [Matrix.mulVec_sub, SpecialLinearGroup.coe_mul, SpecialLinearGroup.coe_mul,
        ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, hAx]
    rw [heq]
    exact hg

theorem radical_normal (W : Submodule F (Fin n → F)) :
    ((radical W).subgroupOf (stabilizer W)).Normal := by
  refine ⟨fun u hu g => ?_⟩
  rw [Subgroup.mem_subgroupOf] at hu ⊢
  have hcoe : ((g * u * g⁻¹ : stabilizer W) : SpecialLinearGroup (Fin n) F) =
      (g : SpecialLinearGroup (Fin n) F) * (u : SpecialLinearGroup (Fin n) F) *
        ((g : SpecialLinearGroup (Fin n) F))⁻¹ := by
    simp [Subgroup.coe_mul, Subgroup.coe_inv]
  rw [hcoe]
  exact radical_conj_mem g.2 hu

theorem isPGroup_radical (p : ℕ) [Fact p.Prime] [CharP F p] (W : Submodule F (Fin n → F)) :
    IsPGroup p (radical W) := by
  rw [isPGroup_iff_pow_pow_eq_one]
  intro g
  refine ⟨1, ?_⟩
  have hgp : (g : SpecialLinearGroup (Fin n) F) ^ p = 1 := by
    obtain ⟨hg1, hg2⟩ := mem_radical.mp g.2
    set N : Matrix (Fin n) (Fin n) F := (g : Matrix (Fin n) (Fin n) F) - 1 with hN
    have hNkill : ∀ w ∈ W, N *ᵥ w = 0 := by
      intro w hw
      rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec, hg1 w hw, sub_self]
    have hNmem : ∀ v, N *ᵥ v ∈ W := by
      intro v
      rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec]
      exact hg2 v
    have hN2 : N * N = 0 := by
      refine matrix_eq_zero_of_forall_mulVec_eq_zero fun v => ?_
      rw [← Matrix.mulVec_mulVec]
      exact hNkill _ (hNmem v)
    have hp0 : (p : Matrix (Fin n) (Fin n) F) = 0 := by
      rw [← Matrix.diagonal_natCast (m := p), CharP.cast_eq_zero F p]
      simp
    apply Subtype.ext
    rw [SpecialLinearGroup.coe_pow]
    have h1 : (g : Matrix (Fin n) (Fin n) F) = 1 + N := by rw [hN]; abel
    rw [h1, one_add_pow_eq_one_add_natCast_mul hN2 p, hp0, zero_mul, add_zero,
      SpecialLinearGroup.coe_one]
  have : g ^ p = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hgp, Subgroup.coe_one]
  simpa using this

private theorem star_commute {W : Submodule F (Fin n → F)} (h0 : ⊥ < W)
    {s : SpecialLinearGroup (Fin n) F} (hs : s ∈ stabilizer W)
    (hc : ∀ u ∈ radical W, s * u * s⁻¹ * u⁻¹ ∈ scalars n F)
    {w : Fin n → F} (hw : w ∈ W) (φ : (Fin n → F) →ₗ[F] F) (hφ : W ≤ LinearMap.ker φ)
    (v : Fin n → F) :
    φ v • ((s : Matrix (Fin n) (Fin n) F) *ᵥ w) =
      φ ((s : Matrix (Fin n) (Fin n) F) *ᵥ v) • w := by
  let t : SpecialLinearGroup (Fin n) F := transvection w φ hw hφ
  have ht : t ∈ radical W := transvection_mem_radical hw φ hφ
  obtain ⟨c, _, hzc⟩ := mem_scalars.mp (hc t ht)
  obtain ⟨w₀, hw₀, hw₀_ne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (ne_of_gt h0)
  have htinv : t⁻¹ ∈ radical W := (radical W).inv_mem ht
  have hfit : ∀ (u : SpecialLinearGroup (Fin n) F), u ∈ radical W →
      ∀ w ∈ W, (u : Matrix (Fin n) (Fin n) F) *ᵥ w = w :=
    fun u hu w hw => (mem_radical.mp hu).1 w hw
  have hZw₀ : ((s * t * s⁻¹ * t⁻¹ : SpecialLinearGroup (Fin n) F) :
      Matrix (Fin n) (Fin n) F) *ᵥ w₀ = w₀ := by
    have h1 : (↑(t⁻¹) : Matrix (Fin n) (Fin n) F) *ᵥ w₀ = w₀ := hfit t⁻¹ htinv w₀ hw₀
    have h2 : (↑(s⁻¹) : Matrix (Fin n) (Fin n) F) *ᵥ w₀ ∈ W :=
      stabilizer_mulVec_mem ((stabilizer W).inv_mem hs) hw₀
    have h3 : (↑t : Matrix (Fin n) (Fin n) F) *ᵥ ((↑(s⁻¹) : Matrix (Fin n) (Fin n) F) *ᵥ w₀) =
        (↑(s⁻¹) : Matrix (Fin n) (Fin n) F) *ᵥ w₀ := hfit t ht _ h2
    have h4 : (↑s : Matrix (Fin n) (Fin n) F) *ᵥ
        ((↑(s⁻¹) : Matrix (Fin n) (Fin n) F) *ᵥ w₀) = w₀ := by
      rw [Matrix.mulVec_mulVec, ← SpecialLinearGroup.coe_mul, mul_inv_cancel,
        SpecialLinearGroup.coe_one, Matrix.one_mulVec]
    simp only [SpecialLinearGroup.coe_mul]
    rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec]
    rw [h1, h3, h4]
  have hc1F : (c : F) = 1 := by
    have h1 : ((s * t * s⁻¹ * t⁻¹ : SpecialLinearGroup (Fin n) F) :
        Matrix (Fin n) (Fin n) F) *ᵥ w₀ = (c : F) • w₀ := by
      rw [hzc, Matrix.scalar_apply, Matrix.diagonal_const_mulVec]
    apply smul_left_injective F hw₀_ne
    change (c : F) • w₀ = (1 : F) • w₀
    rw [← h1, hZw₀, one_smul]
  have hc1 : c = 1 := Units.ext hc1F
  have hz1 : (s * t * s⁻¹ * t⁻¹ : SpecialLinearGroup (Fin n) F) = 1 := by
    apply Subtype.ext
    rw [hzc, hc1]
    simp
  have hst1 : s * t * s⁻¹ = t := by
    have := congrArg (· * t) hz1
    simpa [mul_assoc] using this
  have hst : s * t = t * s := by
    have := congrArg (· * s) hst1
    simpa [mul_assoc] using this
  have hST : (s : Matrix (Fin n) (Fin n) F) * (t : Matrix (Fin n) (Fin n) F) =
      (t : Matrix (Fin n) (Fin n) F) * (s : Matrix (Fin n) (Fin n) F) := by
    rw [← SpecialLinearGroup.coe_mul, ← SpecialLinearGroup.coe_mul, hst]
  have hA : ((s : Matrix (Fin n) (Fin n) F) * (t : Matrix (Fin n) (Fin n) F)) *ᵥ v =
      (s : Matrix (Fin n) (Fin n) F) *ᵥ v +
        φ v • ((s : Matrix (Fin n) (Fin n) F) *ᵥ w) := by
    dsimp only [t]
    rw [← Matrix.mulVec_mulVec, transvection_mulVec, Matrix.mulVec_add, Matrix.mulVec_smul]
  have hB : ((t : Matrix (Fin n) (Fin n) F) * (s : Matrix (Fin n) (Fin n) F)) *ᵥ v =
      (s : Matrix (Fin n) (Fin n) F) *ᵥ v +
        φ ((s : Matrix (Fin n) (Fin n) F) *ᵥ v) • w := by
    dsimp only [t]
    rw [← Matrix.mulVec_mulVec, transvection_mulVec]
  have hAB : (s : Matrix (Fin n) (Fin n) F) *ᵥ v +
        φ v • ((s : Matrix (Fin n) (Fin n) F) *ᵥ w) =
      (s : Matrix (Fin n) (Fin n) F) *ᵥ v +
        φ ((s : Matrix (Fin n) (Fin n) F) *ᵥ v) • w := by
    rw [← hA, hST, hB]
  exact add_left_cancel hAB

theorem exists_scalar_mul_mem_radical {W : Submodule F (Fin n → F)} (h0 : ⊥ < W) (htop : W < ⊤)
    {s : SpecialLinearGroup (Fin n) F} (hs : s ∈ stabilizer W)
    (hc : ∀ u ∈ radical W, s * u * s⁻¹ * u⁻¹ ∈ scalars n F) :
    ∃ z ∈ scalars n F, ∃ q ∈ radical W, s = z * q := by
  obtain ⟨w₀, hw₀, hw₀_ne⟩ :=
    Submodule.exists_mem_ne_zero_of_ne_bot (ne_of_gt h0)
  set S : Matrix (Fin n) (Fin n) F := (s : Matrix (Fin n) (Fin n) F) with hS
  obtain ⟨φ₀, hφ₀_ne, hφ₀W⟩ := Submodule.exists_le_ker_of_lt_top W htop
  obtain ⟨v₀, hv₀⟩ : ∃ v, φ₀ v ≠ 0 := by
    by_contra h
    push Not at h
    exact hφ₀_ne (LinearMap.ext fun v => h v)
  set μ : F := φ₀ (S *ᵥ v₀) / φ₀ v₀ with hμ
  have hμw : ∀ w ∈ W, S *ᵥ w = μ • w := by
    intro w hw
    have h := star_commute h0 hs hc hw φ₀ hφ₀W v₀
    rw [← hS] at h
    have h' := congrArg (fun x : Fin n → F => (φ₀ v₀)⁻¹ • x) h
    simp only [smul_smul, inv_mul_cancel₀ hv₀, one_smul] at h'
    rw [hμ, div_eq_inv_mul]
    exact h'
  have hμ_ne : μ ≠ 0 := by
    intro hμ0
    have hS0 : S *ᵥ w₀ = 0 := by rw [hμw w₀ hw₀, hμ0, zero_smul]
    have hfix_inv : ((s⁻¹ : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) *ᵥ
        (S *ᵥ w₀) = w₀ := by
      rw [hS, Matrix.mulVec_mulVec, coe_inv_mul_coe, Matrix.one_mulVec]
    have : w₀ = 0 := by rw [← hfix_inv, hS0, Matrix.mulVec_zero]
    exact hw₀_ne this
  have hφS : ∀ (φ : (Fin n → F) →ₗ[F] F), W ≤ LinearMap.ker φ → ∀ v,
      φ (S *ᵥ v) = μ * φ v := by
    intro φ hφ v
    have h := star_commute h0 hs hc hw₀ φ hφ v
    rw [← hS] at h
    rw [hμw w₀ hw₀, smul_smul] at h
    have h2 : φ v * μ = φ (S *ᵥ v) := smul_left_injective F hw₀_ne h
    exact h2.symm.trans (mul_comm _ _)
  have hSW : ∀ v, S *ᵥ v - μ • v ∈ W := by
    intro v
    by_contra hv
    obtain ⟨φ, hφv, hφW⟩ := Submodule.exists_le_ker_of_notMem hv
    exact hφv (by
      rw [map_sub, map_smul, hφS φ hφW v, smul_eq_mul, sub_self])
  set R : Matrix (Fin n) (Fin n) F := μ⁻¹ • S with hR
  have hR_fix : ∀ w ∈ W, R *ᵥ w = w := by
    intro w hw
    rw [hR, Matrix.smul_mulVec, hμw w hw, smul_smul, inv_mul_cancel₀ hμ_ne, one_smul]
  have hR_sub : ∀ v, R *ᵥ v - v ∈ W := by
    intro v
    rw [hR, Matrix.smul_mulVec]
    have h : μ⁻¹ • (S *ᵥ v) - v = μ⁻¹ • (S *ᵥ v - μ • v) := by
      rw [smul_sub, smul_smul, inv_mul_cancel₀ hμ_ne, one_smul]
    rw [h]
    exact W.smul_mem _ (hSW v)
  set N : Matrix (Fin n) (Fin n) F := R - 1 with hN
  have hNkill : ∀ w ∈ W, N *ᵥ w = 0 := by
    intro w hw
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec, hR_fix w hw, sub_self]
  have hNmem : ∀ v, N *ᵥ v ∈ W := by
    intro v
    rw [hN, Matrix.sub_mulVec, Matrix.one_mulVec]
    exact hR_sub v
  have hN2 : N * N = 0 := by
    refine matrix_eq_zero_of_forall_mulVec_eq_zero fun v => ?_
    rw [← Matrix.mulVec_mulVec]
    exact hNkill _ (hNmem v)
  have hRN : R = 1 + N := by rw [hN]; abel
  have hdetR : R.det = 1 := by rw [hRN]; exact det_one_add_of_sq_eq_zero hN2
  have hdetR' : R.det = (μ⁻¹) ^ n := by
    rw [hR, Matrix.det_smul, Fintype.card_fin, hS, s.2, mul_one]
  have hμn : μ ^ n = 1 := by
    have h : (μ⁻¹) ^ n = 1 := by rw [← hdetR', hdetR]
    rwa [inv_pow, inv_eq_one] at h
  let q : SpecialLinearGroup (Fin n) F := ⟨R, hdetR⟩
  have hq : q ∈ radical W := by
    refine mem_radical.mpr ⟨?_, ?_⟩
    · intro w hw
      change R *ᵥ w = w
      exact hR_fix w hw
    · intro v
      change R *ᵥ v - v ∈ W
      exact hR_sub v
  let c : Fˣ := Units.mk0 μ hμ_ne
  have hc_n : c ^ n = 1 := by
    apply Units.ext
    rw [Units.val_pow_eq_pow_val, Units.val_mk0, hμn, Units.val_one]
  let z : SpecialLinearGroup (Fin n) F := scalarElement c hc_n
  refine ⟨z, scalarElement_mem_scalars c hc_n, q, hq, ?_⟩
  apply Subtype.ext
  rw [SpecialLinearGroup.coe_mul]
  change (s : Matrix (Fin n) (Fin n) F) =
    (scalarElement c hc_n : Matrix (Fin n) (Fin n) F) * (q : Matrix (Fin n) (Fin n) F)
  rw [coe_scalarElement, Units.val_mk0]
  change (s : Matrix (Fin n) (Fin n) F) = Matrix.scalar (Fin n) μ * R
  rw [Matrix.scalar_apply, hR, ← Matrix.smul_eq_diagonal_mul, smul_smul,
    mul_inv_cancel₀ hμ_ne, one_smul, hS]

end GGLinRad

end CFSG.StandardType
