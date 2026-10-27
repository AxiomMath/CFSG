module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeM3RSDefs

public section

namespace CFSG.StandardType.RCKRP

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem CFSG.StandardType
  CFSG.StandardType.S2MathFi1035Pos CFSG.StandardType.RCKC1 CFSG.StandardType.ClassicalPosition
open CFSG.Open (StatedLieTag)

theorem rckBlockRS_flag
    {m g k : ℕ} {e : Matrix (Fin (m + 1)) (Fin (m + 1)) (GaloisField 2 g)} (hee : e * e = e)
    {K : Type} [Field K] [Algebra (GaloisField 2 g) K] [Module K (LinearMap.range (Matrix.mulVecLin e))] [IsScalarTower (GaloisField 2 g) K (LinearMap.range (Matrix.mulVecLin e))]
    (b : Module.Basis (Fin (k + 1)) K (LinearMap.range (Matrix.mulVecLin e))) {i j : Fin (k + 1)} (hij : i ≠ j) :
    ∃ W' H' : Submodule (GaloisField 2 g) (Fin (m + 1) → GaloisField 2 g), W' ≤ H' ∧ ∀ t : K, t ≠ 0 →
      LinearMap.range (Matrix.toLin' (rckBlockRSMat b (Matrix.transvection i j t) - 1)) = W' ∧
      LinearMap.ker (Matrix.toLin' (rckBlockRSMat b (Matrix.transvection i j t) - 1)) = H' := by
  let A : (Fin (m + 1) → GaloisField 2 g) →ₗ[GaloisField 2 g] (Fin (m + 1) → GaloisField 2 g) :=
    Matrix.mulVecLin e
  let W := LinearMap.range A
  let c : (Fin (m + 1) → GaloisField 2 g) →ₗ[GaloisField 2 g] K :=
    ((b.coord j).restrictScalars (GaloisField 2 g)) ∘ₗ A.rangeRestrict
  have hAA : A.comp A = A := by
    show (Matrix.mulVecLin e).comp (Matrix.mulVecLin e) = Matrix.mulVecLin e
    rw [← Matrix.mulVecLin_mul, hee]
  have hAfix : ∀ w : W, A (w : Fin (m + 1) → GaloisField 2 g) = (w : Fin (m + 1) → GaloisField 2 g) := by
    intro w
    obtain ⟨u, hu⟩ := w.2
    rw [← hu, ← LinearMap.comp_apply, hAA]
  have hsub : ∀ v : Fin (m + 1) → GaloisField 2 g, W.subtype (A.rangeRestrict v) = A v := fun _ => rfl
  have hrangeRestrict : ∀ (a : K) (l : Fin (k + 1)),
      A.rangeRestrict (W.subtype (a • b l)) = (a • b l : W) := by
    intro a l
    apply Subtype.ext
    change A ((a • b l : W) : Fin (m + 1) → GaloisField 2 g)
      = ((a • b l : W) : Fin (m + 1) → GaloisField 2 g)
    rw [hAfix (a • b l)]
  have hc_surj : Function.Surjective c := by
    intro a
    refine ⟨W.subtype (a • b j), ?_⟩
    show b.coord j (A.rangeRestrict (W.subtype (a • b j))) = a
    rw [hrangeRestrict a j]
    change b.coord j (a • b j) = a
    rw [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_pos rfl, smul_eq_mul, mul_one]
  refine ⟨((K ∙ b i).restrictScalars (GaloisField 2 g)).map W.subtype, c.ker, ?_, ?_⟩
  · rintro x ⟨y, hy, rfl⟩
    have hy' : y ∈ K ∙ b i := by simpa using hy
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy'
    rw [LinearMap.mem_ker]
    show b.coord j (A.rangeRestrict (W.subtype (a • b i))) = 0
    rw [hrangeRestrict a i]
    change b.coord j (a • b i) = 0
    rw [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_neg hij, smul_eq_mul, mul_zero]
  · intro t ht
    have hsingle : Matrix.toLin b b (Matrix.single i j t) = (b.coord j).smulRight (t • b i) := by
      have hmat : Matrix.single i j t = Matrix.vecMulVec (b.repr (t • b i)) (b.coord j ∘ b) := by
        ext i' l
        by_cases hi : i = i' <;> by_cases hj : j = l <;>
          simp_all [Matrix.single_apply, Matrix.vecMulVec_apply, Module.Basis.coord_apply,
            Module.Basis.repr_self, map_smul, Finsupp.smul_apply, Finsupp.single_apply]
      rw [← Matrix.toLin_toMatrix b b ((b.coord j).smulRight (t • b i)),
        LinearMap.toMatrix_smulRight, hmat]
    have hfv : ∀ v : Fin (m + 1) → GaloisField 2 g,
        (Matrix.toLin b b (Matrix.transvection i j t)).restrictScalars (GaloisField 2 g) (A.rangeRestrict v)
          = A.rangeRestrict v + ((b.repr (A.rangeRestrict v)) j * t) • b i := by
      intro v
      change Matrix.toLin b b (Matrix.transvection i j t) (A.rangeRestrict v)
          = A.rangeRestrict v + ((b.repr (A.rangeRestrict v)) j * t) • b i
      rw [Matrix.transvection, map_add, Matrix.toLin_one,
        hsingle, LinearMap.add_apply, LinearMap.id_apply, LinearMap.smulRight_apply,
        Module.Basis.coord_apply, smul_smul]
    have hMv : ∀ v : Fin (m + 1) → GaloisField 2 g,
        Matrix.toLin' (rckBlockRSMat b (Matrix.transvection i j t)) v =
          (v - A v) + W.subtype ((Matrix.toLin b b (Matrix.transvection i j t)).restrictScalars (GaloisField 2 g) (A.rangeRestrict v)) := by
      intro v
      rw [rckBlockRSMat, Matrix.toLin'_toMatrix']
      rfl
    have hLv : ∀ v : Fin (m + 1) → GaloisField 2 g,
        Matrix.toLin' (rckBlockRSMat b (Matrix.transvection i j t) - 1) v = W.subtype ((t * c v) • b i) := by
      intro v
      have h1 : Matrix.toLin' (rckBlockRSMat b (Matrix.transvection i j t) - 1) v
          = Matrix.toLin' (rckBlockRSMat b (Matrix.transvection i j t)) v - v := by
        rw [Matrix.toLin'_apply, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.toLin'_apply]
      rw [h1, hMv v, hfv v, map_add, hsub v]
      have hcv : c v = b.repr (A.rangeRestrict v) j := by
        change b.coord j (A.rangeRestrict v) = b.repr (A.rangeRestrict v) j
        rw [Module.Basis.coord_apply]
      have hscalar : b.repr (A.rangeRestrict v) j * t = t * c v := by
        rw [hcv, mul_comm]
      rw [hscalar]
      abel
    constructor
    · apply le_antisymm
      · rintro x ⟨v, rfl⟩
        exact Submodule.mem_map.mpr ⟨(t * c v) • b i,
          Submodule.mem_span_singleton.mpr ⟨t * c v, rfl⟩,
          (hLv v).symm⟩
      · rintro x ⟨y, hy, rfl⟩
        have hy' : y ∈ K ∙ b i := by simpa using hy
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy'
        refine ⟨W.subtype ((t⁻¹ * a) • b j), ?_⟩
        rw [hLv]
        have hcv : c (W.subtype ((t⁻¹ * a) • b j)) = t⁻¹ * a := by
          show b.coord j (A.rangeRestrict (W.subtype ((t⁻¹ * a) • b j))) = t⁻¹ * a
          rw [hrangeRestrict (t⁻¹ * a) j]
          change b.coord j ((t⁻¹ * a) • b j) = t⁻¹ * a
          rw [map_smul, Module.Basis.coord_apply, Module.Basis.repr_self_apply, if_pos rfl, smul_eq_mul, mul_one]
        have hsc : t * (t⁻¹ * a) = a := by rw [← mul_assoc, mul_inv_cancel₀ ht, one_mul]
        rw [hcv, hsc]
    · apply le_antisymm
      · intro v hv
        rw [LinearMap.mem_ker] at hv ⊢
        rw [hLv] at hv
        have hzero : (t * c v) • b i = 0 := by
          apply Subtype.ext
          simpa using hv
        rcases smul_eq_zero.mp hzero with h | h
        · rcases mul_eq_zero.mp h with h0 | h0
          · exact absurd h0 ht
          · exact h0
        · exact absurd h (b.ne_zero i)
      · intro v hv
        rw [LinearMap.mem_ker] at hv ⊢
        rw [hLv, hv]
        simp

end CFSG.StandardType.RCKRP
