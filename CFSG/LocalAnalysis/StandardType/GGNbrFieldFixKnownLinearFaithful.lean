module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQMat
public import CFSG.LocalAnalysis.GLTheoremA.CatA.FQLin
public import CFSG.LocalAnalysis.StandardType.GGTableBTypeATransport

public section

namespace CFSG.StandardType.LinearFieldFix

open CFSG.Assembly CFSG.LocalAnalysis.GLTheoremA CFSG.LocalAnalysis.GLTheoremA.YS09Field
  CFSG.LocalAnalysis.GLTheoremA.FQ

variable {d : ℕ} {K : Type} [Field K]

theorem eq_one_of_mk_matAct_eq (hd : 2 ≤ d)
    (hH : ∀ σ : K ≃+* K, ∀ h ∈ LargeEvenSLGroup (Fin d) K,
      Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ LargeEvenSLGroup (Fin d) K) {σ : K ≃+* K}
    (h : ∀ x : LargeEvenSLGroup (Fin d) K,
      (QuotientGroup.mk (matAct (LargeEvenSLGroup (Fin d) K) hH σ x) :
        LargeEvenProj (LargeEvenSLGroup (Fin d) K)) = QuotientGroup.mk x) :
    σ = 1 := by
  have hfix : ∀ t : K, σ t = t := by
    intro t
    let i : Fin d := ⟨0, by omega⟩
    let j : Fin d := ⟨1, by omega⟩
    have hij : i ≠ j := by
      intro h'
      have h2 : (0 : ℕ) = 1 := by simpa [i, j] using congrArg Fin.val h'
      exact Nat.zero_ne_one h2
    let x : ↥(LargeEvenSLGroup (Fin d) K) :=
      (TypeA.slKerEquiv d K).symm (Matrix.SpecialLinearGroup.transvection hij t)
    have hx : ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) = 1 + Matrix.single i j t := by
      have h1 : (TypeA.slKerEquiv d K) x = Matrix.SpecialLinearGroup.transvection hij t := by
        simp only [x, MulEquiv.apply_symm_apply]
      have h2 := TypeA.coe_slKerEquiv (d := d) (K := K) x
      rw [h1] at h2
      rw [← h2, Matrix.SpecialLinearGroup.transvection_coe]
    have hAx : (((matAct (LargeEvenSLGroup (Fin d) K) hH σ x :
          ↥(LargeEvenSLGroup (Fin d) K)) : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        1 + Matrix.single i j (σ t) := by
      rw [matAct_coe, coe_glMap, hx,
        Matrix.map_add (⇑σ.toRingHom) (fun a b => map_add σ.toRingHom a b),
        Matrix.map_one (⇑σ.toRingHom) (map_zero σ.toRingHom) (map_one σ.toRingHom)]
      simp
    have hxq : (matAct (LargeEvenSLGroup (Fin d) K) hH σ x)⁻¹ * x ∈
        (LargeEvenScalars (Fin d) K).subgroupOf (LargeEvenSLGroup (Fin d) K) :=
      QuotientGroup.eq.mp (h x)
    have hscal : (((matAct (LargeEvenSLGroup (Fin d) K) hH σ x)⁻¹ * x :
        ↥(LargeEvenSLGroup (Fin d) K)) : GL (Fin d) K) ∈ LargeEvenScalars (Fin d) K :=
      Subgroup.mem_subgroupOf.mp hxq
    rw [largeEvenScalars_def] at hscal
    obtain ⟨c, hc⟩ := hscal
    have hm : ((matAct (LargeEvenSLGroup (Fin d) K) hH σ x :
          ↥(LargeEvenSLGroup (Fin d) K)) : GL (Fin d) K) *
          ((((matAct (LargeEvenSLGroup (Fin d) K) hH σ x)⁻¹ * x :
          ↥(LargeEvenSLGroup (Fin d) K)) : GL (Fin d) K)) =
        ((x : ↥(LargeEvenSLGroup (Fin d) K)) : GL (Fin d) K) := by
      have h1 : ((matAct (LargeEvenSLGroup (Fin d) K) hH σ x :
            ↥(LargeEvenSLGroup (Fin d) K)) : GL (Fin d) K) *
            ((((matAct (LargeEvenSLGroup (Fin d) K) hH σ x)⁻¹ * x :
            ↥(LargeEvenSLGroup (Fin d) K)) : GL (Fin d) K)) =
          (((matAct (LargeEvenSLGroup (Fin d) K) hH σ x) *
            ((matAct (LargeEvenSLGroup (Fin d) K) hH σ x)⁻¹ * x) :
            ↥(LargeEvenSLGroup (Fin d) K)) : GL (Fin d) K) := rfl
      rw [h1, mul_inv_cancel_left]
    have hprod : ((x : ↥(LargeEvenSLGroup (Fin d) K)) : GL (Fin d) K) =
        ((matAct (LargeEvenSLGroup (Fin d) K) hH σ x :
          ↥(LargeEvenSLGroup (Fin d) K)) : GL (Fin d) K) *
          Matrix.GeneralLinearGroup.scalar (Fin d) c := by
      rw [hc]
      exact hm.symm
    have hmatmul : ((x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K) =
        (((matAct (LargeEvenSLGroup (Fin d) K) hH σ x :
          ↥(LargeEvenSLGroup (Fin d) K)) : GL (Fin d) K) :
          Matrix (Fin d) (Fin d) K) * Matrix.scalar (Fin d) (c : K) := by
      have h2 := congrArg (fun g : GL (Fin d) K => (g : Matrix (Fin d) (Fin d) K)) hprod
      simpa [Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar] using h2
    have hLii : (1 + Matrix.single i j t) i i = 1 := by
      simp [Matrix.one_apply, Matrix.single_apply, hij, hij.symm]
    have hRii : (1 + Matrix.single i j (σ t)) i i = 1 := by
      simp [Matrix.one_apply, Matrix.single_apply, hij, hij.symm]
    have hLij : (1 + Matrix.single i j t) i j = t := by
      simp [Matrix.one_apply, Matrix.single_apply, hij, hij.symm]
    have hRij : (1 + Matrix.single i j (σ t)) i j = σ t := by
      simp [Matrix.one_apply, Matrix.single_apply, hij, hij.symm]
    have h_c : (c : K) = 1 := by
      have hh := congrArg (fun M : Matrix (Fin d) (Fin d) K => M i i) hmatmul
      rw [hx, hAx, Matrix.scalar_apply, Matrix.mul_diagonal, hLii, hRii, one_mul] at hh
      exact hh.symm
    have hijc : t = (σ t) * (c : K) := by
      have hh := congrArg (fun M : Matrix (Fin d) (Fin d) K => M i j) hmatmul
      rw [hx, hAx, Matrix.scalar_apply, Matrix.mul_diagonal, hLij, hRij] at hh
      exact hh
    rw [h_c, mul_one] at hijc
    exact hijc.symm
  apply RingEquiv.ext
  intro t
  simpa using hfix t

theorem orderOf_eq_of_mk_matAct (hd : 2 ≤ d)
    (hH : ∀ σ : K ≃+* K, ∀ h ∈ LargeEvenSLGroup (Fin d) K,
      Matrix.GeneralLinearGroup.map σ.toRingHom h ∈ LargeEvenSLGroup (Fin d) K) {σ : K ≃+* K}
    {f : MulAut (LargeEvenProj (LargeEvenSLGroup (Fin d) K))}
    (hf : ∀ x : LargeEvenSLGroup (Fin d) K,
      f (QuotientGroup.mk x) = QuotientGroup.mk (matAct (LargeEvenSLGroup (Fin d) K) hH σ x)) :
    orderOf σ = orderOf f := by
  have key : ∀ n : ℕ, ∀ x : ↥(LargeEvenSLGroup (Fin d) K),
      (f ^ n) (QuotientGroup.mk x) =
        QuotientGroup.mk ((matAct (LargeEvenSLGroup (Fin d) K) hH) (σ ^ n) x) := by
    intro n
    induction n with
    | zero =>
        intro x
        simp only [pow_zero, map_one, MulAut.one_apply]
    | succ n ih =>
        intro x
        rw [pow_succ' f n, MulAut.mul_apply, ih x,
          hf (matAct (LargeEvenSLGroup (Fin d) K) hH (σ ^ n) x), pow_succ' σ n,
          map_mul (matAct (LargeEvenSLGroup (Fin d) K) hH) σ (σ ^ n), MulAut.mul_apply]
  refine (orderOf_eq_orderOf_iff (x := σ) (y := f)).mpr fun n => ⟨?_, ?_⟩
  · intro hσ
    have hmat1 : (matAct (LargeEvenSLGroup (Fin d) K) hH) (σ ^ n) = 1 := by
      rw [hσ, map_one]
    apply MulEquiv.ext
    intro y
    obtain ⟨x, rfl⟩ := QuotientGroup.mk_surjective y
    rw [key n x, hmat1, MulAut.one_apply, MulAut.one_apply]
  · intro hf1
    refine eq_one_of_mk_matAct_eq hd hH (σ := σ ^ n) fun x => ?_
    have hh := key n x
    rw [hf1, MulAut.one_apply] at hh
    exact hh.symm

end CFSG.StandardType.LinearFieldFix

end
