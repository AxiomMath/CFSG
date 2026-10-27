module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuModels
public import CFSG.Quasithin.Background.JonesParshallSymplecticBinary
public import CFSG.Quasithin.Background.F918D0

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Matrix CFSG.Quasithin CFSG.Quasithin.JonesParshall CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

private def s16sm_form : LinearMap.BilinForm (ZMod 2) (Fin 6 → ZMod 2) :=
  Matrix.toBilin' gramJ

private theorem s16sm_gramJ_diag (j : Fin 6) : gramJ j j = 0 := by
  fin_cases j <;> decide

private theorem s16sm_gramJ_symm (j l : Fin 6) : gramJ j l = gramJ l j := by
  fin_cases j <;> fin_cases l <;> decide

private theorem s16sm_B_alt : s16sm_form.IsAlt := by
  change (Matrix.toBilin' gramJ).IsAlt
  intro v
  let U : Matrix (Fin 6) (Fin 6) (ZMod 2) :=
    Matrix.of fun j l => if j < l then gramJ j l else 0
  have hN : gramJ = U - Uᵀ := by
    ext j l
    simp only [U, Matrix.sub_apply, Matrix.transpose_apply, Matrix.of_apply]
    rcases lt_trichotomy j l with h | heq | h
    · simp [h, not_lt.mpr h.le]
    · subst heq
      rw [s16sm_gramJ_diag]
      simp
    · have h1 : gramJ j l = -gramJ l j := by
        rw [s16sm_gramJ_symm, CharTwo.neg_eq]
      rw [h1, if_neg (not_lt.mpr h.le), if_pos h]
      simp
  rw [Matrix.toBilin'_apply', hN, Matrix.sub_mulVec, dotProduct_sub, Matrix.mulVec_transpose,
    dotProduct_comm v (Matrix.vecMul v U), ← Matrix.dotProduct_mulVec, sub_self]

private theorem s16sm_gramJ_det_ne_zero : gramJ.det ≠ 0 := by
  have hJJ : gramJ * gramJ = 1 := by decide +kernel
  have h := congrArg Matrix.det hJJ
  rw [Matrix.det_mul, Matrix.det_one] at h
  intro h0
  rw [h0, zero_mul] at h
  exact one_ne_zero h.symm

private theorem s16sm_B_nondegenerate : s16sm_form.Nondegenerate := by
  change (Matrix.toBilin' gramJ).Nondegenerate
  exact LinearMap.BilinForm.nondegenerate_toBilin'_iff_det_ne_zero.mpr s16sm_gramJ_det_ne_zero

private theorem s16sm_toLin_eq_toLin' (A : GL (Fin 6) (ZMod 2)) :
    (Matrix.GeneralLinearGroup.toLin A :
      (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) =
      Matrix.toLin' (A : Matrix (Fin 6) (Fin 6) (ZMod 2)) := by
  rw [Matrix.toLin'_apply', Matrix.GeneralLinearGroup.coe_toLin]

private theorem s16sm_toLin_mem (A : GL (Fin 6) (ZMod 2)) :
    A ∈ spGrp ↔ Matrix.GeneralLinearGroup.toLin A ∈ bilinIsometryGroup s16sm_form := by
  rw [mem_spGrp, mem_bilinIsometryGroup]
  constructor
  · intro hA x y
    have hcomp : s16sm_form.comp (Matrix.toLin' (A : Matrix (Fin 6) (Fin 6) (ZMod 2)))
        (Matrix.toLin' (A : Matrix (Fin 6) (Fin 6) (ZMod 2))) = s16sm_form := by
      change (Matrix.toBilin' gramJ).comp
          (Matrix.toLin' (A : Matrix (Fin 6) (Fin 6) (ZMod 2)))
          (Matrix.toLin' (A : Matrix (Fin 6) (Fin 6) (ZMod 2))) = Matrix.toBilin' gramJ
      rw [Matrix.toBilin'_comp, hA]
    have h := congrArg (fun F : LinearMap.BilinForm (ZMod 2) (Fin 6 → ZMod 2) => F x y) hcomp
    simpa only [LinearMap.BilinForm.comp_apply, s16sm_toLin_eq_toLin'] using h
  · intro h
    have hcomp : s16sm_form.comp (Matrix.toLin' (A : Matrix (Fin 6) (Fin 6) (ZMod 2)))
        (Matrix.toLin' (A : Matrix (Fin 6) (Fin 6) (ZMod 2))) = s16sm_form := by
      refine LinearMap.ext fun x => LinearMap.ext fun y => ?_
      simpa only [LinearMap.BilinForm.comp_apply, s16sm_toLin_eq_toLin'] using h x y
    have hM := congrArg LinearMap.BilinForm.toMatrix' hcomp
    change LinearMap.BilinForm.toMatrix'
        ((Matrix.toBilin' gramJ).comp
          (Matrix.toLin' (A : Matrix (Fin 6) (Fin 6) (ZMod 2)))
          (Matrix.toLin' (A : Matrix (Fin 6) (Fin 6) (ZMod 2)))) =
      LinearMap.BilinForm.toMatrix' (Matrix.toBilin' gramJ) at hM
    rw [LinearMap.BilinForm.toMatrix'_comp, LinearMap.BilinForm.toMatrix'_toBilin',
      LinearMap.toMatrix'_toLin'] at hM
    exact hM

private noncomputable def s16sm_equiv : G6 ≃* bilinIsometryGroup s16sm_form where
  toFun g := ⟨Matrix.GeneralLinearGroup.toLin (g : GL (Fin 6) (ZMod 2)),
    (s16sm_toLin_mem (g : GL (Fin 6) (ZMod 2))).mp g.2⟩
  invFun γ := ⟨Matrix.GeneralLinearGroup.toLin.symm
      (γ : LinearMap.GeneralLinearGroup (ZMod 2) (Fin 6 → ZMod 2)),
    (s16sm_toLin_mem _).mpr (by
      rw [Matrix.GeneralLinearGroup.toLin.apply_symm_apply]
      exact γ.2)⟩
  left_inv g := Subtype.ext (Matrix.GeneralLinearGroup.toLin.symm_apply_apply _)
  right_inv γ := Subtype.ext (Matrix.GeneralLinearGroup.toLin.apply_symm_apply _)
  map_mul' g h :=
    Subtype.ext (map_mul Matrix.GeneralLinearGroup.toLin (g : GL (Fin 6) (ZMod 2))
      (h : GL (Fin 6) (ZMod 2)))

private theorem s16sm_natural_apply (g : G6) :
    binarySymplecticNatural s16sm_form (s16sm_equiv g) = natRep g := by
  refine LinearMap.ext fun v => ?_
  rw [binarySymplecticNatural_apply]
  change (Matrix.GeneralLinearGroup.toLin (g : GL (Fin 6) (ZMod 2)) :
    (Fin 6 → ZMod 2) →ₗ[ZMod 2] (Fin 6 → ZMod 2)) v = natRep g v
  rw [Matrix.GeneralLinearGroup.coe_toLin, Matrix.mulVecLin_apply, natRep_apply]

theorem s16sm_ker_le_one_nat {M : Type} [AddCommGroup M] [Module (ZMod 2) M] [Finite M]
    (ρ : Representation (ZMod 2) G6 M) (q : M →ₗ[ZMod 2] (Fin 6 → ZMod 2))
    (hq : Function.Surjective q) (hqρ : ∀ g m, q (ρ g m) = natRep g (q m))
    (hZ : ∀ g m, q m = 0 → ρ g m = m)
    (hperf : ∀ ψ : M →ₗ[ZMod 2] ZMod 2, (∀ g m, ψ (ρ g m) = ψ m) → ψ = 0) :
    Module.finrank (ZMod 2) (LinearMap.ker q) ≤ 1 := by
  haveI : Finite (bilinIsometryGroup s16sm_form) :=
    Finite.of_injective s16sm_equiv.symm.toMonoidHom s16sm_equiv.symm.injective
  let ρ' : Representation (ZMod 2) (bilinIsometryGroup s16sm_form) M :=
    ρ.comp s16sm_equiv.symm.toMonoidHom
  have hqρ' : ∀ γ m, q (ρ' γ m) = binarySymplecticNatural s16sm_form γ (q m) := by
    intro γ m
    have hnat : binarySymplecticNatural s16sm_form γ = natRep (s16sm_equiv.symm γ) := by
      conv_lhs => rw [← s16sm_equiv.apply_symm_apply γ]
      exact s16sm_natural_apply (s16sm_equiv.symm γ)
    change q (ρ (s16sm_equiv.symm γ) m) = binarySymplecticNatural s16sm_form γ (q m)
    rw [hnat]
    exact hqρ (s16sm_equiv.symm γ) m
  have hZ' : ∀ γ m, q m = 0 → ρ' γ m = m := by
    intro γ m hm
    change ρ (s16sm_equiv.symm γ) m = m
    exact hZ (s16sm_equiv.symm γ) m hm
  have hperf' : ∀ ψ : M →ₗ[ZMod 2] ZMod 2,
      (∀ γ m, ψ (ρ' γ m) = ψ m) → ψ = 0 := by
    intro ψ hψ
    apply hperf ψ
    intro g m
    have h := hψ (s16sm_equiv g) m
    change ψ (ρ (s16sm_equiv.symm (s16sm_equiv g)) m) = ψ m at h
    rwa [s16sm_equiv.symm_apply_apply] at h
  have hfin := finrank_ker_le_finrank_H1_dual ρ' (binarySymplecticNatural s16sm_form)
    q hq hqρ' hZ' hperf'
  exact hfin.trans (finrank_H1_binarySymplecticNatural_dual_le_one
    s16sm_B_alt s16sm_B_nondegenerate)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo

end
