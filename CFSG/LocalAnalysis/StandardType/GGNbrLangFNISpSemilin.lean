module

public import CFSG.LocalAnalysis.StandardType.GGNbrLangFNIOrthogonalSemilin
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUSpLabels
import all CFSG.LocalAnalysis.StandardType.GGTableBSymplecticBstar
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotFieldNormalizeSp

public section

namespace CFSG.StandardType

open CFSG.Assembly
open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher

namespace RecipeFieldSp

theorem exists_semilinear_representatives {K : Type} [Field K] [Finite K] [CharP K 2]
    {r p : ℕ} [NeZero r] (hp : p.Prime)
    {f h : MulAut (LargeEvenProj (LargeEvenSpGroup K r))}
    (hf : f ∈ LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSpGroup K r)))
    (hford : orderOf f = p)
    (hh : h ∈ LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSpGroup K r))
      (LargeEvenGSpSet K r))
    (hhp : h ^ p = 1) (hcomm : h * f = f * h) :
    ∃ (σ : K ≃+* K) (u : ↥(LargeEvenSpGroup K r)),
      σ ≠ 1 ∧ σ ^ p = 1 ∧ u ^ p = 1 ∧
      Matrix.GeneralLinearGroup.map (σ : K →+* K) (u : GL (Fin r ⊕ Fin r) K) = u ∧
      (∀ x, TableBSymp.spProjEquivSp (h x) = u * TableBSymp.spProjEquivSp x * u⁻¹) ∧
      ∀ x, ((TableBSymp.spProjEquivSp (f x) : ↥(LargeEvenSpGroup K r)) :
          GL (Fin r ⊕ Fin r) K) =
        Matrix.GeneralLinearGroup.map (σ : K →+* K)
          ((TableBSymp.spProjEquivSp x : ↥(LargeEvenSpGroup K r)) : GL (Fin r ⊕ Fin r) K) := by
  classical
  let Θ : LargeEvenProj (LargeEvenSpGroup K r) ≃* ↥(LargeEvenSpGroup K r) :=
    TableBSymp.spProjEquivSp
  obtain ⟨σ, hσf⟩ := RecipeFieldSp.exists_fieldAut_of_mem hf
  have hpow : f ^ p = 1 := by
    rw [← hford]
    exact pow_orderOf_eq_one f
  have hr : 1 ≤ r := Nat.pos_of_ne_zero (NeZero.ne r)
  have hσp : σ ^ p = 1 := by
    apply RecipeFieldSpU.fieldAut_injective (m := r) hr
    rw [map_pow, map_one, ← hσf]
    exact hpow
  have hσ1 : σ ≠ 1 := by
    intro h1
    have hf1 : f = 1 := by rw [hσf, h1, map_one]
    have hord1 : orderOf f = 1 := by rw [hf1, orderOf_one]
    exact hp.ne_one (hford.symm.trans hord1)
  have hinn : h ∈ LargeEvenInnSet (LargeEvenProj (LargeEvenSpGroup K r)) :=
    RecipeFieldSp.mem_conjImage_iff_inn.mp hh
  have hZ : Subgroup.center ↥(LargeEvenSpGroup K r) = ⊥ :=
    CFSG.SeitzReduction.SymplecticPilot.center_statedSp_eq_bot (K := K) r
  obtain ⟨u, hu, hup⟩ :=
    exists_conj_pow_eq_one_of_mem_innSet (Θ := Θ) hinn hZ hhp
  have hfield : MulAut.congr Θ (fieldAut r K σ) = fieldSp r K σ := by
    rw [show Θ = (CFSG.SeitzReduction.F4Pilot.spProjEquiv r K).symm from rfl,
      ← CFSG.SeitzReduction.F4Pilot.mulAutCongr_spProjEquiv_fieldSp (r := r) (K := K) σ]
    ext x
    simp [MulAut.congr_apply, MulEquiv.trans_apply]
  have hcommΘ : MulAut.conj u * fieldSp r K σ = fieldSp r K σ * MulAut.conj u := by
    have h := congrArg (MulAut.congr Θ) hcomm
    simp only [map_mul, hu, hσf, hfield] at h
    exact h
  have hfixu : fieldSp r K σ u = u :=
    conj_eq_self_of_commute_conj hcommΘ hZ
  have hσu : Matrix.GeneralLinearGroup.map (σ : K →+* K) (u : GL (Fin r ⊕ Fin r) K) = u := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_map_apply]
    have h := coe_fieldSp (r := r) (K := K) σ u
    rw [hfixu] at h
    exact h.symm
  have hpoint : ∀ x, TableBSymp.spProjEquivSp (h x) =
      u * TableBSymp.spProjEquivSp x * u⁻¹ := by
    intro x
    have h := DFunLike.congr_fun hu (TableBSymp.spProjEquivSp x)
    dsimp only [Θ] at h
    simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply,
      MulAut.conj_apply] at h
    exact h
  have hfpoint : ∀ x, ((TableBSymp.spProjEquivSp (f x) : ↥(LargeEvenSpGroup K r)) :
      GL (Fin r ⊕ Fin r) K) =
      Matrix.GeneralLinearGroup.map (σ : K →+* K)
        ((TableBSymp.spProjEquivSp x : ↥(LargeEvenSpGroup K r)) : GL (Fin r ⊕ Fin r) K) := by
    intro x
    have hcongr : TableBSymp.spProjEquivSp (f x) =
        fieldSp r K σ (TableBSymp.spProjEquivSp x) := by
      have h := DFunLike.congr_fun hfield (TableBSymp.spProjEquivSp x)
      dsimp only [Θ] at h
      simp only [MulAut.congr_apply, MulEquiv.trans_apply, MulEquiv.symm_apply_apply] at h
      simpa only [hσf] using h
    rw [hcongr]
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_map_apply]
    exact coe_fieldSp σ (TableBSymp.spProjEquivSp x)
  exact ⟨σ, u, hσ1, hσp, hup, hσu, hpoint, hfpoint⟩

end RecipeFieldSp

end CFSG.StandardType
