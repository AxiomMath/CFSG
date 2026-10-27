module

public import CFSG.Quasithin.Recognition.G112A2ModSevenCore
public import CFSG.Milestones.ASVolI.G11
public import CFSG.ClassicalInvolution.SubnormalClosure

public section

namespace CFSG.Quasithin.G112A2

open CFSG.Quasithin CFSG.Quasithin.G11 CFSG.Open CFSG.ASVolI.ChG
open CFSG.ComponentClassification.RankTwoClassical
open CFSG.Quasithin.Background.Harris.CaseClassificationAndDescent.TwoComp
open scoped MatrixGroups Matrix

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]

theorem g112A2Seven_fStarIn_le (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) : fStarIn Γ ≤ Γ := by
  intro f hf
  obtain ⟨x, -, rfl⟩ := Subgroup.mem_map.mp hf
  exact x.2

theorem g112A2Seven_fStarIn_normal (Γ : Subgroup (V ≃ₗ[ZMod 2] V)) (γ : V ≃ₗ[ZMod 2] V)
    (hγ : γ ∈ Γ) (f : V ≃ₗ[ZMod 2] V) (hf : f ∈ fStarIn Γ) : γ * f * γ⁻¹ ∈ fStarIn Γ := by
  obtain ⟨x, hx, rfl⟩ := Subgroup.mem_map.mp hf
  have hN : (genFittingFStar ↥Γ).Normal := CFSG.ClassicalInvolution.genFittingFStar_normal ↥Γ
  have hc : (⟨γ, hγ⟩ : ↥Γ) * x * (⟨γ, hγ⟩ : ↥Γ)⁻¹ ∈ genFittingFStar ↥Γ :=
    hN.conj_mem x hx _
  exact Subgroup.mem_map.mpr ⟨(⟨γ, hγ⟩ : ↥Γ) * x * (⟨γ, hγ⟩ : ↥Γ)⁻¹, hc, rfl⟩

theorem g112A2Seven_glue_false (B : LinearMap.BilinForm (ZMod 2) V) (Γ : Subgroup (V ≃ₗ[ZMod 2] V))
    (hF : IsNaturalMatrixModule (fStarIn Γ) (StatedOmega (StatedQuadPlus 2 (GaloisField 2 2))))
    (hdim : Module.finrank (ZMod 2) V = 8)
    (hBiso : ∀ γ ∈ Γ, ∀ v w, B (γ v) (γ w) = B v w)
    (hBnd : ∀ v, (∀ w, B v w = 0) → v = 0)
    (t : V ≃ₗ[ZMod 2] V) (ht : t ∈ Γ)
    (hr : Module.finrank (ZMod 2) (LinearMap.range (t.toLinearMap - LinearMap.id)) = 2)
    (htB : ∀ v, B v (t v) = 0) : False := by
  classical
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have h4 : 4 ≤ Nat.card (GaloisField 2 2) := by
    rw [hK]
  obtain ⟨φ, ψ, hψ⟩ := hF
  let ψM : V ≃ₗ[ZMod 2] Matrix (Fin 2) (Fin 2) (GaloisField 2 2) :=
    ψ.trans ((oMat (GaloisField 2 2)).restrictScalars (ZMod 2))
  have hψM : ∀ v, ψM v = oMat (GaloisField 2 2) (ψ v) := fun v => rfl
  have T2 : ∀ f ∈ fStarIn Γ, ∃ (A B' : SL(2, GaloisField 2 2)), ∀ v : V,
      ψM (f v) = (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) * ψM v *
        (B' : Matrix (Fin 2) (Fin 2) (GaloisField 2 2))ᵀ := by
    intro f hf
    obtain ⟨x, hx⟩ := thetaHom_surj (φ ⟨f, hf⟩).2
    refine ⟨x.1, x.2, fun v => ?_⟩
    have h1 := hψ ⟨f, hf⟩ v
    rw [hψM, hψM, h1, ← hx]
    exact oMat_thetaHom x.1 x.2 (ψ v)
  have T1 : ∀ (A B' : SL(2, GaloisField 2 2)), ∃ f ∈ fStarIn Γ, ∀ v : V,
      ψM (f v) = (A : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) * ψM v *
        (B' : Matrix (Fin 2) (Fin 2) (GaloisField 2 2))ᵀ := by
    intro A B'
    let Y : ↥(StatedOmega (StatedQuadPlus 2 (GaloisField 2 2))) :=
      ⟨thetaHom (A, B'), thetaHom_mem h4 (A, B')⟩
    refine ⟨((φ.symm Y : ↥(fStarIn Γ)) : V ≃ₗ[ZMod 2] V), (φ.symm Y).2, fun v => ?_⟩
    have h1 := hψ (φ.symm Y) v
    rw [MulEquiv.apply_symm_apply] at h1
    rw [hψM, hψM, h1]
    exact oMat_thetaHom A B' (ψ v)
  let tM : Matrix (Fin 2) (Fin 2) (GaloisField 2 2) ≃ₗ[ZMod 2]
      Matrix (Fin 2) (Fin 2) (GaloisField 2 2) :=
    ψM.symm.trans (t.trans ψM)
  have htM : ∀ X, tM X = ψM (t (ψM.symm X)) := fun X => rfl
  let BM : LinearMap.BilinForm (ZMod 2) (Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) :=
    LinearMap.compl₁₂ B ψM.symm.toLinearMap ψM.symm.toLinearMap
  have hBM : ∀ X Y, BM X Y = B (ψM.symm X) (ψM.symm Y) := fun X Y => rfl
  have hnorm : ∀ (A B'' : SL(2, GaloisField 2 2)), ∃ A' B''' : SL(2, GaloisField 2 2), ∀ X,
      tM (g112A2SevenTens A B'' X) = g112A2SevenTens A' B''' (tM X) := by
    intro A B''
    obtain ⟨f, hf, hfA⟩ := T1 A B''
    obtain ⟨A', B''', hf'⟩ := T2 (t * f * t⁻¹) (g112A2Seven_fStarIn_normal Γ t ht f hf)
    refine ⟨A', B''', fun X => ?_⟩
    have hv : ψM.symm (g112A2SevenTens A B'' X) = f (ψM.symm X) := by
      apply ψM.injective
      rw [LinearEquiv.apply_symm_apply, hfA, LinearEquiv.apply_symm_apply]
      rfl
    have hw := hf' (t (ψM.symm X))
    have hw' : (t * f * t⁻¹) (t (ψM.symm X)) = t (f (ψM.symm X)) := by
      simp
    rw [hw'] at hw
    rw [htM, htM, hv]
    unfold g112A2SevenTens
    exact hw
  have hBinv : ∀ (A B'' : SL(2, GaloisField 2 2)) (X Y : Matrix (Fin 2) (Fin 2) (GaloisField 2 2)),
      BM (g112A2SevenTens A B'' X) (g112A2SevenTens A B'' Y) = BM X Y := by
    intro A B'' X Y
    obtain ⟨f, hf, hfA⟩ := T1 A B''
    have hv : ∀ Z, ψM.symm (g112A2SevenTens A B'' Z) = f (ψM.symm Z) := by
      intro Z
      apply ψM.injective
      rw [LinearEquiv.apply_symm_apply, hfA, LinearEquiv.apply_symm_apply]
      rfl
    rw [hBM, hBM, hv, hv, hBiso f (g112A2Seven_fStarIn_le Γ hf)]
  have hBnd' : ∀ X : Matrix (Fin 2) (Fin 2) (GaloisField 2 2), (∀ Y, BM X Y = 0) → X = 0 := by
    intro X hX
    have h0 : ψM.symm X = 0 := hBnd _ (fun w => by
      have h1 := hX (ψM w)
      rw [hBM, LinearEquiv.symm_apply_apply] at h1
      exact h1)
    have h2 := congrArg ψM h0
    rw [LinearEquiv.apply_symm_apply, map_zero] at h2
    exact h2
  have htB' : ∀ X, BM X (tM X) = 0 := by
    intro X
    rw [hBM, htM, LinearEquiv.symm_apply_apply]
    exact htB _
  have hrange : LinearMap.range (tM.toLinearMap - LinearMap.id) =
      (LinearMap.range (t.toLinearMap - LinearMap.id)).map ψM.toLinearMap := by
    ext Y
    constructor
    · rintro ⟨X, rfl⟩
      refine ⟨t (ψM.symm X) - ψM.symm X, ⟨ψM.symm X, rfl⟩, ?_⟩
      simp [htM]
    · rintro ⟨w, ⟨v, rfl⟩, rfl⟩
      refine ⟨ψM v, ?_⟩
      simp [htM]
  have hr' : Module.finrank (ZMod 2) (LinearMap.range (tM.toLinearMap - LinearMap.id)) = 2 := by
    rw [hrange, LinearEquiv.finrank_map_eq, hr]
  have hM : Module.finrank (ZMod 2) (Matrix (Fin 2) (Fin 2) (GaloisField 2 2)) = 8 := by
    rw [← LinearEquiv.finrank_eq ψM]
    exact hdim
  exact g112A2Seven_core_false hK tM hnorm BM hBinv hBnd' htB' hr' hM

end CFSG.Quasithin.G112A2
