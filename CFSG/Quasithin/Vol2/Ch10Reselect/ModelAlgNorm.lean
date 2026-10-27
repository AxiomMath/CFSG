module

public import CFSG.Quasithin.Vol2.Ch10Reselect.ModelAlgId
public import CFSG.Quasithin.Vol2.Ch10Reselect.Commutant
public import Mathlib.RingTheory.SimpleRing.Principal

public section

namespace CFSG.Quasithin.Vol2.Ch10Reselect

open Matrix

private lemma nrm_rho_eq_one {K : Type} [Field K] {g : Matrix.SpecialLinearGroup (Fin 2) K}
    (h : rhoSL K g = 1) : g = 1 := by
  have key : ∀ v, rhoSL K g v = v := fun v => by simp [h]
  have h1 : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ ![1, 0] = ![1, 0] := by
    have := key (![1, 0], 0)
    rw [rhoSL_apply] at this
    exact congrArg Prod.fst this
  have h2 : (g : Matrix (Fin 2) (Fin 2) K) *ᵥ ![0, 1] = ![0, 1] := by
    have := key (![0, 1], 0)
    rw [rhoSL_apply] at this
    exact congrArg Prod.fst this
  have hM : (g : Matrix (Fin 2) (Fin 2) K) = 1 := by
    have e00 := congrFun h1 0
    have e10 := congrFun h1 1
    have e01 := congrFun h2 0
    have e11 := congrFun h2 1
    simp [Matrix.mulVec, dotProduct, Fin.sum_univ_two] at e00 e10 e01 e11
    ext i j
    fin_cases i <;> fin_cases j <;> simp [e00, e10, e01, e11]
  exact Subtype.ext hM

private lemma nrm_rho_injective {K : Type} [Field K] : Function.Injective (rhoSL K) :=
  (injective_iff_map_eq_one (rhoSL K)).2 fun _ hg => nrm_rho_eq_one hg

private lemma nrm_rho_add {K : Type} [Field K] (g : Matrix.SpecialLinearGroup (Fin 2) K)
    (v w : UTilde K) : rhoSL K g (v + w) = rhoSL K g v + rhoSL K g w := by
  simp only [rhoSL_apply, Prod.fst_add, Prod.snd_add, Prod.mk_add_mk, Matrix.mulVec_add]

private lemma nrm_sigma_add {K : Type} [Field K] (σ : RingAut K) (v w : UTilde K) :
    sigmaPerm K σ (v + w) = sigmaPerm K σ v + sigmaPerm K σ w := by
  refine Prod.ext (funext fun i => ?_) (funext fun i => ?_) <;>
    simp [sigmaPerm_apply, map_add]

private lemma nrm_perm_inv_add {X : Type*} [AddGroup X] (f : Equiv.Perm X)
    (hf : ∀ v w, f (v + w) = f v + f w) (v w : X) : f⁻¹ (v + w) = f⁻¹ v + f⁻¹ w := by
  have h : f (f⁻¹ v + f⁻¹ w) = v + w := by
    rw [hf, Equiv.Perm.inv_def, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  rw [← h, Equiv.Perm.inv_def, Equiv.symm_apply_apply]

private lemma nrm_slMap_slMap_inv {K : Type} [Field K] (σ : RingAut K)
    (g : Matrix.SpecialLinearGroup (Fin 2) K) : slMap σ (slMap σ⁻¹ g) = g := by
  apply Matrix.SpecialLinearGroup.ext
  intro i j
  simp [slMap]

private lemma nrm_glMap_glMap_inv {K : Type} [Field K] (σ : RingAut K) (B : GL (Fin 2) K) :
    glMap K σ (glMap K σ⁻¹ B) = B := by
  apply Units.ext
  ext i j
  simp [glMap]

theorem normStruct (hAut : AutSL2Exists) {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) (φ : Equiv.Perm (UTilde K)) (hadd : ∀ v w, φ (v + w) = φ v + φ w)
    (hnorm : ∀ g : Matrix.SpecialLinearGroup (Fin 2) K,
      ∃ g' : Matrix.SpecialLinearGroup (Fin 2) K, φ * rhoSL K g = rhoSL K g' * φ) :
    ∃ (g : Matrix.SpecialLinearGroup (Fin 2) K) (σ : RingAut K) (B : GL (Fin 2) K),
      φ = phi K g σ B := by
  choose β hβ using hnorm
  have hmul : ∀ g h, β (g * h) = β g * β h := by
    intro g h
    apply nrm_rho_injective
    apply mul_right_cancel (b := φ)
    calc rhoSL K (β (g * h)) * φ = φ * rhoSL K (g * h) := (hβ (g * h)).symm
      _ = (φ * rhoSL K g) * rhoSL K h := by rw [map_mul, mul_assoc]
      _ = (rhoSL K (β g) * φ) * rhoSL K h := by rw [hβ g]
      _ = rhoSL K (β g) * (rhoSL K (β h) * φ) := by rw [mul_assoc, hβ h]
      _ = rhoSL K (β g * β h) * φ := by rw [map_mul, mul_assoc]
  let α : Matrix.SpecialLinearGroup (Fin 2) K →* Matrix.SpecialLinearGroup (Fin 2) K :=
    MonoidHom.mk' β hmul
  have hαinj : Function.Injective α := by
    rw [injective_iff_map_eq_one]
    intro g hg
    have hβg : β g = 1 := hg
    have h1 : φ * rhoSL K g = φ * 1 := by
      rw [hβ g, hβg, map_one, one_mul, mul_one]
    exact nrm_rho_eq_one (mul_left_cancel h1)
  have hαbij : Function.Bijective α := by
    haveI : Finite (Matrix.SpecialLinearGroup (Fin 2) K) :=
      Finite.of_injective
        (fun g : Matrix.SpecialLinearGroup (Fin 2) K => (g : Matrix (Fin 2) (Fin 2) K))
        (fun _ _ hgh => Subtype.ext hgh)
    exact Finite.injective_iff_bijective.mp hαinj
  obtain ⟨g₀, σ, hα⟩ := hAut K hK (MulEquiv.ofBijective α hαbij)
  have hβform : ∀ A, β A = g₀ * slMap σ A * g₀⁻¹ := fun A => hα A
  obtain ⟨φ', hφ'⟩ : ∃ φ' : Equiv.Perm (UTilde K),
      φ' = (rhoSL K g₀)⁻¹ * φ * (sigmaPerm K σ)⁻¹ := ⟨_, rfl⟩
  have hkey : ∀ h, φ * rhoSL K h = rhoSL K g₀ * rhoSL K (slMap σ h) * (rhoSL K g₀)⁻¹ * φ := by
    intro h
    rw [hβ h, hβform h]
    simp only [map_mul, map_inv]
  have hcomm : ∀ h, φ' * rhoSL K (slMap σ h) = rhoSL K (slMap σ h) * φ' := by
    intro h
    have hσ' : (sigmaPerm K σ)⁻¹ * rhoSL K (slMap σ h) = rhoSL K h * (sigmaPerm K σ)⁻¹ := by
      have e : rhoSL K (slMap σ h) = sigmaPerm K σ * rhoSL K h * (sigmaPerm K σ)⁻¹ := by
        rw [sigmaPerm_rho σ h]
        group
      rw [e]
      group
    rw [hφ']
    calc (rhoSL K g₀)⁻¹ * φ * (sigmaPerm K σ)⁻¹ * rhoSL K (slMap σ h)
        = (rhoSL K g₀)⁻¹ * φ * ((sigmaPerm K σ)⁻¹ * rhoSL K (slMap σ h)) := by
          simp only [mul_assoc]
      _ = (rhoSL K g₀)⁻¹ * φ * (rhoSL K h * (sigmaPerm K σ)⁻¹) := by rw [hσ']
      _ = (rhoSL K g₀)⁻¹ * (φ * rhoSL K h) * (sigmaPerm K σ)⁻¹ := by simp only [mul_assoc]
      _ = (rhoSL K g₀)⁻¹ * (rhoSL K g₀ * rhoSL K (slMap σ h) * (rhoSL K g₀)⁻¹ * φ) *
            (sigmaPerm K σ)⁻¹ := by rw [hkey h]
      _ = rhoSL K (slMap σ h) * ((rhoSL K g₀)⁻¹ * φ * (sigmaPerm K σ)⁻¹) := by group
  have hcomm' : ∀ g, φ' * rhoSL K g = rhoSL K g * φ' := by
    intro g
    have h := hcomm (slMap σ⁻¹ g)
    rwa [nrm_slMap_slMap_inv] at h
  have hadd' : ∀ v w, φ' (v + w) = φ' v + φ' w := by
    intro v w
    rw [hφ']
    simp only [Equiv.Perm.mul_apply]
    rw [nrm_perm_inv_add (sigmaPerm K σ) (nrm_sigma_add σ), hadd,
      nrm_perm_inv_add (rhoSL K g₀) (nrm_rho_add g₀)]
  have hF : ∀ (g : Matrix.SpecialLinearGroup (Fin 2) K) (v : UTilde K),
      (AddMonoidHom.mk' φ' hadd') ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ v.1,
          (g : Matrix (Fin 2) (Fin 2) K) *ᵥ v.2) =
        ((g : Matrix (Fin 2) (Fin 2) K) *ᵥ ((AddMonoidHom.mk' φ' hadd') v).1,
          (g : Matrix (Fin 2) (Fin 2) K) *ᵥ ((AddMonoidHom.mk' φ' hadd') v).2) := by
    intro g v
    have h := congrArg (fun p : Equiv.Perm (UTilde K) => p v) (hcomm' g)
    simp only [Equiv.Perm.mul_apply] at h
    rw [← rhoSL_apply, ← rhoSL_apply]
    exact h
  obtain ⟨a, b, c, d, hform⟩ :=
    addMonoidHom_pair_of_commute_sl2 (AddMonoidHom.mk' φ' hadd') hF
  have hφform : ∀ v, φ' v = (a • v.1 + b • v.2, c • v.1 + d • v.2) := fun v => hform v
  obtain ⟨M, hM⟩ : ∃ M : Matrix (Fin 2) (Fin 2) K, M = !![a, b; c, d] := ⟨_, rfl⟩
  have hdet : M.det ≠ 0 := by
    intro hd
    obtain ⟨w, hw, hMw⟩ := Matrix.exists_mulVec_eq_zero_iff.mpr hd
    have hw0 : a * w 0 + b * w 1 = 0 := by
      have := congrFun hMw 0
      simp [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      linear_combination this
    have hw1 : c * w 0 + d * w 1 = 0 := by
      have := congrFun hMw 1
      simp [hM, Matrix.mulVec, dotProduct, Fin.sum_univ_two] at this
      linear_combination this
    have h0 : a • (w 0 • (![1, 0] : Fin 2 → K)) + b • (w 1 • (![1, 0] : Fin 2 → K)) = 0 := by
      rw [smul_smul, smul_smul, ← add_smul, hw0, zero_smul]
    have h1 : c • (w 0 • (![1, 0] : Fin 2 → K)) + d • (w 1 • (![1, 0] : Fin 2 → K)) = 0 := by
      rw [smul_smul, smul_smul, ← add_smul, hw1, zero_smul]
    have hv : φ' (w 0 • (![1, 0] : Fin 2 → K), w 1 • (![1, 0] : Fin 2 → K)) = φ' 0 := by
      rw [hφform, hφform]
      simp only [Prod.fst_zero, Prod.snd_zero, smul_zero, add_zero]
      exact Prod.ext h0 h1
    have hinj := φ'.injective hv
    have hw0' : w 0 = 0 := by
      have := congrArg (fun p : UTilde K => p.1 0) hinj
      simpa using this
    have hw1' : w 1 = 0 := by
      have := congrArg (fun p : UTilde K => p.2 0) hinj
      simpa using this
    exact hw (funext fun i => by fin_cases i <;> simp [hw0', hw1'])
  have hunit : IsUnit M.det := isUnit_iff_ne_zero.mpr hdet
  obtain ⟨B, hB⟩ : ∃ B : GL (Fin 2) K, (B : Matrix (Fin 2) (Fin 2) K) = M :=
    ⟨Units.mk M M⁻¹ (Matrix.mul_nonsing_inv M hunit) (Matrix.nonsing_inv_mul M hunit), rfl⟩
  have hφ'B : φ' = bPerm K B := by
    apply Equiv.ext
    intro v
    rw [hφform, bPerm_apply, hB]
    simp [hM]
  have hφeq : φ = rhoSL K g₀ * φ' * sigmaPerm K σ := by
    rw [hφ']
    group
  have hσB : bPerm K B * sigmaPerm K σ = sigmaPerm K σ * bPerm K (glMap K σ⁻¹ B) := by
    rw [sigmaPerm_bPerm σ (glMap K σ⁻¹ B), nrm_glMap_glMap_inv]
  refine ⟨g₀, σ, glMap K σ⁻¹ B, ?_⟩
  show φ = rhoSL K g₀ * sigmaPerm K σ * bPerm K (glMap K σ⁻¹ B)
  rw [hφeq, hφ'B, mul_assoc (rhoSL K g₀) (bPerm K B) (sigmaPerm K σ), hσB, mul_assoc]

end CFSG.Quasithin.Vol2.Ch10Reselect
