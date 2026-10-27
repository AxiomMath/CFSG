module

public import CFSG.Quasithin.Background.G117Inputs
public import CFSG.Adapters.SpecialLinearPerfect
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFourSplitNormal

public section

open Matrix CFSG.Assembly.LowTwoRank CFSG.ComponentClassification.CatalogueBOrthogonalFourSplit
open scoped commutatorElement

namespace CFSG.Quasithin

namespace G11

namespace P3Ortho

namespace Om4

variable {K : Type} [Field K]

theorem commonDeterminant_scalarPair (c : Kˣ) : commonDeterminant (scalarPair c) = c ^ 2 := by
  apply Units.ext
  simp [commonDeterminant, scalarPair, Matrix.GeneralLinearGroup.det, sq]

section CharTwoInj

variable [CharP K 2]

theorem specialRho_injective : Function.Injective (specialRho (K := K)) := by
  rw [injective_iff_map_eq_one]
  intro z hz
  obtain ⟨c, hc, h1, h2⟩ := (specialRho_eq_one_iff z).1 hz
  have hc' : ((c : K) - 1) ^ 2 = 0 := by
    have h2' : (2 : K) = 0 := CharTwo.two_eq_zero
    have hc2 : (c : K) ^ 2 = 1 := by
      have := congrArg Units.val hc
      simpa [Units.val_pow_eq_pow_val] using this
    linear_combination hc2 - ((c : K) - 1) * h2'
  have hc1 : c = 1 := by
    apply Units.ext
    have := pow_eq_zero_iff (two_ne_zero) |>.1 hc'
    simpa [sub_eq_zero] using this
  subst hc1
  simp only [map_one] at h1 h2
  exact Prod.ext (Matrix.SpecialLinearGroup.toGL_injective (by simpa using h1))
    (Matrix.SpecialLinearGroup.toGL_injective (by simpa using h2))

end CharTwoInj

section CharTwo

variable [Finite K] [CharP K 2]

theorem exists_unit_sq (δ : Kˣ) : ∃ c : Kˣ, c ^ 2 = δ := by
  have : Fintype K := Fintype.ofFinite K
  obtain ⟨r, hr⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) (δ : K)
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  exact ⟨Units.mk0 r hr0, Units.ext (by simp [hr, sq])⟩

theorem rho_mem_specialImage (z : equalDeterminants K) : rho z ∈ specialImage K := by
  obtain ⟨c, hc⟩ := exists_unit_sq (commonDeterminant z)⁻¹
  have h1 : commonDeterminant (z * scalarPair c) = 1 := by
    rw [map_mul, commonDeterminant_scalarPair, hc, mul_inv_cancel]
  have h2 := rho_mem_specialImage_of_commonDeterminant _ h1
  rwa [map_mul, rho_scalarPair, mul_one] at h2

theorem mem_specialImage_or_mul_tau (g : DeterminantIsometries K) :
    g ∈ specialImage K ∨ g * tau ∈ specialImage K := by
  obtain ⟨z, rfl | rfl⟩ := determinant_isometry_exhaustion g
  · exact Or.inl (rho_mem_specialImage z)
  · right
    rw [mul_assoc, tau_mul_tau, mul_one]
    exact rho_mem_specialImage z

theorem commutator_mem_specialImage (g h : DeterminantIsometries K) :
    ⁅g, h⁆ ∈ specialImage K := by
  have hN : (specialImage K).Normal := inferInstance
  rcases mem_specialImage_or_mul_tau g with hg | hg
  · have e : ⁅g, h⁆ = g * (h * g⁻¹ * h⁻¹) := by group
    rw [e]
    exact (specialImage K).mul_mem hg (hN.conj_mem g⁻¹ ((specialImage K).inv_mem hg) h)
  rcases mem_specialImage_or_mul_tau h with hh | hh
  · have e : ⁅g, h⁆ = (g * h * g⁻¹) * h⁻¹ := by group
    rw [e]
    exact (specialImage K).mul_mem (hN.conj_mem h hh g) ((specialImage K).inv_mem hh)
  · have e : ⁅g, h⁆ = (g * tau) * (tau⁻¹ * ((h * tau) * (g * tau)⁻¹) * tau⁻¹⁻¹) * (h * tau)⁻¹ := by
      group
    rw [e]
    exact (specialImage K).mul_mem ((specialImage K).mul_mem hg
      (hN.conj_mem _ ((specialImage K).mul_mem hh ((specialImage K).inv_mem hg)) tau⁻¹))
      ((specialImage K).inv_mem hh)

end CharTwo

section Coordinates

variable (K)

@[expose] def toMat : (Fin 2 ⊕ Fin 2 → K) ≃ₗ[K] Matrix (Fin 2) (Fin 2) K where
  toFun v := !![v (.inl 0), v (.inl 1); -v (.inr 1), v (.inr 0)]
  invFun X := Sum.elim ![X 0 0, X 0 1] ![X 1 1, -X 1 0]
  map_add' v w := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp [add_comm]
  map_smul' c v := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  left_inv v := by
    funext s
    rcases s with i | i <;> fin_cases i <;> simp
  right_inv X := by
    ext i j
    fin_cases i <;> fin_cases j <;> simp

theorem det_toMat (v : Fin 2 ⊕ Fin 2 → K) : (toMat K v).det = StatedQuadPlus 2 K v := by
  simp [toMat, Matrix.det_fin_two, StatedQuadPlus, Fin.sum_univ_two]

@[expose] noncomputable def Ψ :
    GL (Fin 2 ⊕ Fin 2) K ≃* (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :=
  Matrix.GeneralLinearGroup.toLin.trans
    ((LinearMap.GeneralLinearGroup.congrLinearEquiv (toMat K)).trans
      (LinearMap.GeneralLinearGroup.generalLinearEquiv K _))

theorem Ψ_apply (A : GL (Fin 2 ⊕ Fin 2) K) (X : Matrix (Fin 2) (Fin 2) K) :
    Ψ K A X = toMat K ((A : Matrix _ _ K) *ᵥ (toMat K).symm X) := rfl

variable {K}

theorem map_statedOmega :
    (StatedOmega (StatedQuadPlus 2 K)).map (Ψ K).toMonoidHom =
      ⁅DeterminantIsometries K, DeterminantIsometries K⁆ := by
  have hset : {A : GL (Fin 2 ⊕ Fin 2) K | ∀ v, StatedQuadPlus 2 K ((A : Matrix _ _ K) *ᵥ v) =
      StatedQuadPlus 2 K v} =
      (((DeterminantIsometries K).comap (Ψ K).toMonoidHom : Subgroup _) : Set _) := by
    ext A
    simp only [Set.mem_ofPred_eq, SetLike.mem_coe, Subgroup.mem_comap,
      TauCeti.QuadraticMap.mem_orthogonalGroup_iff, MulEquiv.coe_toMonoidHom]
    constructor
    · intro h X
      have hX : X.det = StatedQuadPlus 2 K ((toMat K).symm X) := by
        rw [← det_toMat, LinearEquiv.apply_symm_apply]
      rw [determinantForm_apply, determinantForm_apply, Ψ_apply, det_toMat, h, hX]
    · intro h v
      have h1 := h (toMat K v)
      rw [determinantForm_apply, determinantForm_apply, Ψ_apply, LinearEquiv.symm_apply_apply,
        det_toMat, det_toMat] at h1
      exact h1
  unfold StatedOmega
  rw [hset, Subgroup.closure_eq, Subgroup.map_commutator,
    Subgroup.map_comap_eq_self_of_surjective (Ψ K).surjective]

end Coordinates

section Perfect

theorem isPerfect_prod {G G' : Type*} [Group G] [Group G'] (h : Group.IsPerfect G)
    (h' : Group.IsPerfect G') : Group.IsPerfect (G × G') := by
  rw [Group.isPerfect_def, commutator_def, ← Subgroup.top_prod_top, Subgroup.commutator_prod_prod,
    ← commutator_def, ← commutator_def, h.commutator_eq_top, h'.commutator_eq_top]

variable (K)

@[expose] noncomputable def rho' :
    Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K →*
      (Matrix (Fin 2) (Fin 2) K ≃ₗ[K] Matrix (Fin 2) (Fin 2) K) :=
  (DeterminantIsometries K).subtype.comp specialRho

variable {K}

theorem range_rho'_le : (rho' K).range ≤ DeterminantIsometries K := by
  rintro _ ⟨z, rfl⟩
  exact (specialRho z).2

theorem commutator_eq_range [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    ⁅DeterminantIsometries K, DeterminantIsometries K⁆ = (rho' K).range := by
  have hSL := CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K h4
  have : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K ×
      Matrix.SpecialLinearGroup (Fin 2) K) := isPerfect_prod hSL hSL
  have := Group.IsPerfect.range (rho' K)
  apply le_antisymm
  · rw [Subgroup.commutator_le]
    intro g hg h hh
    obtain ⟨z, hz⟩ := commutator_mem_specialImage ⟨g, hg⟩ ⟨h, hh⟩
    exact ⟨z, congrArg Subtype.val hz⟩
  · calc (rho' K).range = ⁅(rho' K).range, (rho' K).range⁆ := Subgroup.commutator_eq_self.symm
      _ ≤ ⁅DeterminantIsometries K, DeterminantIsometries K⁆ :=
        Subgroup.commutator_mono (range_rho'_le) (range_rho'_le)

theorem rho'_injective [CharP K 2] : Function.Injective (rho' K) :=
  Subtype.val_injective.comp specialRho_injective

end Perfect

theorem iso_of_card (K : Type) [Field K] [Finite K] [CharP K 2] (h4 : 4 ≤ Nat.card K) :
    Nonempty (↥(StatedOmega (StatedQuadPlus 2 K)) ≃*
      (Matrix.SpecialLinearGroup (Fin 2) K × Matrix.SpecialLinearGroup (Fin 2) K)) := by
  let e1 := (Ψ K).subgroupMap (StatedOmega (StatedQuadPlus 2 K))
  let e2 := MulEquiv.subgroupCongr
    (show (StatedOmega (StatedQuadPlus 2 K)).map (Ψ K).toMonoidHom = (rho' K).range by
      rw [map_statedOmega, commutator_eq_range h4])
  let e3 := (MonoidHom.ofInjective (rho'_injective (K := K))).symm
  exact ⟨e1.trans (e2.trans e3)⟩

end Om4

end P3Ortho

theorem om4Plus4Iso : Om4Plus4Iso := by
  refine P3Ortho.Om4.iso_of_card (GaloisField 2 2) ?_
  rw [GaloisField.card 2 2 (by norm_num)]
  norm_num

end G11

end CFSG.Quasithin
