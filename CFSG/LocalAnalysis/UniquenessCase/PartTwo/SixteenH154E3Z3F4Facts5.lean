module

public import CFSG.LinearAlgebra.FixedPointFreeOrderThreeField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSemilinearCoordinates
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts5A
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts5B
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts5C
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Z3F4Facts5D

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.LinearAlgebra CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear Subgroup

theorem s16h_e3_z3_order_five {F : Subgroup (Matrix.GeneralLinearGroup (Fin 3) OmegaField)}
    (hF : Nat.card ↥F = 5) :
    ∃ P : Subgroup (Matrix.GeneralLinearGroup (Fin 3) OmegaField),
      Nat.card ↥P = 9 ∧ (∀ a ∈ P, a ^ 3 = 1) ∧ (∀ a ∈ P, ∀ b ∈ P, a * b = b * a) ∧
      (∀ a : Matrix.GeneralLinearGroup (Fin 3) OmegaField,
        a ∈ normalizer (F : Set (Matrix.GeneralLinearGroup (Fin 3) OmegaField)) → a ^ 3 = 1 →
          a ∈ P) ∧
      (∀ τ : coordinateSemilinearGroup 3 OmegaField,
        τ ∈ normalizer (Subgroup.map
          (SemidirectProduct.inl : Matrix.GeneralLinearGroup (Fin 3) OmegaField →*
            coordinateSemilinearGroup 3 OmegaField) F :
              Set (coordinateSemilinearGroup 3 OmegaField)) →
          SemidirectProduct.rightHom τ ≠ 1 →
          ∀ a ∈ P, τ * SemidirectProduct.inl a * τ⁻¹ = SemidirectProduct.inl a⁻¹) := by
  classical
  haveI hfinF : Finite ↥F := Nat.finite_of_card_ne_zero (by rw [hF]; norm_num)
  have hne : F ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hF
    norm_num at hF
  obtain ⟨f, hfF, hf1⟩ : ∃ f : Matrix.GeneralLinearGroup (Fin 3) OmegaField, f ∈ F ∧ f ≠ 1 := by
    by_contra h
    apply hne
    rw [Subgroup.eq_bot_iff_forall]
    intro x hx
    by_contra hx1
    exact h ⟨x, hx, hx1⟩
  have hf5 : f ^ 5 = 1 := by
    have h1 : (⟨f, hfF⟩ : ↥F) ^ Nat.card ↥F = 1 := pow_card_eq_one'
    rw [hF] at h1
    simpa using h1
  have hford : orderOf f = 5 := by
    have hdvd : orderOf f ∣ 5 := orderOf_dvd_of_pow_eq_one hf5
    rcases (Nat.dvd_prime Nat.prime_five).mp hdvd with h | h
    · exact absurd (orderOf_eq_one_iff.mp h) hf1
    · exact h
  have hFz : F = Subgroup.zpowers f := by
    refine (Subgroup.eq_of_le_of_card_ge (Subgroup.zpowers_le.mpr hfF) ?_).symm
    rw [hF, Nat.card_zpowers, hford]
  let fL : (Module.End OmegaField (Fin 3 → OmegaField))ˣ := Matrix.GeneralLinearGroup.toLin f
  have hfL5 : (fL : Module.End OmegaField (Fin 3 → OmegaField)) ^ 5 = 1 := by
    have h1 : fL ^ 5 = 1 := by rw [← map_pow, hf5, map_one]
    exact congrArg Units.val h1
  have hfL1 : (fL : Module.End OmegaField (Fin 3 → OmegaField)) ≠ 1 := by
    intro h
    apply hf1
    apply Matrix.GeneralLinearGroup.toLin.injective
    rw [map_one]
    exact Units.ext h
  have hfin : Module.finrank OmegaField (Fin 3 → OmegaField) = 3 := by simp
  let Q : Subgroup (Module.End OmegaField (Fin 3 → OmegaField))ˣ :=
    (s16h_e3_z3f5_diagHom hfL5).range
  let P : Subgroup (Matrix.GeneralLinearGroup (Fin 3) OmegaField) :=
    Q.map (Matrix.GeneralLinearGroup.toLin.symm.toMonoidHom)
  have hmemP : ∀ a : Matrix.GeneralLinearGroup (Fin 3) OmegaField,
      a ∈ P ↔ Matrix.GeneralLinearGroup.toLin a ∈ Q := by
    intro a
    constructor
    · intro ha
      rcases Subgroup.mem_map.mp ha with ⟨q, hq, hqa⟩
      rw [← hqa]
      simpa using hq
    · intro ha
      exact Subgroup.mem_map.mpr ⟨Matrix.GeneralLinearGroup.toLin a, ha, by simp⟩
  refine ⟨P, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Subgroup.card_map_of_injective (MulEquiv.injective _)]
    exact s16h_e3_z3f5_card_diagHom_range hfin hfL5 hfL1
  · intro a ha
    have hQ : Matrix.GeneralLinearGroup.toLin a ∈ Q := (hmemP a).mp ha
    rcases MonoidHom.mem_range.mp hQ with ⟨p, hp⟩
    have haeq : a = Matrix.GeneralLinearGroup.toLin.symm (s16h_e3_z3f5_diagHom hfL5 p) := by
      rw [hp, MulEquiv.symm_apply_apply]
    rw [haeq, ← map_pow (Matrix.GeneralLinearGroup.toLin.symm),
      s16h_e3_z3f5_diagHom_pow_three hfL5 p, map_one]
  · intro a ha b hb
    have hQa : Matrix.GeneralLinearGroup.toLin a ∈ Q := (hmemP a).mp ha
    have hQb : Matrix.GeneralLinearGroup.toLin b ∈ Q := (hmemP b).mp hb
    rcases MonoidHom.mem_range.mp hQa with ⟨p, hp⟩
    rcases MonoidHom.mem_range.mp hQb with ⟨q, hq⟩
    apply Matrix.GeneralLinearGroup.toLin.injective
    rw [map_mul, map_mul, ← hp, ← hq]
    exact s16h_e3_z3f5_diagHom_comm hfL5 p q
  · intro a haN ha3
    refine (hmemP a).mpr (s16h_e3_z3f5_three_element_mem hfin hfL5 hfL1 ?_ ?_)
    · rw [← map_pow, ha3, map_one]
    · have hnorm : a * f * a⁻¹ ∈ Subgroup.zpowers f := by
        rw [hFz] at haN
        exact ((Subgroup.mem_normalizer_iff.mp haN) f).1 (Subgroup.mem_zpowers f)
      have h : Matrix.GeneralLinearGroup.toLin (a * f * a⁻¹) ∈
          Subgroup.map Matrix.GeneralLinearGroup.toLin.toMonoidHom (Subgroup.zpowers f) :=
        Subgroup.mem_map.mpr ⟨a * f * a⁻¹, hnorm, rfl⟩
      simpa [fL, MonoidHom.map_zpowers, map_mul, map_inv] using h
  · intro τ hτN hτright a haP
    have hQ : Matrix.GeneralLinearGroup.toLin a ∈ Q := (hmemP a).mp haP
    have hτnorm : τ ∈ Subgroup.normalizer
        (Subgroup.zpowers (SemidirectProduct.inl f : coordinateSemilinearGroup 3 OmegaField) :
          Set (coordinateSemilinearGroup 3 OmegaField)) := by
      rw [hFz, MonoidHom.map_zpowers] at hτN
      exact hτN
    exact s16h_e3_z3f5_semilinear_inverts hfL5 hfL1 hτnorm hτright hQ

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
