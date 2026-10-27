module

public import CFSG.RankThree.Classical2.NegativeExchangedSL3

public section

namespace CFSG.RankThree.PartOne.KETw3

open Matrix CFSG.RankThree.Classical CFSG.RankThree.Classical2
open scoped MatrixGroups

theorem eq_of_central_discrepancy {Γ G : Type*} [Group Γ] [Group G] [hΓ : Group.IsPerfect Γ]
    (f₁ f₂ : Γ →* G) (Z : Subgroup G) (hZ : Z ≤ Subgroup.center G)
    (h : ∀ A : Γ, ∃ z ∈ Z, f₁ A = z * f₂ A) : f₁ = f₂ := by
  choose z hzZ hz using h
  have hzc : ∀ A (x : G), z A * x = x * z A := fun A x =>
    (Subgroup.mem_center_iff.1 (hZ (hzZ A)) x).symm
  have hzmul : ∀ A B, z (A * B) = z A * z B := by
    intro A B
    have e1 := hz (A * B)
    rw [map_mul, hz A, hz B] at e1
    have e2 : z A * f₂ A * (z B * f₂ B) = z A * z B * f₂ (A * B) := by
      rw [map_mul, mul_assoc, ← mul_assoc (f₂ A) (z B), (hzc B (f₂ A)).symm, mul_assoc, mul_assoc]
    exact mul_right_cancel (e1.symm.trans e2)
  let g : Γ →* G := MonoidHom.mk' z hzmul
  have hk : commutator Γ ≤ g.ker := by
    rw [commutator_def]
    refine Subgroup.commutator_le.2 fun a _ b _ => ?_
    rw [MonoidHom.mem_ker, map_commutatorElement, commutatorElement_eq_one_iff_mul_comm]
    exact hzc a (z b)
  refine MonoidHom.ext fun A => ?_
  have hA : g A = 1 := hk Group.IsPerfect.mem_commutator
  have hzA : z A = 1 := hA
  rw [hz A, hzA, one_mul]

theorem scalar_range_le_center {Ω : Type} [Field Ω] {n : ℕ} :
    (Matrix.GeneralLinearGroup.scalar (Fin n) : Ωˣ →* GL (Fin n) Ω).range ≤
      Subgroup.center (GL (Fin n) Ω) := by
  rintro _ ⟨u, rfl⟩
  rw [Subgroup.mem_center_iff]
  intro g
  apply Units.ext
  rw [Units.val_mul, Units.val_mul, Matrix.GeneralLinearGroup.coe_scalar]
  exact (Matrix.scalar_commute (u : Ω) (fun _ => Commute.all _ _)
    (g : Matrix (Fin n) (Fin n) Ω)).symm.eq

theorem exists_discrepancy_conj {Ω : Type} [Field Ω] {Γ : Type*} {T X : Γ → GL (Fin 3) Ω}
    (M a : GL (Fin 3) Ω)
    (h : ∀ A : Γ, ∃ z ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3) : Ωˣ →* GL (Fin 3) Ω).range,
      M * T A * M⁻¹ = z * (a * X A * a⁻¹)) :
    ∀ A : Γ, ∃ z ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3) : Ωˣ →* GL (Fin 3) Ω).range,
      (a⁻¹ * M) * T A * (a⁻¹ * M)⁻¹ = z * X A := by
  intro A
  obtain ⟨z, hzZ, hz⟩ := h A
  refine ⟨z, hzZ, ?_⟩
  have hzc : z * a = a * z := (Subgroup.mem_center_iff.1 (scalar_range_le_center hzZ) a).symm
  calc (a⁻¹ * M) * T A * (a⁻¹ * M)⁻¹ = a⁻¹ * (M * T A * M⁻¹) * a := by group
    _ = a⁻¹ * (z * (a * X A * a⁻¹)) * a := by rw [hz]
    _ = (a⁻¹ * (z * a)) * X A := by group
    _ = z * X A := by rw [hzc]; group

theorem not_twisted_discrepancy_pos {Ω : Type} [Field Ω] (Fr : Ω →+* Ω)
    (hFr : Function.Bijective Fr) (k₂ : Subfield Ω) (M a : GL (Fin 3) Ω)
    (h : ∀ A : SL(3, k₂), ∃ z ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3) :
        Ωˣ →* GL (Fin 3) Ω).range,
      M * Matrix.SpecialLinearGroup.toGL (invTransposeMapSL Fr 3
        (Matrix.SpecialLinearGroup.map k₂.subtype A)) * M⁻¹ =
        z * (a * Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map k₂.subtype A) *
          a⁻¹)) :
    False := by
  have : Group.IsPerfect SL(3, k₂) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (le_refl 3)
  have h' := exists_discrepancy_conj (T := fun A : SL(3, k₂) => Matrix.SpecialLinearGroup.toGL
    (invTransposeMapSL Fr 3 (Matrix.SpecialLinearGroup.map k₂.subtype A)))
    (X := fun A : SL(3, k₂) => Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.map k₂.subtype A)) M a h
  set M₀ : GL (Fin 3) Ω := a⁻¹ * M with hM₀
  let f₁ : SL(3, k₂) →* GL (Fin 3) Ω := (MulAut.conj M₀).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.toGL.comp ((invTransposeMapSL Fr 3).comp
      (Matrix.SpecialLinearGroup.map k₂.subtype)))
  let f₂ : SL(3, k₂) →* GL (Fin 3) Ω :=
    Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map k₂.subtype)
  have hf := eq_of_central_discrepancy f₁ f₂ _ scalar_range_le_center (fun A => by
    obtain ⟨z, hzZ, hz⟩ := h' A
    exact ⟨z, hzZ, by simpa [f₁, f₂, MulAut.conj_apply] using hz⟩)
  refine not_exists_conj_map_inv_transpose_naturalSL k₂ (le_refl 3) (RingEquiv.ofBijective Fr hFr)
    ⟨M₀, fun X hX => ?_⟩
  obtain ⟨A, rfl⟩ := hX
  have h1 := congrArg (fun g : GL (Fin 3) Ω => (g : Matrix (Fin 3) (Fin 3) Ω))
    (DFunLike.congr_fun hf A)
  simpa [f₁, f₂, MulAut.conj_apply, Units.val_mul, coe_invTransposeMapSL] using h1

theorem not_twisted_discrepancy_neg {Ω : Type} [Field Ω] (Fr : Ω →+* Ω)
    (hFr : Function.Bijective Fr) (k₂ : Subfield Ω) (htk : ∃ t ∈ k₂, Fr t ≠ t)
    (M a : GL (Fin 3) Ω)
    (h : ∀ A : SL(3, k₂), ∃ z ∈ (Matrix.GeneralLinearGroup.scalar (Fin 3) :
        Ωˣ →* GL (Fin 3) Ω).range,
      M * invTransposeHom (Matrix.SpecialLinearGroup.toGL (invTransposeMapSL Fr 3
        (Matrix.SpecialLinearGroup.map k₂.subtype A))) * M⁻¹ =
        z * (a * Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map k₂.subtype A) *
          a⁻¹)) :
    False := by
  have : Group.IsPerfect SL(3, k₂) :=
    CFSG.LinearGroups.special_linear_dimension_at_least_three_perfect (le_refl 3)
  have hinvT : ∀ X : SL(3, Ω), (invTransposeHom (Matrix.SpecialLinearGroup.toGL
      (invTransposeMapSL Fr 3 X)) : GL (Fin 3) Ω) =
        Matrix.SpecialLinearGroup.toGL (Matrix.SpecialLinearGroup.map Fr X) := by
    intro X
    apply Units.ext
    rw [coe_invTransposeHom, Matrix.coe_units_inv, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      coe_invTransposeMapSL, Matrix.SpecialLinearGroup.coe_GL_coe_matrix,
      Matrix.SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply]
    have hdet : IsUnit ((X : Matrix (Fin 3) (Fin 3) Ω).map Fr).det := isUnit_det_map Fr X
    rw [← Matrix.transpose_nonsing_inv, Matrix.nonsing_inv_nonsing_inv _ hdet,
      Matrix.transpose_transpose]
  have h' := exists_discrepancy_conj (T := fun A : SL(3, k₂) => Matrix.SpecialLinearGroup.toGL
    (Matrix.SpecialLinearGroup.map Fr (Matrix.SpecialLinearGroup.map k₂.subtype A)))
    (X := fun A : SL(3, k₂) => Matrix.SpecialLinearGroup.toGL
      (Matrix.SpecialLinearGroup.map k₂.subtype A)) M a (fun A => by
        obtain ⟨z, hzZ, hz⟩ := h A
        exact ⟨z, hzZ, by rwa [hinvT] at hz⟩)
  set M₀ : GL (Fin 3) Ω := a⁻¹ * M with hM₀
  let f₁ : SL(3, k₂) →* GL (Fin 3) Ω := (MulAut.conj M₀).toMonoidHom.comp
    (Matrix.SpecialLinearGroup.toGL.comp ((Matrix.SpecialLinearGroup.map Fr).comp
      (Matrix.SpecialLinearGroup.map k₂.subtype)))
  let f₂ : SL(3, k₂) →* GL (Fin 3) Ω :=
    Matrix.SpecialLinearGroup.toGL.comp (Matrix.SpecialLinearGroup.map k₂.subtype)
  have hf := eq_of_central_discrepancy f₁ f₂ _ scalar_range_le_center (fun A => by
    obtain ⟨z, hzZ, hz⟩ := h' A
    exact ⟨z, hzZ, by simpa [f₁, f₂, MulAut.conj_apply] using hz⟩)
  obtain ⟨-, hfix⟩ := scalar_and_eq_of_conj_map_naturalSL k₂ (le_refl 3)
    (RingEquiv.ofBijective Fr hFr) M₀ (fun X hX => by
      obtain ⟨A, rfl⟩ := hX
      have h1 := congrArg (fun g : GL (Fin 3) Ω => (g : Matrix (Fin 3) (Fin 3) Ω))
        (DFunLike.congr_fun hf A)
      simpa [f₁, f₂, MulAut.conj_apply, Units.val_mul] using h1)
  obtain ⟨t, ht, htF⟩ := htk
  exact htF (hfix t ht)

end CFSG.RankThree.PartOne.KETw3
