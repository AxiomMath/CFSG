module

public import CFSG.RankThree.PartTwo.Sec17.F174L3AutCls

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open scoped MatrixGroups Matrix

theorem s16c1_G47_cube_five {F : Type} [Field F] [Finite F] (hF : Nat.card F = 5) :
    ∀ r : F, r ^ 3 = 1 → r = 1 := by
  classical
  haveI : Fintype F := Fintype.ofFinite F
  intro r hr
  have hr0 : r ≠ 0 := by
    rintro rfl
    simp at hr
  have h4 : r ^ 4 = 1 := by
    have h := FiniteField.pow_card_sub_one_eq_one r hr0
    rwa [Fintype.card_eq_nat_card, hF] at h
  have h5 : r ^ 4 = r ^ 3 * r := by ring
  rw [hr, h4] at h5
  simpa using h5.symm

theorem s16c1_G47_L3_cls {F : Type} [Field F] [Finite F] (hF : Nat.card F = 5)
    (σ : MulAut SL(3, F)) :
    (∃ B : GL (Fin 3) F, ∀ s : SL(3, F), ((σ s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (B : Matrix (Fin 3) (Fin 3) F) * (s : Matrix (Fin 3) (Fin 3) F) *
        ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) ∨
    (∃ B : GL (Fin 3) F, ∀ s : SL(3, F), ((σ s : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (B : Matrix (Fin 3) (Fin 3) F) * ((s⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F).transpose *
        ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F)) := by
  classical
  have hcube := s16c1_G47_cube_five hF
  haveI : Fact (Nat.Prime 5) := ⟨by norm_num⟩
  have hsub : Subsingleton (F ≃+* F) := by
    have hord : addOrderOf (1 : F) = 5 := by
      have hdvd : addOrderOf (1 : F) ∣ 5 := hF ▸ addOrderOf_dvd_natCard (1 : F)
      rcases (Nat.dvd_prime Fact.out).mp hdvd with h | h
      · simp at h
      · exact h
    have htop : AddSubgroup.zmultiples (1 : F) = ⊤ := by
      apply AddSubgroup.eq_top_of_card_eq
      rw [Nat.card_zmultiples, hord, hF]
    refine ⟨fun τ τ' => ?_⟩
    ext x
    have hx : x ∈ AddSubgroup.zmultiples (1 : F) := htop ▸ AddSubgroup.mem_top x
    obtain ⟨n, rfl⟩ := AddSubgroup.mem_zmultiples_iff.mp hx
    simp
  obtain ⟨-, hgen⟩ := CFSG.LocalAnalysis.ComponentInitial.LinearFlag.automorphism_generation
    (K := F) (n := 3) (by norm_num)
  obtain ⟨A, τ, ε, hε, hσ⟩ := hgen
    (MulAut.congr (CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Tr.projEquiv hcube) σ)
  have hτ : τ = 1 := Subsingleton.elim _ _
  interval_cases ε
  · left
    refine ⟨A, CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Tr.formula_conj hcube σ A ?_⟩
    rw [hσ, hτ, map_one, pow_zero, mul_one, mul_one]
  · right
    refine ⟨A, CFSG.RankThree.PartTwo.Sec17.F174L3Aut.Tr.formula_dual hcube σ A ?_⟩
    rw [hσ, hτ, map_one, pow_one, mul_one]

theorem s16c1_G47_gl_scale {F : Type} [Field F] [Finite F] (hF : Nat.card F = 5)
    (B : GL (Fin 3) F) :
    ∃ g : SL(3, F), ∀ s : SL(3, F), ((g * s * g⁻¹ : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) =
      (B : Matrix (Fin 3) (Fin 3) F) * (s : Matrix (Fin 3) (Fin 3) F) *
        ((B⁻¹ : GL (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) := by
  have hcube := s16c1_G47_cube_five hF
  have hinj : Function.Injective (fun u : Fˣ => u ^ 3) := by
    intro a b hab
    have h1 : (a * b⁻¹) ^ 3 = 1 := by
      simp only at hab
      rw [mul_pow, inv_pow, hab, mul_inv_cancel]
    have h2 : ((a * b⁻¹ : Fˣ) : F) = 1 := hcube _ (by simpa using congrArg Units.val h1)
    exact mul_inv_eq_one.mp (Units.ext h2)
  obtain ⟨u, hu⟩ := Finite.injective_iff_surjective.mp hinj (Matrix.GeneralLinearGroup.det B)
  simp only at hu
  set z : GL (Fin 3) F := Matrix.GeneralLinearGroup.scalar (Fin 3) u⁻¹ with hzdef
  have hker : z * B ∈ (Matrix.GeneralLinearGroup.det : GL (Fin 3) F →* Fˣ).ker := by
    rw [MonoidHom.mem_ker, map_mul, hzdef, Matrix.GeneralLinearGroup.det_scalar, Fintype.card_fin,
      inv_pow, hu, inv_mul_cancel]
  rw [← Matrix.SpecialLinearGroup.range_toGL_eq_ker_det] at hker
  obtain ⟨g, hg⟩ := hker
  refine ⟨g, fun s => ?_⟩
  have hz : ∀ A : GL (Fin 3) F, z * A = A * z := Matrix.GeneralLinearGroup.scalar_commute _
  have h : Matrix.SpecialLinearGroup.toGL (g * s * g⁻¹) =
      B * Matrix.SpecialLinearGroup.toGL s * B⁻¹ := by
    calc Matrix.SpecialLinearGroup.toGL (g * s * g⁻¹)
        = (z * B) * Matrix.SpecialLinearGroup.toGL s * (z * B)⁻¹ := by
          rw [map_mul, map_mul, map_inv, hg]
      _ = z * (B * Matrix.SpecialLinearGroup.toGL s * B⁻¹) * z⁻¹ := by group
      _ = B * Matrix.SpecialLinearGroup.toGL s * B⁻¹ := by
          rw [hz (B * Matrix.SpecialLinearGroup.toGL s * B⁻¹)]
          group
  have h' := congrArg (fun y : GL (Fin 3) F => (y : Matrix (Fin 3) (Fin 3) F)) h
  simpa only [Matrix.SpecialLinearGroup.coe_GL_coe_matrix, Units.val_mul] using h'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
