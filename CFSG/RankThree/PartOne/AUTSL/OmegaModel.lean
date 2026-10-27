module

public import CFSG.RankThree.PartOne.KC.OrthogonalAutSemilinearTags
public import CFSG.RankThree.PartOne.AUTSL.Transport

public section

namespace CFSG.RankThree.PartOne.AUTSL

open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  CFSG.LocalAnalysis.ComponentInitial.OrthogonalTail CFSG.ClassicalGroups.Orthogonal
  CFSG.Assembly.LowTwoRank Matrix

section Model

variable {K : Type} [Field K]

theorem matrixDerived_eq_statedOmega {d : ℕ} (Q : QuadraticForm K (Fin d → K)) :
    matrixDerived Q = StatedOmega ⇑Q := by
  rw [statedOmega_eq_comap rfl]
  have key : ∀ H : Subgroup ((Fin d → K) ≃ₗ[K] (Fin d → K)),
      H.comap (toLinEquiv (Fin d) K).toMonoidHom = H.map (toLinEquiv (Fin d) K).symm.toMonoidHom :=
    fun H => Subgroup.comap_equiv_eq_map_symm (toLinEquiv (Fin d) K) H
  unfold matrixDerived matrixIsometries
  change ⁅Subgroup.comap (toLinEquiv (Fin d) K).toMonoidHom _,
    Subgroup.comap (toLinEquiv (Fin d) K).toMonoidHom _⁆ = _
  rw [key, key, Subgroup.map_commutator]

theorem exists_ne_zero_of_polar_nondegenerate {d : ℕ} (hd : 0 < d) (Q : QuadraticForm K (Fin d → K))
    (hnd : (QuadraticMap.polarBilin Q).Nondegenerate) : ∃ v, Q v ≠ 0 := by
  by_contra hall
  push Not at hall
  have h1 : ∀ v w, QuadraticMap.polar Q v w = 0 := fun v w => by
    simp only [QuadraticMap.polar, hall, sub_self]
  have h2 : (Pi.single ⟨0, hd⟩ 1 : Fin d → K) = 0 := by
    refine hnd.1 _ fun w => ?_
    rw [QuadraticMap.polarBilin_apply_apply, h1]
  have := congrFun h2 ⟨0, hd⟩
  simp at this

variable [Finite K] [CharP K 2]

omit [Finite K] in
theorem matrixDerivedScalars_eq_bot {d : ℕ} (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) : matrixDerivedScalars Q = ⊥ := by
  refine (Subgroup.eq_bot_iff_forall _).2 fun A hA => ?_
  obtain ⟨c, hc⟩ := (mem_matrixDerivedScalars_iff Q A).1 hA
  have hAiso : A.val ∈ matrixIsometries Q := matrixDerived_le_isometries Q A.2
  obtain ⟨v, hv⟩ := hQ
  rw [mem_matrixIsometries_iff] at hAiso
  have h1 := hAiso v
  have h2 : Q ((matrixLinearEquiv A.val) v) = (c : K) * (c : K) * Q v := by
    have : matrixLinearEquiv A.val v = (c : K) • v := by
      rw [← hc]
      ext i
      simp [matrixLinearEquiv, Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
        Matrix.mulVec_diagonal]
    rw [this, QuadraticMap.map_smul, smul_eq_mul]
  rw [h2] at h1
  have h3 : ((c : K) * (c : K) - 1) * Q v = 0 := by linear_combination h1
  have h4 : (c : K) * (c : K) = 1 := by
    rcases mul_eq_zero.1 h3 with h | h
    · exact sub_eq_zero.1 h
    · exact absurd h hv
  have h5 : (c : K) = 1 := by
    have : ((c : K) - 1) ^ 2 = 0 := by
      have h2' : (2 : K) = 0 := by exact_mod_cast CharP.cast_eq_zero K 2
      linear_combination h4 + (1 - (c : K)) * h2'
    have h6 : (c : K) - 1 = 0 := pow_eq_zero_iff (two_ne_zero) |>.1 this
    exact sub_eq_zero.1 h6
  have h7 : c = 1 := Units.ext h5
  apply Subtype.ext
  rw [← hc, h7, map_one]
  rfl

@[expose] noncomputable def derivedProjEquiv {d : ℕ} (Q : QuadraticForm K (Fin d → K))
    (hQ : ∃ v, Q v ≠ 0) : matrixDerived Q ≃* matrixProjectiveDerived Q :=
  MulEquiv.ofBijective (matrixProjectiveProjection Q)
    ⟨(MonoidHom.ker_eq_bot_iff _).1 (by
        have : (matrixProjectiveProjection Q).ker = matrixDerivedScalars Q :=
          QuotientGroup.ker_mk' _
        rw [this]
        exact matrixDerivedScalars_eq_bot Q hQ),
      matrixProjectiveProjection_surjective Q⟩

omit [Finite K] in
theorem derivedProjEquiv_apply {d : ℕ} (Q : QuadraticForm K (Fin d → K)) (hQ : ∃ v, Q v ≠ 0)
    (A : matrixDerived Q) : derivedProjEquiv Q hQ A = matrixProjectiveProjection Q A := rfl

theorem exists_matrix_form_omega (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    {Γ : Subgroup (GL (Fin (2 * 4)) K)}
    (hΓ : Γ = matrixDerived (coordinateQuadMinus 4 K (by norm_num) b c))
    (α : MulAut Γ) : ∃ (A : GL (Fin (2 * 4)) K) (σ : K ≃+* K), ∀ g : Γ,
      (((α g : Γ) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
        (A : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) *
          (((g : Γ) : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K).map σ *
          ((A⁻¹ : GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) := by
  subst hΓ
  have h14 : (1 : ℕ) ≤ 4 := by norm_num
  have hreg := regular_coordinateQuadMinus 4 K b c (le_refl 4) hirr
  have hQ : ∃ v, coordinateQuadMinus 4 K h14 b c v ≠ 0 :=
    exists_ne_zero_of_polar_nondegenerate (by norm_num) _ hreg.1
  have htop := CFSG.RankThree.PartOne.KCOrthogonalAut.matrixProjectiveImage_eq_top_minus K 4
    (le_refl 4) b c hirr
  let Φ := derivedProjEquiv (coordinateQuadMinus 4 K h14 b c) hQ
  have hmem : MulAut.congr Φ α ∈ matrixProjectiveImage (coordinateQuadMinus 4 K h14 b c) := by
    rw [htop]
    exact Subgroup.mem_top _
  obtain ⟨g, hg⟩ := (mem_matrixProjectiveImage_iff _ _).1 hmem
  refine ⟨g.val.left, g.val.right, fun A => ?_⟩
  have h1 : Φ (α A) = Φ (matrixDerivedConjugation (coordinateQuadMinus 4 K h14 b c) g A) := by
    have h2 : MulAut.congr Φ α (Φ A) = Φ (α A) := congr_apply_apply' Φ α A
    rw [← h2, ← hg]
    show matrixProjectiveConjugation _ g (matrixProjectiveProjection _ A) =
      matrixProjectiveProjection _ _
    exact matrixProjectiveConjugation_mk _ g A
  have h3 := Φ.injective h1
  have h4 : (((α A : matrixDerived (coordinateQuadMinus 4 K h14 b c)) :
      GL (Fin (2 * 4)) K) : Matrix (Fin (2 * 4)) (Fin (2 * 4)) K) =
      ((matrixDerivedConjugation (coordinateQuadMinus 4 K h14 b c) g A :
        matrixDerived (coordinateQuadMinus 4 K h14 b c)) : GL (Fin (2 * 4)) K).val := by
    rw [h3]
  rw [h4, matrixDerivedConjugation_val, Units.val_mul, Units.val_mul]
  rfl

omit [Finite K] [CharP K 2] in
theorem omega_witt (b c : K) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (T : Submodule K (Fin (2 * 4) → K))
    (hT : ∀ x ∈ T, coordinateQuadMinus 4 K (by norm_num) b c x = 0) :
    Module.finrank K T ≤ 3 := by
  have h14 : (1 : ℕ) ≤ 4 := by norm_num
  let ψ : (quadTail (4 - 1) (minusTailForm K b c)).IsometryEquiv
      (coordinateQuadMinus 4 K h14 b c) :=
    (minusTailIsometry 4 K b c).trans (coordinateMinusIsometry 4 K h14 b c)
  have h1 := finrank_le_of_totSing_tail (anisotropic_minusTailForm hirr)
    (totSing_map_symm ψ rfl hT)
  have h2 := LinearEquiv.finrank_map_eq ψ.symm.toLinearEquiv T
  have h3 : Module.finrank K (T.map ψ.symm.toLinearMap) = Module.finrank K T := h2
  omega

end Model

end CFSG.RankThree.PartOne.AUTSL
