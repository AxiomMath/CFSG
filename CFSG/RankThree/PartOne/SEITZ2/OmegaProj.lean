module

public import CFSG.RankThree.PartOne.KC.OrthogonalCommutatorBridge
public import CFSG.RankThree.PartOne.S11d.LieCentralizerOrth
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix QuadraticMap CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.RankThree.PartOne.KCOrthComm CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
open CFSG.ComponentClassification.CatalogueBOrthogonalFixedTransfer (matrixLinearEquiv_scalar)
open CFSG.ComponentClassification.CatalogueBHigherLinearField (glFieldAut)

section Proj

variable {K : Type} [Field K] [CharP K 2] {d : ℕ} [NeZero d]
  {Q : QuadraticForm K (Fin d → K)}

@[expose] noncomputable def projLin (hQ : (polarBilin Q).Nondegenerate) :
    matrixProjectiveDerived Q →* ((Fin d → K) ≃ₗ[K] (Fin d → K)) :=
  QuotientGroup.lift (matrixDerivedScalars Q)
    ((orthDerived Q).subtype.comp (matrixDerivedEquiv Q).toMonoidHom) (fun A hA => by
      have h := (mem_matrixDerivedScalars_iff_scalars Q A).mp hA
      exact eq_one_of_mem_scalars_of_mem_orthDerived hQ (matrixDerivedEquiv Q A).2
        (Subgroup.mem_subgroupOf.mp h))

theorem projLin_mk (hQ : (polarBilin Q).Nondegenerate) (A : matrixDerived Q) :
    projLin hQ (matrixProjectiveProjection Q A) = matrixLinearIso A.val := rfl

theorem projLin_injective (hQ : (polarBilin Q).Nondegenerate) :
    Function.Injective (projLin hQ) := by
  intro x y h
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q x
  obtain ⟨B, rfl⟩ := matrixProjectiveProjection_surjective Q y
  rw [projLin_mk, projLin_mk] at h
  have : A = B := Subtype.ext (matrixLinearIso.injective h)
  rw [this]

theorem mem_range_projLin (hQ : (polarBilin Q).Nondegenerate)
    {X : (Fin d → K) ≃ₗ[K] (Fin d → K)} : X ∈ (projLin hQ).range ↔ X ∈ orthDerived Q := by
  constructor
  · rintro ⟨t, rfl⟩
    obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q t
    rw [projLin_mk]
    exact (matrixDerivedEquiv Q A).2
  · intro hX
    obtain ⟨A, hA⟩ := (matrixDerivedEquiv Q).surjective ⟨X, hX⟩
    exact ⟨matrixProjectiveProjection Q A, by rw [projLin_mk]; exact congrArg Subtype.val hA⟩

theorem exists_isometry_projLin_conj [Finite K] (hQ : (polarBilin Q).Nondegenerate)
    (g : linearSimilarityPairs Q) :
    ∃ G ∈ TauCeti.QuadraticMap.orthogonalGroup Q, ∀ t : matrixProjectiveDerived Q,
      projLin hQ (matrixProjectiveConjugationHom Q g.1 t) = G * projLin hQ t * G⁻¹ := by
  have hr : g.1.val.right = 1 := (mem_linearSimilarityPairs_iff Q g.1).mp g.2
  obtain ⟨mu, hmu⟩ := g.1.2
  have hmu' : ∀ v, Q (g.1.val.left.val *ᵥ v) = (mu : K) * Q v := fun v => by
    have := hmu v
    rw [coordinateSemilinearMap_apply, hr] at this
    exact this
  obtain ⟨r, hr2⟩ := FiniteField.isSquare_of_char_two (ringChar.eq K 2) ((mu⁻¹ : Kˣ) : K)
  have hr0 : r ≠ 0 := fun h0 => by
    rw [h0, mul_zero] at hr2
    exact (mu⁻¹).ne_zero hr2
  set s : GL (Fin d) K := GeneralLinearGroup.scalar (Fin d) (Units.mk0 r hr0) with hs
  set L : GL (Fin d) K := g.1.val.left with hL
  have hsc : ∀ X : GL (Fin d) K, s * X = X * s := by
    intro X
    have hmem : s ∈ Subgroup.center (GL (Fin d) K) := by
      rw [GeneralLinearGroup.center_eq_range_scalar]
      exact ⟨Units.mk0 r hr0, rfl⟩
    exact (Subgroup.mem_center_iff.mp hmem X).symm
  have hG₀ : s * L ∈ matrixIsometries Q := by
    rw [mem_matrixIsometries_iff]
    intro v
    rw [matrixLinearEquiv_mul, LinearEquiv.mul_apply, hs, matrixLinearEquiv_scalar,
      QuadraticMap.map_smul, smul_eq_mul]
    change r * r * Q (L.val *ᵥ v) = Q v
    rw [hmu' v, ← mul_assoc, ← hr2]
    have : ((mu⁻¹ : Kˣ) : K) * (mu : K) = 1 := by simp
    rw [this, one_mul]
  refine ⟨matrixLinearIso (s * L), hG₀, fun t => ?_⟩
  obtain ⟨A, rfl⟩ := matrixProjectiveProjection_surjective Q t
  change projLin hQ (matrixProjectiveConjugation Q g.1 (matrixProjectiveProjection Q A)) = _
  rw [matrixProjectiveConjugation_mk, projLin_mk, projLin_mk, matrixDerivedConjugation_val, hr]
  have h1 : glFieldAut (Fin d) K (1 : K ≃+* K) A.val = A.val := by
    rw [map_one]
    rfl
  rw [h1, ← map_inv, ← map_mul, ← map_mul]
  congr 1
  calc L * A.val * L⁻¹ = (L * A.val * L⁻¹) * (s * s⁻¹) := by group
    _ = ((L * A.val * L⁻¹) * s) * s⁻¹ := by group
    _ = (s * (L * A.val * L⁻¹)) * s⁻¹ := by rw [hsc]
    _ = s * L * A.val * (s * L)⁻¹ := by group

end Proj

end CFSG.RankThree.PartOne.SEITZ2
