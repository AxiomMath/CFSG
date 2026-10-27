module

public import CFSG.LocalAnalysis.StandardType.GGSixAutSteinberg
public import CFSG.LocalAnalysis.StandardType.GGRootCentralizerOmegaSpin
public import CFSG.LocalAnalysis.StandardType.GGPsiDiagInnerMinus
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataReindexGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates

public section

namespace CFSG.StandardType

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted
  CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData CFSG.ClassicalGroups.Orthogonal
  CFSG.Assembly.LowTwoRank

namespace AutOm

section Model

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {d : ℕ}

theorem reindex_spinMatrix_mem (e : ι ≃ Fin d) (Q₀ : QuadraticForm K (ι → K))
    (hR : (spinMatrix Q₀).range = StatedOmega ⇑Q₀) (x : spinGroup Q₀) :
    reindexMatrixEquiv e (spinMatrix Q₀ x) ∈ matrixDerived (reindexQuadraticForm e Q₀) := by
  rw [← stated_derived_reindex, ← hR]
  exact ⟨spinMatrix Q₀ x, ⟨x, rfl⟩, rfl⟩

@[expose] noncomputable def spinModel (e : ι ≃ Fin d) (Q₀ : QuadraticForm K (ι → K))
    (hR : (spinMatrix Q₀).range = StatedOmega ⇑Q₀) :
    spinGroup Q₀ →* matrixDerived (reindexQuadraticForm e Q₀) :=
  ((reindexMatrixEquiv e).toMonoidHom.comp (spinMatrix Q₀)).codRestrict _
    (reindex_spinMatrix_mem e Q₀ hR)

theorem spinModel_val (e : ι ≃ Fin d) (Q₀ : QuadraticForm K (ι → K))
    (hR : (spinMatrix Q₀).range = StatedOmega ⇑Q₀) (x : spinGroup Q₀) :
    (spinModel e Q₀ hR x : GL (Fin d) K) = reindexMatrixEquiv e (spinMatrix Q₀ x) := rfl

theorem spinModel_mulVec (e : ι ≃ Fin d) (Q₀ : QuadraticForm K (ι → K))
    (hR : (spinMatrix Q₀).range = StatedOmega ⇑Q₀) (x : spinGroup Q₀) (v : ι → K) :
    Matrix.mulVec ((spinModel e Q₀ hR x : GL (Fin d) K) : Matrix (Fin d) (Fin d) K)
      (reindexVectorEquiv e v) = reindexVectorEquiv e (spinAction Q₀ x v) := by
  rw [spinModel_val, ← spinMatrix_mulVec, ← reindexMatrixEquiv_mulVec, matrixLinearEquiv_apply]

theorem spinModel_surjective (e : ι ≃ Fin d) (Q₀ : QuadraticForm K (ι → K))
    (hR : (spinMatrix Q₀).range = StatedOmega ⇑Q₀) :
    Function.Surjective (spinModel e Q₀ hR) := by
  rintro ⟨A, hA⟩
  rw [← stated_derived_reindex, ← hR] at hA
  obtain ⟨_, ⟨x, rfl⟩, rfl⟩ := hA
  exact ⟨x, rfl⟩

theorem spinModel_injective (e : ι ≃ Fin d) (Q₀ : QuadraticForm K (ι → K))
    (hR : (spinMatrix Q₀).range = StatedOmega ⇑Q₀)
    (hinj : Function.Injective (spinAction Q₀)) : Function.Injective (spinModel e Q₀ hR) := by
  intro x y hxy
  apply hinj
  refine LinearEquiv.ext fun v => (reindexVectorEquiv (K := K) e).injective ?_
  rw [← spinModel_mulVec e Q₀ hR, ← spinModel_mulVec e Q₀ hR, hxy]

end Model

section Minus

variable {K : Type} [Field K] [Finite K] {n : ℕ} {b c : K}

theorem range_spinMatrix_minus (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (spinMatrix (quadMinus n K b c)).range = StatedOmega ⇑(quadMinus n K b c) := by
  rw [coe_quadMinus]
  exact range_spinMatrix_quadMinus hn hirr

@[expose] noncomputable def spinModelMinus (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    spinGroup (quadMinus n K b c) →* matrixDerived (coordinateQuadMinus n K (by omega) b c) :=
  spinModel (minusIndexEquiv n (by omega)) (quadMinus n K b c) (range_spinMatrix_minus hn hirr)

theorem spinModelMinus_mulVec (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (x : spinGroup (quadMinus n K b c)) (v : Vm n K) :
    Matrix.mulVec ((spinModelMinus hn hirr x : GL (Fin (2 * n)) K) :
        Matrix (Fin (2 * n)) (Fin (2 * n)) K)
          (reindexVectorEquiv (minusIndexEquiv n (by omega)) v) =
      reindexVectorEquiv (minusIndexEquiv n (by omega)) (spinAction (quadMinus n K b c) x v) :=
  spinModel_mulVec _ _ _ x v

theorem spinModelMinus_surjective (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Function.Surjective (spinModelMinus hn hirr) :=
  spinModel_surjective _ _ _

variable [CharP K 2]

theorem spinModelMinus_injective (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Function.Injective (spinModelMinus hn hirr) :=
  spinModel_injective _ _ _ (RootCentOmega.spinAction_quadMinus_injective hirr)

theorem ker_spinModelMinus (hn : 4 ≤ n) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    (spinModelMinus hn hirr).ker = Subgroup.center (spinGroup (quadMinus n K b c)) := by
  rw [(MonoidHom.ker_eq_bot_iff _).2 (spinModelMinus_injective hn hirr),
    PsiDiag.SpinM.center_eq_bot hirr hn]

end Minus

section Plane

variable {K : Type} [Field K] {n : ℕ}

theorem reindex_planeOne (hn : 1 ≤ n) :
    reindexVectorEquiv (minusIndexEquiv n hn) (planeVec n (planeOne : Fin 2 → K)) =
      Pi.single (minusIndexEquiv n hn (.inr (.inr 0))) 1 := by
  funext k
  rw [reindexVectorEquiv_apply]
  obtain ⟨x, rfl⟩ := (minusIndexEquiv n hn).surjective k
  rw [Equiv.symm_apply_apply]
  by_cases hx : x = .inr (.inr 0)
  · subst hx
    simp [planeVec, planeOne]
  · rw [Pi.single_eq_of_ne ((minusIndexEquiv n hn).injective.ne hx)]
    rcases x with i | i | t
    · rfl
    · rfl
    · have ht : t = 1 := by
        fin_cases t
        · exact absurd rfl hx
        · rfl
      subst ht
      simp [planeVec, planeOne]

end Plane

end AutOm

end CFSG.StandardType
