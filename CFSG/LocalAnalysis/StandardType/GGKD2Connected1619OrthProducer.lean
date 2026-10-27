module

public import CFSG.LocalAnalysis.StandardType.GGKD2Connected1619Contracts
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataReindexGroups
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointIsometryRegular
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalBasic
public import CFSG.LocalAnalysis.StandardType.GGTableBOrthogonalEndNode
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyOrthTorus
public import CFSG.LocalAnalysis.ComponentInitial.BasicFacts

public section

namespace S2MathAs3_1619Final

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Open S2MathAs3_1615
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
open CFSG.ClassicalGroups.Orthogonal

private theorem ltromp_matrixIsometries_eq_isometryCore {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) :
    matrixIsometries Q = CFSG.MatrixModel.isometryCore (⇑Q) := by
  have h : matrixLinearIso (d := d) (K := K) =
      CFSG.ClassicalGroups.Orthogonal.toLinEquiv (Fin d) K := rfl
  rw [matrixIsometries, CFSG.MatrixModel.isometryCore, h]
  exact (CFSG.ClassicalGroups.Orthogonal.closure_isometries_eq_comap
    (Q := Q) (Q₀ := ⇑Q) rfl).symm

private theorem ltromp_matrixDerived_eq_statedOmega {K : Type} [Field K] {d : ℕ}
    (Q : QuadraticForm K (Fin d → K)) : matrixDerived Q = StatedOmega ⇑Q := by
  simp only [matrixDerived, StatedOmega, CFSG.MatrixModel.isometryCore,
    ltromp_matrixIsometries_eq_isometryCore Q]

private noncomputable def ltromp_reindexEquiv {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {d : ℕ} (e : ι ≃ Fin d) (Q : QuadraticForm K (ι → K)) :
    StatedOmega ⇑Q ≃* StatedOmega ⇑(reindexQuadraticForm e Q) :=
  (statedMatrixDerivedEquiv e Q).trans
    (MulEquiv.subgroupCongr (ltromp_matrixDerived_eq_statedOmega (reindexQuadraticForm e Q)))

private noncomputable def ltromp_ePlus (m : ℕ) : Fin m ⊕ Fin m ≃ Fin (2 * m) :=
  (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)).trans (finCongr (by omega : m + m = 2 * m))

private noncomputable def ltromp_eMinus (m : ℕ) :
    (Fin m ⊕ Fin m) ⊕ Fin 2 ≃ Fin (2 * (m + 1)) :=
  (Equiv.sumCongr (finSumFinEquiv : Fin m ⊕ Fin m ≃ Fin (m + m)) (Equiv.refl (Fin 2))).trans
    ((finSumFinEquiv : Fin (m + m) ⊕ Fin 2 ≃ Fin ((m + m) + 2)).trans
      (finCongr (by omega : (m + m) + 2 = 2 * (m + 1))))

theorem orthProducer_holds :
    ∀ lab : LargeEvenLabel, LargeEvenInLambda2 lab → (lab.tag = .D ∨ lab.tag = .twD) →
      4 ≤ lab.rank →
        LargeEvenLabelAll lab (fun R _ I _ => OrthRawRealization lab R I) := by
  intro lab hlab htag hr4
  rcases lab with ⟨tag, rank, n⟩
  rcases htag with rfl | rfl
  ·
    have hr4' : 4 ≤ rank := by simpa using hr4
    have hn1 : 1 ≤ n := hlab.1
    intro Q hQ
    have h3 : ¬ rank = 3 := by omega
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    rw [if_neg h3] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hcard, hQF⟩ := hQ
    letI := hKf
    letI := hKfin
    haveI hChar : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn1
        hcard
    let e : Fin rank ⊕ Fin rank ≃ Fin (2 * rank) := ltromp_ePlus rank
    let Phi : QuadraticForm K (Fin (2 * rank) → K) :=
      reindexQuadraticForm e (TableBOrth.qPlusForm K rank)
    have hPhi : (QuadraticMap.polarBilin Phi).Nondegenerate :=
      CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.polar_nondegenerate_isometry
        (reindexQuadraticIsometry e (TableBOrth.qPlusForm K rank))
        (TableBOrth.nondegenerate_qPlusForm (K := K) rank)
    let theta : LargeEvenProj (LargeEvenOmega (LargeEvenQPlus K rank)) ≃*
        StatedOmega ⇑Phi :=
      (OrthTorus.rPlusEquiv K (m := rank) (by omega)).trans
        ((TableBOrth.omegaEquivOrthDerived (TableBOrth.qPlusForm K rank)).symm.trans
          (ltromp_reindexEquiv e (TableBOrth.qPlusForm K rank)))
    refine ⟨K, hKf, hKfin, hcard, hQF, ?_⟩
    refine ⟨K, hKf, hKfin, hChar, hcard, Phi, hPhi, theta, ?_⟩
    intro beta hbeta
    obtain ⟨g, rfl⟩ := hbeta
    exact ⟨theta g, fun r => by simp only [MulAut.conj_apply, map_mul, map_inv]⟩
  ·
    have hr4' : 4 ≤ rank := by simpa using hr4
    have hn1 : 1 ≤ n := hlab.1
    intro Q hQ
    have h2 : ¬ rank = 2 := by omega
    have h3 : ¬ rank = 3 := by omega
    dsimp only [CFSG.StandardType.LargeEvenRawDatum] at hQ ⊢
    rw [if_neg h2, if_neg h3] at hQ ⊢
    obtain ⟨K, hKf, hKfin, hcard, b, c, hirr, hQF⟩ := hQ
    letI := hKf
    letI := hKfin
    haveI hChar : CharP K 2 :=
      CFSG.LocalAnalysis.ComponentInitial.finite_field_prime_power_characteristic Nat.prime_two hn1
        hcard
    let e : LargeEvenMinusIdx (rank - 1) ≃ Fin (2 * rank) :=
      (ltromp_eMinus (rank - 1)).trans (finCongr (by omega : 2 * ((rank - 1) + 1) = 2 * rank))
    let Phi : QuadraticForm K (Fin (2 * rank) → K) :=
      reindexQuadraticForm e (TableBOrth.qMinusForm K (rank - 1) b c)
    have hPhi : (QuadraticMap.polarBilin Phi).Nondegenerate :=
      CFSG.ComponentClassification.CatalogueBOrthogonalPointIsometry.polar_nondegenerate_isometry
        (reindexQuadraticIsometry e (TableBOrth.qMinusForm K (rank - 1) b c))
        (TableBOrth.nondegenerate_qMinusForm (K := K) (rank - 1) hirr)
    let theta : LargeEvenProj (LargeEvenOmega (LargeEvenQMinus (rank - 1) b c)) ≃*
        StatedOmega ⇑Phi :=
      (OrthTorus.rMinusEquiv K (rank - 1) b c).trans
        ((TableBOrth.omegaEquivOrthDerived (TableBOrth.qMinusForm K (rank - 1) b c)).symm.trans
          (ltromp_reindexEquiv e (TableBOrth.qMinusForm K (rank - 1) b c)))
    refine ⟨K, hKf, hKfin, hcard, b, c, hirr, hQF, ?_⟩
    refine ⟨K, hKf, hKfin, hChar, hcard, Phi, hPhi, theta, ?_⟩
    intro beta hbeta
    obtain ⟨g, rfl⟩ := hbeta
    exact ⟨theta g, fun r => by simp only [MulAut.conj_apply, map_mul, map_inv]⟩

end S2MathAs3_1619Final

end
