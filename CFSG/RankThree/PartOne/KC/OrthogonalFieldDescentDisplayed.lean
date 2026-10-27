module

public import CFSG.RankThree.PartOne.KC.OrthogonalFieldDescentSplit
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointDataSemilinear

public section

namespace CFSG.RankThree.PartOne.KCOrthogonalDescent

open Module QuadraticMap CFSG.Blueprint.EvenSource
  CFSG.ComponentClassification.CatalogueBOrthogonalPointData

variable {F : Type} [Field F]

theorem sum_reindex_basisFun {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀] {m δ : ℕ}
    (ε : ι₀ ≃ Fin m ⊕ Fin m ⊕ Fin δ) (x y : Fin m → F) (z : Fin δ → F) :
    ∑ i, x i • ((Pi.basisFun F ι₀).reindex ε) (.inl i) +
        ∑ i, y i • ((Pi.basisFun F ι₀).reindex ε) (.inr (.inl i)) +
        ∑ j, z j • ((Pi.basisFun F ι₀).reindex ε) (.inr (.inr j)) =
      fun j => Sum.elim x (Sum.elim y z) (ε j) := by
  funext j
  simp only [Basis.reindex_apply, Pi.basisFun_apply, Pi.add_apply, Finset.sum_apply,
    Pi.smul_apply, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero,
    Equiv.eq_symm_apply]
  rcases h : ε j with i | i | l <;> simp

@[expose] noncomputable def HypSplit.ofReindex {ι₀ : Type} [Fintype ι₀] [DecidableEq ι₀] {m δ : ℕ}
    (Q : QuadraticForm F (ι₀ → F)) (ε : ι₀ ≃ Fin m ⊕ Fin m ⊕ Fin δ) (T : (Fin δ → F) → F)
    (hQ : ∀ v : ι₀ → F, Q v = ∑ i, v (ε.symm (.inl i)) * v (ε.symm (.inr (.inl i))) +
      T (fun j => v (ε.symm (.inr (.inr j)))))
    (hT : ∀ z, T z = 0 → z = 0) : HypSplit Q m δ where
  b := (Pi.basisFun F ι₀).reindex ε
  eval x y z := by
    have h0 : ∑ j, z j • ((Pi.basisFun F ι₀).reindex ε) (.inr (.inr j)) =
        fun j => Sum.elim (0 : Fin m → F) (Sum.elim (0 : Fin m → F) z) (ε j) := by
      have := sum_reindex_basisFun ε (0 : Fin m → F) (0 : Fin m → F) z
      simpa using this
    rw [sum_reindex_basisFun, h0, hQ, hQ]
    simp
  aniso z hz := by
    have h0 : ∑ j, z j • ((Pi.basisFun F ι₀).reindex ε) (.inr (.inr j)) =
        fun j => Sum.elim (0 : Fin m → F) (Sum.elim (0 : Fin m → F) z) (ε j) := by
      have := sum_reindex_basisFun ε (0 : Fin m → F) (0 : Fin m → F) z
      simpa using this
    rw [h0, hQ] at hz
    simp only [Equiv.apply_symm_apply, Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, mul_zero,
      Finset.sum_const_zero, zero_add] at hz
    exact hT z hz

section Coordinate

variable (n : ℕ) (K : Type) [Field K]

@[expose] noncomputable def hypSplitCoordinatePlus : HypSplit (coordinateQuadPlus n K) n 0 :=
  HypSplit.ofReindex (coordinateQuadPlus n K)
    ((plusIndexEquiv n).symm.trans
      (Equiv.sumCongr (Equiv.refl (Fin n)) (Equiv.sumEmpty (Fin n) (Fin 0)).symm))
    (fun _ => 0)
    (fun v => by
      rw [coordinateQuadPlus_apply]
      simp)
    (fun z _ => Subsingleton.elim _ _)

@[expose] noncomputable def hypSplitCoordinateMinus (hn : 1 ≤ n) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) : HypSplit (coordinateQuadMinus n K hn b c) (n - 1) 2 :=
  HypSplit.ofReindex (coordinateQuadMinus n K hn b c) (minusIndexEquiv n hn).symm
    (fun z => z 0 ^ 2 + b * z 0 * z 1 + c * z 1 ^ 2)
    (fun v => by
      rw [coordinateQuadMinus_apply]
      simp only [Equiv.symm_symm]
      ring)
    (fun z hz => by
      have h1 : z 1 = 0 := by
        by_contra h1
        apply hirr (z 0 / z 1)
        field_simp
        linear_combination hz
      have h0 : z 0 = 0 := by
        rw [h1] at hz
        simpa using hz
      funext i
      fin_cases i
      · exact h0
      · exact h1)

theorem le_sourceWittIndex_coordinateQuadPlus : n ≤ sourceWittIndex ⇑(coordinateQuadPlus n K) :=
  (hypSplitCoordinatePlus n K).le_sourceWittIndex

theorem sourceWittIndex_coordinateQuadPlus
    (hnd : (polarBilin (coordinateQuadPlus n K)).Nondegenerate) :
    sourceWittIndex ⇑(coordinateQuadPlus n K) = n :=
  (hypSplitCoordinatePlus n K).sourceWittIndex_eq hnd

theorem sourceWittIndex_coordinateQuadMinus (hn : 1 ≤ n) (b c : K)
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (hnd : (polarBilin (coordinateQuadMinus n K hn b c)).Nondegenerate) :
    sourceWittIndex ⇑(coordinateQuadMinus n K hn b c) = n - 1 :=
  (hypSplitCoordinateMinus n K hn b c hirr).sourceWittIndex_eq hnd

end Coordinate

end CFSG.RankThree.PartOne.KCOrthogonalDescent
