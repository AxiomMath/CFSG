module

public import CFSG.GroupTheory.WeirSylow.OrthogonalModels
public import CFSG.Assembly.ComponentTypeDefs
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.RankThree.PartOne.KC.OrthogonalSubfieldForms

public section

namespace CFSG.RankThree.PartOne.SEITZ2

open Matrix CFSG.RankThree.PartOne.KCOrthogonalSubfield
open CFSG.ComponentClassification.CatalogueBOrthogonalSemilinear
open CFSG.ComponentClassification.CatalogueBOrthogonalPointData
  (coordinateQuadMinus minusIndexEquiv reindexQuadraticIsometry)
open CFSG.GroupTheory.WeirSylow (binForm_isometry quadMinusIsometry)

theorem exists_tail_isometry_k {k : Type} [Field k] [Finite k] {n : ℕ} (hn : 1 ≤ n) {b c b' c' : k}
    (hirr : ∀ s : k, s ^ 2 + b * s + c ≠ 0) (hirr' : ∀ s : k, s ^ 2 + b' * s + c' ≠ 0) :
    ∃ A : GL (Fin (2 * n)) k, ∀ v : Fin (2 * n) → k,
      coordinateQuadMinus n k hn b c (A.val *ᵥ v) = coordinateQuadMinus n k hn b' c' v := by
  obtain ⟨L⟩ := binForm_isometry (b := b) (c := c) (b' := b') (c' := c') hirr hirr'
  let Ψ : (CFSG.LieType.Universal.Spin.quadMinus n k b' c').IsometryEquiv
      (CFSG.LieType.Universal.Spin.quadMinus n k b c) :=
    ((quadMinusIsometry n b' c').trans
      (QuadraticMap.IsometryEquiv.prod (QuadraticMap.IsometryEquiv.refl _) L)).trans
      (quadMinusIsometry n b c).symm
  let Θ : (coordinateQuadMinus n k hn b' c').IsometryEquiv (coordinateQuadMinus n k hn b c) :=
    ((reindexQuadraticIsometry (minusIndexEquiv n hn)
      (CFSG.LieType.Universal.Spin.quadMinus n k b' c')).symm.trans Ψ).trans
      (reindexQuadraticIsometry (minusIndexEquiv n hn)
        (CFSG.LieType.Universal.Spin.quadMinus n k b c))
  refine ⟨matrixLinearIso.symm Θ.toLinearEquiv, fun v => ?_⟩
  have h1 : ((matrixLinearIso.symm Θ.toLinearEquiv : GL (Fin (2 * n)) k) : Matrix _ _ k) *ᵥ v =
      Θ v := by
    have h : matrixLinearIso (matrixLinearIso.symm Θ.toLinearEquiv) v = Θ.toLinearEquiv v := by
      rw [MulEquiv.apply_symm_apply]
    exact h
  rw [h1]
  exact Θ.map_app v

theorem exists_tail_isometry {K : Type} [Field K] [Finite K] (k : Subfield K) {n : ℕ}
    (hn : 1 ≤ n) {b c b' c' : K} (hb : b ∈ k) (hc : c ∈ k) (hb' : b' ∈ k) (hc' : c' ∈ k)
    (hirr : ∀ s ∈ k, s ^ 2 + b * s + c ≠ 0) (hirr' : ∀ s ∈ k, s ^ 2 + b' * s + c' ≠ 0) :
    ∃ μ : GL (Fin (2 * n)) K, (∀ i j, μ.val i j ∈ k) ∧
      ∀ v : Fin (2 * n) → K, coordinateQuadMinus n K hn b c (μ.val *ᵥ v) =
        coordinateQuadMinus n K hn b' c' v := by
  obtain ⟨A, hA⟩ := exists_tail_isometry_k (k := k) (b := (⟨b, hb⟩ : k)) (c := ⟨c, hc⟩)
    (b' := ⟨b', hb'⟩) (c' := ⟨c', hc'⟩) hn
    (fun s hz => hirr s.1 s.2 (by simpa using congrArg Subtype.val hz))
    (fun s hz => hirr' s.1 s.2 (by simpa using congrArg Subtype.val hz))
  refine ⟨glIncl k A, fun i j => ?_, fun v => ?_⟩
  · rw [glIncl_val, Matrix.map_apply]
    exact (A.val i j).2
  · have h := eq_of_agree k
      ((coordinateQuadMinus n K hn b c).comp (matrixLinearEquiv (glIncl k A)).toLinearMap)
      (coordinateQuadMinus n K hn b' c') (fun w => by
        rw [QuadraticMap.comp_apply]
        change coordinateQuadMinus n K hn b c (matrixLinearEquiv (glIncl k A)
          (vecIncl k w)) = _
        rw [matrixLinearEquiv_apply, mulVec_vecIncl,
          coordinateQuadMinus_isExtension k n hn ⟨b, hb⟩ ⟨c, hc⟩,
          coordinateQuadMinus_isExtension k n hn ⟨b', hb'⟩ ⟨c', hc'⟩, hA])
    have := congrArg (fun F => F v) h
    simpa [QuadraticMap.comp_apply, matrixLinearEquiv_apply] using this

end CFSG.RankThree.PartOne.SEITZ2
