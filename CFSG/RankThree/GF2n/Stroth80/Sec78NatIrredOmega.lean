module

public import CFSG.RankThree.GF2n.Stroth80.Sec310Stmt
public import CFSG.ClassicalGroups.Orthogonal.ElementaryGroupIrreducible
public import CFSG.ClassicalGroups.Orthogonal.StatedOmegaTransport

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG.Open CFSG.ClassicalGroups.Orthogonal CFSG.LieType.Universal.Spin
open QuadraticMap
open scoped Matrix

private theorem natIrred_of_elemMatrixIso {K : Type} [Field K] {ι : Type} [Fintype ι]
    [DecidableEq ι] {Q : QuadraticForm K (ι → K)} {X : Subgroup (GL ι K)}
    (E : ElemMatrixIso Q X) (hQ : (polarBilin Q).Nondegenerate)
    (hP : ∃ P : Fin 2 → HypPair Q, ∀ i j, i ≠ j → (P i).Orth (P j)) : NatIrred X := by
  intro S hS
  refine submodule_eq_bot_or_top_of_elementaryGroup_invariant hQ hP S ?_
  intro g hg x hx
  have h1 := E.app (E.equiv.symm ⟨g, hg⟩) x
  rw [MulEquiv.apply_symm_apply] at h1
  have h3 := hS _ (E.equiv.symm ⟨g, hg⟩).2 x hx
  rw [← h1] at h3
  exact h3

theorem natIrred_statedOmegaPlus {K : Type} [Field K] {m : ℕ} (hm : 3 ≤ m) :
    NatIrred (StatedOmega (StatedQuadPlus m K)) := by
  refine natIrred_of_elemMatrixIso (ElemMatrixIso.plus hm)
    (nondegenerate_polarBilin_quadPlus m K)
    ⟨fun i => plusPair K (Fin.castLE (by omega : 2 ≤ m) i), ?_⟩
  intro i j hij
  exact plusPair_orth (fun h => hij (Fin.castLE_injective _ h))

theorem natIrred_statedOmegaMinus_of_three_le {K : Type} [Field K] [Finite K] [CharP K 2] {m : ℕ}
    {b c : K} (hm : 3 ≤ m) (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    NatIrred (StatedOmega (StatedQuadMinus m K b c)) := by
  refine natIrred_of_elemMatrixIso (ElemMatrixIso.minus (by omega : 2 ≤ m) hirr)
    (nondegenerate_polarBilin_quadMinus_of_finite m K hirr)
    ⟨fun i => minusPair K b c (Fin.castLE (by omega : 2 ≤ m - 1) i), ?_⟩
  intro i j hij
  exact minusPair_orth (fun h => hij (Fin.castLE_injective _ h))

end CFSG.RankThree.GF2n.Stroth80
