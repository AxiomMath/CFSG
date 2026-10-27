module

public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFShapeA
public import CFSG.LocalAnalysis.WeakClosure81.GF2Reps135C2OmQMinusNFShapeC

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.LieType.Universal.Spin CFSG.LieType.Universal.Spin.Twisted CFSG.LieType.RootSystem
open CFSG.StandardType
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.Thm14_5

theorem omqnf_exists_conj_nW {n : ℕ} (hn : 4 ≤ n) {K : Type} [Field K] [Finite K] [CharP K 2]
    {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) {y : spinGroup (quadMinus n K b c)}
    (hy : y * y = 1) (hy1 : y ≠ 1) :
    ∃ (g : spinGroup (quadMinus n K b c))
      (x : (coxeterMatrix (isFiniteType_cartanB (n - 1))).Group)
      (π : Equiv.Perm (Fin (n - 1))) (s : Fin (n - 1) → ℤ),
      SpIsSign s ∧ omqnfRealizes (n - 1) x π s ∧
      (SmallO8mCurtis.curtisDatum n hn hirr).nW x = g * y * g⁻¹ ∧
      (((∀ a, s a = 1) ∧ π * π = 1 ∧ π ⟨0, by omega⟩ = ⟨1, by omega⟩ ∧
          π ⟨1, by omega⟩ = ⟨0, by omega⟩) ∨
        (π = 1 ∧ s ⟨0, by omega⟩ = -1 ∧
          Odd (Finset.univ.filter fun a => s a = -1).card)) := by
  rcases omqnf_involution_type hn hirr hy hy1 with ⟨r, hr1, hr2, hl, hk⟩ | ⟨j, hj, hj2, hl, hk⟩
  · obtain ⟨g, x, π, s, hs, hx, hg, hsh⟩ := omqnf_exists_conj_shapeA hn hirr hy hy1 hr1 hr2 hl hk
    exact ⟨g, x, π, s, hs, hx, hg, Or.inl hsh⟩
  · obtain ⟨g, x, π, s, hs, hx, hg, hsh⟩ := omqnf_exists_conj_shapeC hn hirr hy hy1 hj hj2 hl hk
    exact ⟨g, x, π, s, hs, hx, hg, Or.inr hsh⟩

end CFSG.LocalAnalysis.WeakClosure81
