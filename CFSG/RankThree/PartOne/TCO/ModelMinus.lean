module

public import CFSG.Assembly.GL83LieDefs
public import CFSG.RankThree.PartOne.S11d.LieCentralizerPOmega
public import CFSG.RankThree.PartOne.S11d.OrthLayer

public section

namespace CFSG.RankThree.PartOne.TCO

open Module QuadraticMap CFSG.RankThree.Classical2 CFSG.ClassicalGroups.Orthogonal
  CFSG.LieType.Universal.Spin
open CFSG.Assembly.LowTwoRank (StatedProj StatedOmega StatedQuadMinus)

theorem nonempty_statedProj_mulEquiv_orthDerived {K : Type} [Field K] [Finite K] [CharP K 2]
    {n : ℕ} (hn : 4 ≤ n) {b c : K} (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    Nonempty (StatedProj (StatedOmega (StatedQuadMinus n K b c)) ≃*
      orthDerived (quadMinus n K b c)) := by
  obtain ⟨hnd, -⟩ := CFSG.ClassicalGroups.Orthogonal.regular_quadMinus (n := n) hn hirr
  have : Inhabited (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2) := ⟨Sum.inr (Sum.inr 0)⟩
  have : Nontrivial (Fin (n - 1) ⊕ Fin (n - 1) ⊕ Fin 2 → K) := Pi.nontrivial
  exact ⟨(statedProjOrthEquiv (coe_quadMinus n K b c)).trans
    (MulEquiv.ofBijective (piOrth (quadMinus n K b c))
      ⟨piOrth_injective hnd, piOrth_surjective⟩).symm⟩

end CFSG.RankThree.PartOne.TCO
