module

public import CFSG.LocalAnalysis.WeakClosure81.W18Defs
public import CFSG.LocalAnalysis.WeakClosure81.W18Weak
public import CFSG.LocalAnalysis.WeakClosure81.W172Stmt

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {G : Type} [Group G] [Finite G]

namespace MinCex183

variable {D : Data G} {V₀ V H : Subgroup G} {i : ℕ}

theorem mBarGT_two (c : MinCex183 D V₀ V H i) : MBarGT D.M V₀ V 2 := by
  rcases not_and_or.mp c.fail with h1 | h2
  · exact (not_concl181_iff.mp h1).2.1
  · exact MBarGT.mono (not_concl182_iff.mp h2).2.1 (by omega)

theorem not_isSolvable (c : MinCex183 D V₀ V H i) (h172 : W3Thm172Weak G) : ¬ IsSolvable ↥H := by
  intro hsolv
  have hm : MBarGT D.M V₀ V 2 := c.mBarGT_two
  have hN : normalizer (E3.wClos V 1 D.T : Set G) ≤ D.M := by
    rcases Nat.le_one_iff_eq_zero_or_eq_one.mp c.hyp.i_le with hi | hi
    · have h4 : 4 ≤ Nat.card V := by
        have := MBarGT.two_pow_le_card hm
        norm_num at this
        omega
      have hi0 := c.hyp.normW
      rw [hi] at hi0
      exact (normalizer_wClos_one_le c.hyp.setting.isElemAbelian h4).trans hi0
    · have hi1 := c.hyp.normW
      rw [hi] at hi1
      exact hi1
  exact c.hyp.notLe (h172 D V₀ V c.hyp.setting c.hyp.ne_bot H c.hyp.hyp171 hsolv hm hN)

end MinCex183

end CFSG.LocalAnalysis.WeakClosure81

end
