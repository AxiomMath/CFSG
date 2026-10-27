module

import CFSG.LocalAnalysis.UniquenessCase.UC22P22i
import CFSG.Mathlib.Arithmetic.TwoPowSubOnePrimes
public import CFSG.CGT.PushingUpLit.Transport
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

namespace Ctx21

theorem exists_mem_B0_orderOf_ne_three {D : Data G} {Ch : Choice2011 G} (c : Ctx21 D Ch)
    (hn3 : 3 ≤ c.n) :
    ∃ b ∈ c.B0, ∃ r : ℕ, r.Prime ∧ r ≠ 2 ∧ r ≠ 3 ∧ orderOf b = r := by
  obtain ⟨r, hr, hr2, hr3, hrd⟩ :=
    CFSG.exists_prime_ne_two_ne_three_dvd_two_pow_sub_one hn3
  have hmem : r ∈ piSet c.B0 := by
    rw [c.hpi]
    exact ⟨hr, hrd⟩
  obtain ⟨b, hb, hbo⟩ := uc22p22i_exists_elt_of_mem_piSet hmem
  exact ⟨b, hb, r, hr, hr2, hr3, hbo⟩

end Ctx21

end CFSG.LocalAnalysis.UniquenessCase.UC22
