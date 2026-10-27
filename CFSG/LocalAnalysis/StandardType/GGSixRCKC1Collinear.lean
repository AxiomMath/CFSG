module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1CollinearSpinSix
public import CFSG.LieType.Universal.RankZero
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1CollinearSU
import CFSG.LocalAnalysis.StandardType.GGSixRCKC1CollinearSp

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.StandardType CFSG.StandardType.S2MathFi1035Pos

theorem rckK2NbrCollinear_of_rest
    (h : RCKCollinearRest) : RCKK2NbrCollinear := by
  refine rckK2NbrCollinear_of_via ?_ h
  intro t' m g β ht hg hβ hcase
  rcases ht with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
  ·
    rcases hcase with hl | ⟨hs, -⟩
    · exact rckCollinearVia_PSL hg hβ hl
    · exact absurd hs (by simp [GGShortTag, GGTwistedTag])
  ·
    by_cases hl : GGLongRoot (ggU .PSU m g).D β
    · rcases Nat.lt_or_ge g 2 with hg2 | hg2
      · obtain rfl : g = 1 := by omega
        exact rckCollinearVia_PSU_long_two hβ hl
      · exact rckCollinearVia_PSU_long_of_two_le hg2 hβ hl
    · exact rckCollinearVia_PSU_short hg hβ hl
  ·
    by_cases hl : GGLongRoot (ggU .PSp m g).D β
    · exact rckCollinearVia_PSp_long hg hβ hl
    · exact rckCollinearVia_PSp_short hg hβ hl
  ·
    have hl : GGLongRoot (ggU .POmegaPlus m g).D β := by
      rcases hcase with hl | ⟨hs, -⟩
      · exact hl
      · exact absurd hs (by simp [GGShortTag, GGTwistedTag])
    by_cases h4 : 4 ≤ m
    · exact rckCollinearVia_POmegaPlus hg h4 hβ hl
    · by_cases h3 : 3 ≤ m
      · have hm3 : m = 3 := by omega
        subst hm3
        exact rckCollinearVia_POmegaPlus_three hg hβ hl
      · exfalso
        have e : ggU .POmegaPlus m g = trivialUniversal := by
          simp only [ggU, lieUniversal, dif_neg h3]
        have hrank : (ggU .POmegaPlus m g).D.rank = 0 :=
          (congrArg (fun L : LieUniversal => L.D.rank) e).trans rfl
        exact UniversalRootDatum.not_mem_roots_of_rank_eq_zero _ hrank hβ
  ·
    by_cases hm2 : m = 2
    · subst hm2
      exact rckCollinearVia_POmegaMinus_two hg hβ
    · by_cases hl : GGLongRoot (ggU .POmegaMinus m g).D β
      · by_cases h4 : 4 ≤ m
        · exact rckCollinearVia_POmegaMinus_long hg h4 hβ hl
        · by_cases h3 : 3 ≤ m
          · have hm3 : m = 3 := by omega
            subst hm3
            exact rckCollinearVia_POmegaMinus_three hg hβ hl
          · exfalso
            have hrank : (ggU .POmegaMinus m g).D.rank = 0 := by
              simp [ggU, lieUniversal, CFSG.LieType.Universal.Spin.Twisted.minusDatum]
              omega
            exact UniversalRootDatum.not_mem_roots_of_rank_eq_zero _ hrank hβ
      · by_cases h2 : 2 ≤ m
        · exact rckCollinearVia_POmegaMinus_short hg h2 hβ hl
        · exfalso
          have hrank : (ggU .POmegaMinus m g).D.rank = 0 := by
            simp [ggU, lieUniversal, CFSG.LieType.Universal.Spin.Twisted.minusDatum]
            omega
          exact UniversalRootDatum.not_mem_roots_of_rank_eq_zero _ hrank hβ
  ·
    by_cases hl : GGLongRoot (ggU .F4 m g).D β
    · exact rckCollinearVia_F4_long hg hβ hl
    · exact rckCollinearVia_F4_short hg hβ hl
  ·
    have hl : GGLongRoot (ggU .E6 m g).D β := by
      rcases hcase with hl | ⟨hs, -⟩
      · exact hl
      · exact absurd hs (by simp [GGShortTag, GGTwistedTag])
    exact rckCollinearVia_E6 hg hβ hl
  ·
    have hl : GGLongRoot (ggU .E7 m g).D β := by
      rcases hcase with hl | ⟨hs, -⟩
      · exact hl
      · exact absurd hs (by simp [GGShortTag, GGTwistedTag])
    exact rckCollinearVia_E7 hg hβ hl
  ·
    have hl : GGLongRoot (ggU .E8 m g).D β := by
      rcases hcase with hl | ⟨hs, -⟩
      · exact hl
      · exact absurd hs (by simp [GGShortTag, GGTwistedTag])
    exact rckCollinearVia_E8 hg hβ hl
  ·
    by_cases hl : GGLongRoot (ggU .twistedE6 m g).D β
    · exact rckCollinearVia_twistedE6_long hg hβ hl
    · exact rckCollinearVia_twistedE6_short hg hβ hl

end CFSG.StandardType.RCKC1
