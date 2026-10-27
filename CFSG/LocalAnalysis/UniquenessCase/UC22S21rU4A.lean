module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22ud
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08UsePair
public import CFSG.LocalAnalysis.UniquenessCase.UCFront78Nar
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213a
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213f
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem s21_22U4A_of (D : Data G) (Ch : Choice2011 G) (hc : Nonempty (Ctx22b D Ch))
    (h117 : R117W D) (h869P : F08.R869NPair D) (h8100E : R8100E D) (hV : S22_V D Ch)
    (hn3 : ∀ c : Ctx22b D Ch, 3 ≤ c.n) (h1930 : H1930 D)
    (he : 3 < CFSG.Open.evenRank G) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ} (hn : 2 < n) (hL2 : IsL2 (Bar2 L) n)
    (hpow : IsPowTwo n) : False := by
  obtain ⟨c⟩ := hc
  by_cases hn0 : IsPowTwo c.n
  · exact uc22p2213f_false_of_powTwo D Ch h8100E h1930 he c.toCtx21 (hn3 c) hn0 hL hc2
      hn.le hpow hL2
  · exact uc22p2213a_false_of_not_isPowTwo D Ch h117 h869P hV h1930 c hL hc2 hn hL2 hpow hn0

end CFSG.LocalAnalysis.UniquenessCase.UC22
