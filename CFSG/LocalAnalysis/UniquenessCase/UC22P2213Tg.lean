module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213Tf
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2121TB
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213b
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213Tb
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213Tc

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22.Ext

variable {G : Type} [Group G] [Finite G]

theorem uc22p2213t_s22_13Sig3N (D : Data G) (Ch : Choice2011 G)
    (he : CFSG.Open.evenRank G = 3) (hK147 : K147) (h117 : R117W D) (h869N : F08.R869N D)
    (hV : S22_V D Ch) (h17 : S21_17 D Ch) (h15 : S21_15C D Ch) (h17J : S21_17J D Ch)
    (h8100 : R8100T D) (h8 : S21_8Sp4 D Ch) (h8P : S21_8P D Ch) (h846 : F08.R846 D)
    (h228 : S22_8 D Ch) (hSg : UC6S846.SigmaStd D) (h229 : S22_9 D Ch) (h9 : S21_9Sig3 D Ch)
    (h21 : S21_21TB D Ch) (hn3 : H1930 D → ∀ c : Ctx22b D Ch, 3 ≤ c.n) :
    S22_12 D Ch → S22_13 D Ch := by
  intro h12 h1930 c p hp
  by_cases hH : Hyp2120 D { c.toCtx21 with B := c.B0, hB := c.hB0, hle := le_rfl }
  · exact uc22p2213t_of_hyp2120TB D Ch h21 hV h1930 c (by have := hn3 h1930 c; omega) hH hp
  rw [uc22p2213b_hyp2120_B0_iff D Ch h12 h1930 ⟨p, hp⟩ c] at hH
  obtain ⟨L, hL, hLn⟩ := not_forall₂.1 hH
  by_cases hN : (L.subgroupOf D.M).Normal
  · obtain ⟨n, hodd, hsp | hsu⟩ : ∃ n : ℕ, Odd n ∧ (IsSp4 (Bar2 L) n ∨ IsSU3 (Bar2 L) n) :=
      not_not.1 fun h => hLn ⟨hN, h⟩
    · exact ⟨L, n, uc22p2213t_sp4 D Ch h117 hV h8 h8P he h1930 c hp hL hodd hsp⟩
    · exact (uc22p2213t_false_of_su3N D Ch hK147 h117 h869N hV h846 h228 hSg h229 h9 he h1930 c
        (hn3 h1930 c) hL hN hodd hsu).elim
  · obtain ⟨n, hK⟩ := uc22p2213t_of_not_normal D Ch h17 h15 h17J h8100 h117
      (F08.R869NPair_of_R869N D h869N) hV he h1930 c (by have := hn3 h1930 c; omega) hp hL hN
    exact ⟨L, n, hK⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
