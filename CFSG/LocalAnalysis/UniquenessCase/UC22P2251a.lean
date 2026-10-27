module

public import CFSG.LocalAnalysis.UniquenessCase.UC22P22n
public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
import CFSG.LocalAnalysis.UniquenessCase.UC22P22qr
import CFSG.LocalAnalysis.UniquenessCase.UC22P22e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.CGT.Timmesfeld75 (IsTI)

variable {G : Type} [Group G] [Finite G]

theorem uc22p2251a_pRank_sub_one_le (D : Data G) (h61 : UC6.R6_1 D) {V : Subgroup G}
    (hV : InCalV D.M V) (hTI : ¬ IsTI V) {p : ℕ} (hp : p ∈ D.sig) :
    CFSG.Open.pRank p D.M - 1 ≤ CFSG.pRank p (MBar D.M V) := by
  haveI := cTilde_bot_normal D.M V hV.2.2.1
  rw [pRank_mbar D.M V p]
  refine uc22p22q_pRank_sub_one_le (D.sig_prime p hp).1 ?_
  rw [cTilde_bot]
  exact uc22p22n_pRank_centralizer_le_one D h61 hV hTI p hp

theorem uc22p2251a_two_lt_pRank_mbar (D : Data G) (hx : DataExt D) (h61 : UC6.R6_1 D)
    (he : 3 < CFSG.Open.evenRank G) {V : Subgroup G} (hV : InCalV D.M V) (hTI : ¬ IsTI V) :
    ∀ p ∈ D.sig, 2 < CFSG.pRank p (MBar D.M V) := by
  intro p hp
  have h4 := hx.four_le he p hp
  have h := uc22p2251a_pRank_sub_one_le D h61 hV hTI hp
  omega

theorem uc22p2251a_two_lt_pRank_mbarU (D : Data G) {Ch : Choice2011 G} (hx : DataExt D)
    (h61 : UC6.R6_1 D) (he : 3 < CFSG.Open.evenRank G) (c : Ctx22 D Ch) :
    ∀ p ∈ D.sig, 2 < CFSG.pRank p (MBar D.M D.U) :=
  uc22p2251a_two_lt_pRank_mbar D hx h61 he (uc22p22e_inCalV_U D) c.hU

end CFSG.LocalAnalysis.UniquenessCase.UC22
