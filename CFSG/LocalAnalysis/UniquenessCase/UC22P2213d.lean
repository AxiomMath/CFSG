module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S22a
public import CFSG.LocalAnalysis.UniquenessCase.UC22DataExt
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2213Defs
public import CFSG.LocalAnalysis.UniquenessCase.UC22P2214a
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229N
import CFSG.LocalAnalysis.UniquenessCase.UC22P2213b
import CFSG.LocalAnalysis.UniquenessCase.UC22P22a
public import CFSG.LocalAnalysis.UniquenessCase.UC22Bridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup

variable {G : Type} [Group G] [Finite G]

theorem s21_21Used_of_s21_21E {D : Data G} {Ch : Choice2011 G}
    (he : 3 < CFSG.Open.evenRank G) (h : S21_21E D Ch) : S21_21Used D Ch :=
  fun h1930 c hH => absurd (h h1930 c hH) (by omega)

theorem uc22p2213d_false_of_hyp2120 (D : Data G) (Ch : Choice2011 G) (h21E : S21_21E D Ch)
    (h1930 : H1930 D) (he : 3 < CFSG.Open.evenRank G) (c : Ctx21 D Ch) (hH : Hyp2120 D c) :
    False := by
  have := h21E h1930 c hH
  omega

theorem uc22p2213d_false_of_su3 (D : Data G) (Ch : Choice2011 G) (h9 : S21_9N D Ch)
    (h1930 : H1930 D) (he : 3 < CFSG.Open.evenRank G) (c : Ctx21 D Ch) {L : Subgroup G}
    (hL : L ∈ calC D.M) (hN : (L.subgroupOf D.M).Normal) {n : ℕ} (hn : Odd n)
    (hsu : IsSU3 (Bar2 L) n) : False := by
  have h2 := uc22p22a_two_le_of_isU3 hsu.2
  have hpow : ¬ IsPowTwo n := uc22p22a_not_isPowTwo_of_odd hn (by omega)
  have := h9 h1930 c L hL hN n hsu hpow
  omega

theorem uc22p2213d_false_of_sp4 (D : Data G) (Ch : Choice2011 G) (hx : DataExt D)
    (h8E : S21_8E D Ch) (h1930 : H1930 D) (he : 3 < CFSG.Open.evenRank G) (c : Ctx21 D Ch)
    {L : Subgroup G} (hL : L ∈ calC D.M) {n : ℕ} (hn : Odd n) (hsp : IsSp4 (Bar2 L) n) :
    False := by
  obtain ⟨p, hp⟩ := hx.sig_nonempty
  have h3 := h8E h1930 c L hL n hn hsp p hp
  have h4 := hx.four_le he p hp
  omega

theorem uc22p2213d_exists_not_normal (D : Data G) (Ch : Choice2011 G) (hx : DataExt D)
    (h12 : S22_12 D Ch) (h21E : S21_21E D Ch) (h9 : S21_9N D Ch) (h8E : S21_8E D Ch)
    (h1930 : H1930 D) (he : 3 < CFSG.Open.evenRank G) (c : Ctx22b D Ch) :
    ∃ L ∈ calC D.M, ¬ (L.subgroupOf D.M).Normal := by
  by_contra hcon
  push Not at hcon
  refine uc22p2213d_false_of_hyp2120 D Ch h21E h1930 he _
    ((uc22p2213b_hyp2120_B0_iff D Ch h12 h1930 hx.sig_nonempty c).2 fun L hL => ?_)
  refine ⟨hcon L hL, ?_⟩
  rintro ⟨n, hn, hsp | hsu⟩
  · exact uc22p2213d_false_of_sp4 D Ch hx h8E h1930 he c.toCtx21 hL hn hsp
  · exact uc22p2213d_false_of_su3 D Ch h9 h1930 he c.toCtx21 hL (hcon L hL) hn hsu

end CFSG.LocalAnalysis.UniquenessCase.UC22
