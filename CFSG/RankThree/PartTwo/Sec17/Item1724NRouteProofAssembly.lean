module

import CFSG.RankThree.PartTwo.Sec4.Sporadic.Item415
public import CFSG.RankThree.PartTwo.Sec17.Item1724NRouteProofCore

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late

theorem configScalar_of_stepsN
    (h169 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Item169 A (lB A) L)
    (h163 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Item163 A (lB A) c L)
    (h164 : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Item164 A (lB A) c)
    (hM : ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L : Subgroup G),
      Sec15R G A c L → Claim17M A (lB A))
    (hY1 : Para1714) (hW : Para1722) (hWQ : Para1724) (hS : Para1725) (hR : Para1726)
    (h1721 : Item1721) (h1724 : Item1724Three) (h1725 : Item1725) (h1726 : Item1726)
    (h1727 : Item1727) : ConfigScalar := by
  intro G _ _ A c L hR15
  obtain ⟨Y₀, h0⟩ := exists_sec17Std hR15 (h169 G A c L hR15) (h163 G A c L hR15)
    (h164 G A c L hR15) (hM G A c L hR15)
  obtain ⟨Y₁, S, p, P, h1⟩ := hY1 G A c L Y₀ h0
  obtain ⟨w, Q, h2⟩ := hW G A c L Y₀ Y₁ S p P h1
  obtain ⟨-, w', h3⟩ := hWQ G A c L Y₀ Y₁ S p P w Q h2
  obtain ⟨Y₁', S', P', s, h4⟩ := hS G A c L Y₀ Y₁ S p P w' Q h3
  obtain ⟨d, r, h5⟩ := hR G A c L Y₀ Y₁' S' p P' w' Q s h4
  have : Fact p.Prime := ⟨h5.p_prime⟩
  obtain ⟨m, hm⟩ := exists_conj_eq_pow_of_data Sec4.Sporadic.rank3II_4_15 h1721 h1725
    (rank3II_17_28Z_ofN h1724 h1726 h1727) h5
  have hZQ : omegaOneZ p Q ≤ Q := omegaOneZ_le p Q
  have hZ1 : omegaOneZ p Q ≠ ⊥ := omegaOneZ_ne_bot h5.isPGroup_Q h5.Q_ne_bot
  have hQc := Proof1724N.inf_centralizer_c_eq_bot h5.toSec17W
    (h1724 G A c L Y₀ Y₁' S' p P' w' Q h5.toSec17W)
  have hfix : omegaOneZ p Q ⊓ Subgroup.centralizer ({c} : Set G) = ⊥ :=
    le_bot_iff.mp ((inf_le_inf_right _ hZQ).trans hQc.le)
  refine ⟨p, inferInstance, omegaOneZ p Q, s, m, isElemAbelian_omegaOneZ p Q, hZ1,
    normalizer_le_normalizer_omegaOneZ p Q h5.s_normalizes_Q, h5.s_inverts_c,
    sq_ne_one_of_conj_eq_pow (isElemAbelian_omegaOneZ p Q) hZ1 h5.c_pow_three hfix hm, hm⟩

end CFSG.RankThree.PartTwo.Sec17
