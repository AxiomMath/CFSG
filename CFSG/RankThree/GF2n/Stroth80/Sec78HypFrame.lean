module

public import CFSG.RankThree.GF2n.Stroth80.Sec78ConjFrame
public import CFSG.RankThree.GF2n.Stroth80.Sec7Transport

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Open.StatedAPI CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem sec7ctr_hyp_frame (hc : Ctx M Q Z B) {n : ℕ} {t s : G} (hs : Sec7Hyp hc n t) {h : G}
    (hh : h ∈ M) (hsL : s ∈ LB M Q (conjSubgroup h B)) (hsQ : s ∉ Q)
    (hR : Rt M (LB M Q B) s = Rt M (LB M Q B) t)
    (hV : Vt M (LB M Q B) B Z s = Vt M (LB M Q B) B Z t) :
    Sec7Hyp (hc.conj_of_mem hh) n s where
  toSec5 :=
    ⟨hs.toSec5.width, hs.toSec5.n_gt, by
      rw [hc.LB_conj hh]
      exact sec7ctr_NoA2_conj hc hh hs.toSec5.noA2,
      hs.toSec5.gen.conj_of_mem hh, hsL, hsQ⟩
  notPlus4 := fun hP => hs.notPlus4
    ((OmegaPlusNat_congr hc hR hV 2).mp ((sec7ctr_OmegaPlusNat_conj_frame hc hh s 2).mp hP))
  orth := by
    obtain ⟨m, hm, h1 | h1⟩ := hs.orth
    · exact ⟨m, hm, Or.inl ((sec7ctr_OmegaPlusNat_conj_frame hc hh s m).mpr
        ((OmegaPlusNat_congr hc hR hV m).mpr h1))⟩
    · exact ⟨m, hm, Or.inr ((sec7ctr_OmegaMinusNat_conj_frame hc hh s m).mpr
        ((OmegaMinusNat_congr hc hR hV m).mpr h1))⟩
  large := by
    rw [sec7ctr_CN_conj_frame hc hh s, hc.CN_congr hR hV]
    exact hs.large

end CFSG.RankThree.GF2n.Stroth80
