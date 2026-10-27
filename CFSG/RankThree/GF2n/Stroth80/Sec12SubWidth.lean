module

public import CFSG.RankThree.GF2n.Stroth80.Sec7TailBasic
public import CFSG.Adapters.ProjectiveSpecialLinear

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open CFSG.Assembly.LowTwoRank
open scoped commutatorElement Matrix

variable {G : Type} [Group G] [Finite G] {M Q Z B : Subgroup G}

theorem not_omegaPlusNat_two_of {hc : Ctx M Q Z B} {t : G} {m : ℕ} (hm : 3 ≤ m)
    (h : OmegaPlusNat hc t m ∨ OmegaMinusNat hc t m) : ¬ OmegaPlusNat hc t 2 := by
  intro h2
  rcases h with h | h
  · exact absurd (h2.eq_of_plus h) (by omega)
  · exact absurd (omegaPlusNat_eq_omegaMinusNat (by omega) h2 h) (by omega)

end CFSG.RankThree.GF2n.Stroth80
