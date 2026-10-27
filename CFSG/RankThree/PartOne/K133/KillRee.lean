module

public import CFSG.RankThree.PartOne.K133.KillBasic
public import CFSG.RankThree.PartOne.CTP.SeitzExc
public import CFSG.RankThree.PartOne.K133.Quot

public section

namespace CFSG.RankThree.PartOne.K133

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.Blueprint
open CFSG.RankThree.PartOne.Census3 (IsoLie)


theorem noRankThree_smallRee {X : Type} [Group X] (hiso : IsoLie X (.reeG2 1)) {p : ℕ}
    (hp : p.Prime) (h5 : 5 ≤ p) : NoRankThree p X := by
  rintro ⟨Ē, hEl, hcard⟩
  obtain ⟨k, hk⟩ := CTP.card_mulAut_dvd_smallRee (ℓ := 3) rfl (CTP.reeTitsModel_reeG2 1 hiso)
  have h1 : p ^ 3 ∣ Nat.card (MulAut X) := hcard ▸ Subgroup.card_subgroup_dvd_card Ē
  exact CTP.not_sq_dvd_smallRee_aut hp h5
    ((pow_dvd_pow p (by norm_num : 2 ≤ 3)).trans (h1.trans hk))

theorem kf133ResMaxItem_two : KF133ResMaxItem 2 :=
  KF133ResMaxAt.of_noRankThree fun _ _ _ hX _ hp h5 => noRankThree_smallRee hX hp h5

end CFSG.RankThree.PartOne.K133
