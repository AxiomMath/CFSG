module

public import CFSG.RankThree.PartOne.N143.O7Torus
public import CFSG.RankThree.PartOne.N143.TorusLift

public section

namespace CFSG.RankThree.PartOne.N143.O7

open CFSG.Assembly.RankThreeEven (localRank)

theorem four_le_localRank_of_cover {Y : Type} [Group Y] [Finite Y] (φ : Y →* ↥Om)
    (hφ : Function.Surjective φ) (hker : φ.ker ≤ Subgroup.center Y)
    (hpk : 3 ∣ Nat.card φ.ker) : 4 ≤ localRank 3 Y :=
  succ_le_localRank_of_torus (r := 3) hφ hker Nat.prime_three (by norm_num) hpk thetaOm
    thetaOm_injective thetaOm_swap thetaOm_inv tOm_ne_one tOm_sq tOm_commute

end CFSG.RankThree.PartOne.N143.O7
