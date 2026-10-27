module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9Core
import CFSG.RankThree.PartTwo.Sec15.Sylow155R3K9Crit

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R3

theorem goodJ2_of_not_dvd_twentyFive {S : Type} [Group S] {C : Subgroup S}
    (h : ¬ 25 ∣ Nat.card C) : GoodJ2 C :=
  goodJ2_of_card_dvd dvd_rfl fun h' => h ((by norm_num : (25 : ℕ) ∣ 604800).trans h')

theorem goodJ2_of_selfCentralizing3 {S : Type} [Group S] [Finite S] {C R : Subgroup S}
    (hRC : R ≤ C) (hRn : ∀ g ∈ C, ∀ r ∈ R, g * r * g⁻¹ ∈ R) (hR3 : IsPGroup 3 R)
    (hcent : Subgroup.centralizer (R : Set S) ⊓ C ≤ R) (hcard : Nat.card R ≤ 3 ^ 7) :
    GoodJ2 C :=
  goodJ2_of_not_dvd_twentyFive (not_dvd_card_of_selfCentralizing_three hRC hRn hR3 hcent hcard)

end CFSG.RankThree.PartTwo.Sec15.Sylow155R3
