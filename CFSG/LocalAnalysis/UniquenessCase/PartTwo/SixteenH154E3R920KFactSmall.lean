module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3R920KFact
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNotLarge23.Parts
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3OmegaA
import CFSG.Quasithin.Background.B6Sections

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem kFactL28_not_three_group {Q : Type} [Group Q] [Finite Q] (hQ : IsPGroup 3 Q)
    {X W T : Subgroup Q} (c : KCfgL28 X W T) : False := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨n, hn⟩ := IsPGroup.iff_card.mp hQ
  have h504Bar : 504 ∣ Nat.card (Bar2 X) := by
    rw [s16h_e3_omega_card_of_isL2 c.isL2]
    decide
  have hBarX : Nat.card (Bar2 X) ∣ Nat.card X :=
    Subgroup.card_dvd_of_surjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥X))
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X))
  have hXQ : Nat.card X ∣ Nat.card Q := Subgroup.card_subgroup_dvd_card X
  have h504Q : 504 ∣ Nat.card Q := (h504Bar.trans hBarX).trans hXQ
  rw [hn] at h504Q
  have h7 : 7 ∣ 3 ^ n := (by decide : 7 ∣ 504).trans h504Q
  exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_seven h7) (by decide)

theorem kFactL28_not_J1 {Q : Type} [Group Q] [Finite Q] (hQ : IsSpor Q .J1)
    {X W T : Subgroup Q} (c : KCfgL28 X W T) : False := by
  have h504Bar : 504 ∣ Nat.card (Bar2 X) := by
    rw [s16h_e3_omega_card_of_isL2 c.isL2]
    decide
  have hBarX : Nat.card (Bar2 X) ∣ Nat.card X :=
    Subgroup.card_dvd_of_surjective (f := QuotientGroup.mk' (CFSG.pCore 2 ↥X))
      (QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥X))
  have hXQ : Nat.card X ∣ Nat.card Q := Subgroup.card_subgroup_dvd_card X
  have h504Q : 504 ∣ Nat.card Q := (h504Bar.trans hBarX).trans hXQ
  have hcardQ : Nat.card Q = 175560 :=
    CFSG.LocalAnalysis.UniquenessCase.UC22.KNL23.card_isJ1 hQ
  rw [hcardQ] at h504Q
  exact absurd h504Q (by decide)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
