module


import CFSG.GH74.Orders.LieType
import CFSG.LocalAnalysis.SectionRank.AmbientRank
public import CFSG.LocalAnalysis.UniquenessCase.UC22Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.UC22

theorem card_of_isL2Odd_seven {X : Type} [Group X] (hX : IsL2Odd X 7) : Nat.card X = 168 := by
  have h := CFSG.GH74.card_of_lieModel_PSL (n := 2) (by norm_num) hX
  simpa [ordA] using h

theorem kL2SevenOddRank_holds :
    ∀ (X : Type) [Group X] [Finite X], IsL2Odd X 7 →
      ∀ p : ℕ, p.Prime → p ≠ 2 → pRank p (⊤ : Subgroup X) ≤ 1 := by
  intro X _ _ hX p hp hp2
  have hcard : Nat.card X = 168 := card_of_isL2Odd_seven hX
  rw [CFSG.SectionRank.pRank_coe_eq_openPRank]
  unfold CFSG.Open.pRank
  refine csSup_le' ?_
  rintro k ⟨E, -, -, hE⟩
  by_contra hk
  have hk2 : 2 ≤ k := by omega
  have hdvd : p ^ 2 ∣ 168 := by
    rw [← hcard]
    calc p ^ 2 ∣ p ^ k := pow_dvd_pow p hk2
      _ = Nat.card E := hE.symm
      _ ∣ Nat.card X := Subgroup.card_subgroup_dvd_card E
  have hp12 : p ≤ 12 := by
    have h := Nat.le_of_dvd (by norm_num) hdvd
    nlinarith [hp.two_le]
  have hp2le := hp.two_le
  interval_cases p <;> first | exact hp2 rfl | exact absurd hdvd (by norm_num)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719

end
