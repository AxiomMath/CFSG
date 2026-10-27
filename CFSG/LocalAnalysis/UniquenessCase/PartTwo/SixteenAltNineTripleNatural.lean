module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSpOmegaThreeNatural
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeKNeOneFamilies
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKOuterSix
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeCentralizerRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem s168e3_false_of_sum_three_alt_nine
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom)
    (hs : s15 D.M V₀ V hV L = 1)
    (hAlt : UC22.IsAlt ↥(lBar V₀ V hV L) 9) :
    False := by
  have hcard : Nat.card ↥(lBar V₀ V hV L) = 181440 := by
    rw [s15k_six_alt_card hAlt (by norm_num : 2 ≤ 9)]
    norm_num [Nat.factorial]
  have hcover : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q) := by
    intro Q _ _ hQ ⟨eQ⟩ h3Z
    have : Group.IsPerfect Q := ⟨hQ.1⟩
    have hZ : Nat.card (Subgroup.center Q) ≤ 2 :=
      CFSG.OddStandard.GlueAlt.card_center_le_two_of_alt (by norm_num : 8 ≤ 9)
        (eQ.trans hAlt.some)
    have h3le : 3 ≤ Nat.card (Subgroup.center Q) := Nat.le_of_dvd Nat.card_pos h3Z
    omega
  refine s168e3_false_of_sum_three_of_three_not_dvd_kBar c hcomp hsum htrans hs
    (s16c167_cfg2_simple_alt (by norm_num) hAlt) hcover
    (s168e3_three_not_dvd_kBar_of_alt_nine_to_eleven c hcomp
      (by norm_num : 9 ≤ 9) (by norm_num : 9 ≤ 11) hAlt)
    ?_ (by rw [hcard]; decide +kernel)
  intro p hp hp2 hp3 hp7 hsq
  rw [hcard] at hsq
  rcases s168e3_prime_eq_three_or_seven_of_sq_dvd_336_mul hp hp2 hsq (by norm_num) with h | h
  · exact hp3 h
  · exact hp7 h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
