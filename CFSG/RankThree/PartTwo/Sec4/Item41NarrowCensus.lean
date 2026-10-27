module

public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
public import CFSG.RankThree.PartTwo.Sec4.Census.TripleCoverResidual
import CFSG.RankThree.PartTwo.Sec4.Census.Simple46
import CFSG.RankThree.PartTwo.Sec4.Census.Cover46

public section

namespace CFSG.RankThree.PartTwo.Sec4.Census

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Sec4 TauCeti
open CFSG.RankThree.PartOne.Census3
open CFSG.Assembly.LowTwoRank CFSG.Models
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.Blueprint.Multiplier (genericOrders exceptionalOrders)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)
open CFSG.GH74.Generic (card_center_dvd_hopfMultiplier centralQuotientMap
  centralQuotientMap_surjective centralQuotientMap_ker card_eq_card_mul_card_ker)

section Item43

theorem rank3II_4_3_of_narrow41 (h1 : Item4_1LargePrime) (h2 : Item4_1ThreeCover)
    (hGA : GriessMultipliersAllModels) (hres : TripleCoverSporadicResidual) : Item4_3 := by
  intro G _ _ hG hq h3
  have hS : SectionFourHyp (G ⧸ Subgroup.center G) :=
    Item41Narrow.sectionFourHyp_quotient_center h1 h2 hG hq
  have : IsSimpleGroup (G ⧸ Subgroup.center G) := hq.2.1
  have hnonab : ∃ a b : G ⧸ Subgroup.center G, a * b ≠ b * a := hq.2.2
  obtain ⟨i, ⟨e⟩⟩ := exists_index_of_sectionFourHyp hS
  have htc : IsThreeCenterCover G i.Group := ⟨hq, h3, ⟨e⟩⟩
  have hex : ∀ {j : CFSGIndex}, ExcludedIndex j → (G ⧸ Subgroup.center G ≃* j.Group) → False :=
    fun hj e' => SectionFourHyp.false_of_four_le_twoLocalOddRank hS (hj _ this hnonab e')
  have hexG : 4 ≤ CFSG.twoLocalOddRank G → False :=
    SectionFourHyp.false_of_four_le_twoLocalOddRank hG
  have hspin := PartOne.CTP.spinRankFour
  have hexc := CFSG.RankThree.PartTwo.Census.Exceptional.exceptionalRankFour
  cases i with
  | cyclic p hp =>
    exfalso
    obtain ⟨a, b, hab⟩ := hnonab
    have hc : ∀ x y : (CFSGIndex.cyclic p hp).Group, x * y = y * x := fun x y => mul_comm x y
    exact hab (e.injective (by rw [map_mul, map_mul]; exact hc _ _))
  | alternating n hn =>
    rcases tripleCoverAlternating n G hn htc with rfl | rfl
    · exact Or.inr (Or.inl ⟨e⟩)
    · exact Or.inr (Or.inr (Or.inl ⟨e⟩))
  | sporadic s =>
    rcases item43_sporadic hres hG hS hnonab e htc with h | h | h | h
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))))
    · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))))
  | lie d =>
    obtain ⟨d, hv⟩ := d
    have hd := tripleCoverLie_of_griess hGA ⟨d, hv⟩ G htc
    cases d with
    | A r q =>
      obtain ⟨h3r, h3q⟩ := hd
      have hr1 : 1 ≤ r :=
        ((LieTypeIndex.inStandardRange_iff _).mp ((LieTypeIndex.valid_iff _).mp hv).1).1
      rcases (show r = 2 ∨ 5 ≤ r by omega) with rfl | hr5
      · exact Or.inl ⟨q.p, q.exponent, ⟨q.prime_p⟩, q.exponent_pos, isoLThreePi_of_A2 hv h3q e⟩
      · refine (hex (excludedIndex_A_of_five_le r q hv hr5 ?_) e).elim
        by_contra hq
        push Not at hq
        have hc : q.card = 2 := by
          rw [PrimePower.card_def, hq.1, show q.exponent = 1 by have := q.exponent_pos; omega]
          norm_num
        rw [hc] at h3q
        omega
    | twistedA r q =>
      have hr2 : 2 ≤ r :=
        LieTypeIndex.two_le_of_twistedA_inStandardRange ((LieTypeIndex.valid_iff _).mp hv).1
      rcases hd with ⟨h3r, h3q⟩ | ⟨rfl, hq3⟩
      · rcases (show r = 2 ∨ 5 ≤ r by omega) with rfl | hr5
        · exact Or.inl ⟨q.p, q.exponent, ⟨q.prime_p⟩, q.exponent_pos,
            isoLThreePi_of_twistedA2 hv h3q e⟩
        · by_cases h62 : r = 5 ∧ q.p = 2 ∧ q.exponent = 1
          · exact (hexG (tripleCoverU62RankFour q (h62.1 ▸ hv) h62.2.1 h62.2.2 G (by
              obtain ⟨rfl, -, -⟩ := h62
              exact htc))).elim
          · exact (hex (excludedIndex_twistedA_of_five_le r q hv hr5 h62) e).elim
      · obtain ⟨hp3, hf1⟩ := eq_three_of_card_eq_three hq3
        obtain ⟨p, f, hp, hf⟩ := q
        obtain rfl : p = 3 := hp3
        obtain rfl : f = 1 := hf1
        exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl
          ⟨e.trans (CFSG.RankThree.PartTwo.Census.typeTwistedAGroupEquivProjSU 3 _ hv)⟩))))
    | B r q =>
      obtain ⟨rfl, hq3⟩ := hd
      obtain ⟨hp3, -⟩ := eq_three_of_card_eq_three hq3
      exact (hex (excludedIndex_of_four_le (hspin.typeB 3 q hv le_rfl (fun h => by omega)
        (fun h => by omega))) e).elim
    | G2 q =>
      obtain ⟨hp3, hf1⟩ := eq_three_of_card_eq_three hd
      exact Or.inr (Or.inr (Or.inr (Or.inl
        (CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv e
          (chevalleyExceptionalModel_G2_three q hv hp3 hf1)))))
    | E6 q => exact (hex (excludedIndex_of_four_le (hexc.e6 q hv)) e).elim
    | twistedE6 q => exact (hex (excludedIndex_of_four_le (hexc.twistedE6 q hv)) e).elim
    | C r q => exact hd.elim
    | D r q => exact hd.elim
    | twistedD r q => exact hd.elim
    | E7 q => exact hd.elim
    | E8 q => exact hd.elim
    | F4 q => exact hd.elim
    | trialityD4 q => exact hd.elim
    | suzuki m => exact hd.elim
    | reeG2 m => exact hd.elim
    | reeF4 m => exact hd.elim
    | tits => exact hd.elim

end Item43

section Item43Griess

theorem rank3II_4_3_of_griess_narrow41 (h1 : Item4_1LargePrime) (h2 : Item4_1ThreeCover)
    (hGA : GriessMultipliersAllModels) : Item4_3 :=
  rank3II_4_3_of_narrow41 h1 h2 hGA tripleCoverSporadicResidual

end Item43Griess

section Item46

theorem rank3II_4_6_of_items_narrow41 (h1 : Item4_1LargePrime) (h2 : Item4_1ThreeCover)
    (h42 : Item4_2) (h43 : Item4_3) (hin : Inputs46) : Item4_6 := by
  intro G _ _ hG h3 L hL
  have hq : CFSG.IsQuasisimple (L ⧸ aschbacherSolvableCore 3 L) := hL.2.2
  have hS := Item41Narrow.sectionFourHyp_thetaQuotient h1 hG hL
  have hZ3 := isPGroup_center_thetaQuotient L
  by_cases hZ : Subgroup.center (L ⧸ aschbacherSolvableCore 3 L) = ⊥
  · have : IsSimpleGroup (L ⧸ aschbacherSolvableCore 3 L) := isSimpleGroup_of_center_eq_bot hq hZ
    obtain ⟨z, hz, hz3⟩ := exists_orderOf_eq_three_of_dvd h3
    exact isList46_of_list42 hZ
      (localRank_thetaQuotient_le_two hG hz hz3 (not_mem_of_center_eq_bot hz hz3 hZ)) hin.rank
      hin.bridge (h42 _ hS inferInstance (exists_ne_of_isQuasisimple hq))
  · have h3Z : 3 ∣ Nat.card (Subgroup.center (L ⧸ aschbacherSolvableCore 3 L)) := by
      obtain ⟨k, hk⟩ := IsPGroup.iff_card.mp hZ3
      have hk0 : k ≠ 0 := by
        rintro rfl
        exact hZ (Subgroup.card_eq_one.mp (by rw [hk, pow_zero]))
      rw [hk]
      exact dvd_pow_self 3 hk0
    exact isList46_of_cover hS
      (Item41Narrow.sectionFourHyp_quotient_center_of_isPGroup h2 hS hq hZ3) hq hZ3 hZ hin.cover
      (h43 _ hS hq h3Z)

end Item46

section Item46Griess

theorem rank3II_4_6_of_griess_narrow41 (h1 : Item4_1LargePrime) (h2 : Item4_1ThreeCover)
    (hGA : GriessMultipliersAllModels) (hcen : CoverCenterThreeRest) : Item4_6 :=
  rank3II_4_6_of_items_narrow41 h1 h2 rank3II_4_2 (rank3II_4_3_of_griess_narrow41 h1 h2 hGA)
    (Inputs46.of_open coverSLThree46 (coverCenterThree_of_rest hcen) nineCoverU43RankFour
      (RankThree46Open.of_sporadic rankThree46Sporadic))

end Item46Griess

end CFSG.RankThree.PartTwo.Sec4.Census
