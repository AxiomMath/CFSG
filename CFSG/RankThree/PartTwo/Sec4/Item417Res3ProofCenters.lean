module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofSmallTwo
public import CFSG.RankThree.PartOne.Mult.Exceptional
import CFSG.RankThree.PartTwo.KFacts.KS21Mult
import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherEasy
import CFSG.RankThree.SteinbergR3ECASymplecticPrimeSubfield
import CFSG.LocalAnalysis.SectionRank.EvenCover.Symplectic

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSL projSU projSp)
open CFSG.Assembly.LowTwoRank (StatedSp StatedProj StatedLieAdmissible)
open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

namespace Res417Three

theorem false_of_sp42 {Y : Type} [Group Y] [Group.IsPerfect Y]
    (φ : Y ⧸ Subgroup.center Y ≃* projSp 2 (GaloisField 2 1)) : False := by
  have hperf : Group.IsPerfect (Y ⧸ Subgroup.center Y) :=
    Group.IsPerfect.ofSurjective (f := QuotientGroup.mk' (Subgroup.center Y))
      (QuotientGroup.mk'_surjective _)
  let ψ : StatedProj (StatedSp 2 (GaloisField 2 1)) ≃* StatedSp 2 (GaloisField 2 1) :=
    (QuotientGroup.quotientMulEquivOfEq
      (CFSG.SectionRank.EvenCover.statedScalars_subgroupOf_statedSp_eq_bot 2)).trans
      QuotientGroup.quotientBot
  have : Fintype (GaloisField 2 1) := Fintype.ofFinite _
  obtain ⟨ω⟩ := CFSG.RankThree.CASymplecticSubfield.nonempty_statedSp_two_mulEquiv_perm
    (k := GaloisField 2 1)
    (by rw [← Nat.card_eq_fintype_card, GaloisField.card 2 1 one_ne_zero, pow_one])
  let θ := ((φ.trans (projSpEquivStatedProj 2 (GaloisField 2 1))).trans ψ).trans ω
  exact Item434SmallTwoOther.not_isPerfect_perm_six
    (Group.IsPerfect.ofSurjective (f := θ.toMonoidHom) θ.surjective)

theorem not_dvd_center_of_lieModel (hGA : GriessMultipliersAllModels) {Y : Type} [Group Y]
    [Finite Y] (hY : IsQuasisimple Y) {t : CFSG.Assembly.LowTwoRank.StatedLieTag} {n p f : ℕ}
    (hm : CFSG.Models.LieModel (Y ⧸ Subgroup.center Y) t n p f) {r : ℕ} (hr : r.Prime)
    (hr3 : 3 < r) (h1 : t = .PSL → r ∣ n → r ∣ p ^ f - 1 → False)
    (h2 : t = .PSU → r ∣ n → r ∣ p ^ f + 1 → False) : ¬ r ∣ Nat.card (Subgroup.center Y) := by
  intro hrZ
  rcases CFSG.RankThree.PartOne.prime_dvd_table hr hr3
      (hrZ.trans (CFSG.RankThree.PartOne.Mult.card_center_dvd_of_lieModel hGA hY hm)) with
    ⟨ht, hrn, hq⟩ | ⟨ht, hrn, hq⟩
  · exact h1 ht hrn hq
  · exact h2 ht hrn hq

theorem k417CenterChevTwo_of_griess
    (hGA : GriessMultipliersAllModels) : K417CenterChevTwo := by
  intro Y _ _ hY hX r hr hr3 hrZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Group.IsPerfect Y := hY.1
  have hr5 : 5 ≤ r := CFSG.RankThree.PartOne.five_le_of_prime' hr hr3
  have hr4 : ¬ r ∣ 4 := fun h => absurd (Nat.le_of_dvd (by norm_num) h) (by omega)
  rcases hX with ⟨n, hn, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ | ⟨f, hG2 | hD4 | hF4 | hT⟩
  · rcases Nat.lt_or_ge n 2 with hn2 | hn2
    · obtain rfl : n = 1 := by omega
      exact false_of_sp42 φ
    · have h4 : 4 ≤ 2 ^ n := by
        calc 4 = 2 ^ 2 := by norm_num
          _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn2
      have hadm : StatedLieAdmissible .PSp 2 2 n :=
        ⟨Nat.prime_two, hn, le_rfl, fun h => by
          have h2 : (2 : ℕ) ^ n = 2 := congrArg Prod.snd h
          rw [h2] at h4
          omega⟩
      exact not_dvd_center_of_lieModel hGA hY
        (KFacts.KS21Mult.lieModel_of_mulEquiv φ (KFacts.KS21Mult.lieModel_projSp hadm)) hr hr3
        (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hrZ
  · have hadm : StatedLieAdmissible .PSU 4 2 n :=
      ⟨Nat.prime_two, hn, by norm_num, fun h => by
        have h2 : (4 : ℕ) = 3 := congrArg Prod.fst h
        omega⟩
    exact not_dvd_center_of_lieModel hGA hY
      (KFacts.KS21Mult.lieModel_of_mulEquiv φ (KFacts.KS21Mult.lieModel_projSU hadm)) hr hr3
      (fun h => absurd h (by decide)) (fun _ h => absurd h hr4) hrZ
  · exact CFSG.RankThree.PartOne.Mult.exceptionalCenterSmallPrimes_of_griess hGA Y hY
      (Or.inl ⟨.G2, 2, f, by simp [chevalleyExceptionalTags], hG2⟩) r hr hr3 hrZ
  · exact CFSG.RankThree.PartOne.Mult.exceptionalCenterSmallPrimes_of_griess hGA Y hY
      (Or.inl ⟨.trialityD4, 2, f, by simp [chevalleyExceptionalTags], hD4⟩) r hr hr3 hrZ
  · exact CFSG.RankThree.PartOne.Mult.exceptionalCenterSmallPrimes_of_griess hGA Y hY
      (Or.inr (Or.inl ⟨.twistedF4, 2, f, by simp [reeTitsTags], hF4⟩)) r hr hr3 hrZ
  · exact CFSG.RankThree.PartOne.Mult.exceptionalCenterSmallPrimes_of_griess hGA Y hY
      (Or.inr (Or.inl ⟨.Tits, 2, f, by simp [reeTitsTags], hT⟩)) r hr hr3 hrZ

@[expose] def K417CenterU54 : Prop :=
  ∀ (Y : Type) [Group Y] [Finite Y], IsQuasisimple Y → SectionFourHyp Y →
    Nonempty (Y ⧸ Subgroup.center Y ≃* projSU 5 2 2) → ¬ 5 ∣ Nat.card (Subgroup.center Y)

theorem k417CenterSmallTwo_of_griess (hGA : GriessMultipliersAllModels)
    (hU : K417CenterU54) : K417CenterSmallTwo := by
  intro Y _ _ hY hS hX r hr hr3 hrZ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rcases hX with ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩
  · have hadm : StatedLieAdmissible .PSL 5 2 1 :=
      ⟨Nat.prime_two, le_rfl, by norm_num, by decide, by decide⟩
    exact not_dvd_center_of_lieModel hGA hY
      (KFacts.KS21Mult.lieModel_of_mulEquiv φ (KFacts.KS21Mult.lieModel_projSL hadm)) hr hr3
      (fun _ _ h => by
        have := Nat.le_of_dvd (by norm_num) h
        have := hr.two_le
        omega)
      (fun h => absurd h (by decide)) hrZ
  · have hadm : StatedLieAdmissible .PSp 3 2 1 := ⟨Nat.prime_two, le_rfl, by norm_num, by decide⟩
    exact not_dvd_center_of_lieModel hGA hY
      (KFacts.KS21Mult.lieModel_of_mulEquiv φ (KFacts.KS21Mult.lieModel_projSp hadm)) hr hr3
      (fun h => absurd h (by decide)) (fun h => absurd h (by decide)) hrZ
  · have hadm : StatedLieAdmissible .PSU 5 2 2 := ⟨Nat.prime_two, by norm_num, by norm_num,
      by decide⟩
    refine not_dvd_center_of_lieModel hGA hY
      (KFacts.KS21Mult.lieModel_of_mulEquiv φ (KFacts.KS21Mult.lieModel_projSU hadm)) hr hr3
      (fun h => absurd h (by decide)) (fun _ h5 _ => ?_) hrZ
    have hr5 : r = 5 := (Nat.prime_dvd_prime_iff_eq hr (by norm_num)).mp h5
    subst hr5
    exact hU Y hY hS ⟨φ⟩ hrZ

end Res417Three

end CFSG.RankThree.PartTwo.Sec4
