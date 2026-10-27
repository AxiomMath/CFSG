module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFourFour
public import CFSG.GroupTheory.ProductAutFactors
public import CFSG.LocalAnalysis.EvenBN.GMSK.CatSporadicBenderLarge
public import CFSG.LocalAnalysis.UniquenessCase.UC6S898b
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.InnerTorusFacts
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.ComponentClassification.OuterAutomorphisms
open CFSG.Blueprint
open CFSG.GroupTheory

theorem card_isL2_ne_card_isU3 {A B : Type} [Group A] [Group B] [Finite A] [Finite B]
    {n : ℕ}
    (hn : 2 ≤ n) (hn_even : Even n) (hA : IsL2 A n) (hB : IsU3 B n) :
    Nat.card A ≠ Nat.card B := by
  have hcardA : Nat.card A = 2 ^ n * (2 ^ (2 * n) - 1) := card_of_isL2 hA
  have hcardBmul : Nat.card B * Nat.gcd 3 (2 ^ n + 1) =
      2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1)) := card_mul_gcd_of_isU3 hB
  have hgcd : Nat.gcd 3 (2 ^ n + 1) = 1 := by
    refine Nat.Coprime.gcd_eq_one ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr ?_)
    exact CFSG.LocalAnalysis.UniquenessCase.UC6S898.not_three_dvd_two_pow_add_one_of_even
      hn_even
  have hcardB : Nat.card B =
      2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1)) := by
    rw [← hcardBmul, hgcd, mul_one]
  rw [hcardA, hcardB]
  have h1 : 2 ^ n < 2 ^ (3 * n) * (2 ^ (3 * n) + 1) := by
    have h2 : 2 ^ n ≤ 2 ^ (3 * n) := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h3 : 1 < 2 ^ (3 * n) + 1 := by
      have hpos : 0 < 2 ^ (3 * n) := pow_pos (by norm_num : (0:ℕ) < 2) (3 * n)
      omega
    nlinarith
  have h4 : 0 < 2 ^ (2 * n) - 1 := by
    have h5 : 1 < 2 ^ (2 * n) := Nat.one_lt_pow (by omega) (by norm_num)
    omega
  have hlt : 2 ^ n * (2 ^ (2 * n) - 1) <
      2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1)) := by
    calc 2 ^ n * (2 ^ (2 * n) - 1)
        < (2 ^ (3 * n) * (2 ^ (3 * n) + 1)) * (2 ^ (2 * n) - 1) :=
          Nat.mul_lt_mul_of_pos_right h1 h4
      _ = 2 ^ (3 * n) * ((2 ^ (2 * n) - 1) * (2 ^ (3 * n) + 1)) := by ring
  exact Nat.ne_of_lt hlt

theorem k_OutL2U3Product_holds : K_OutL2U3Product := by
  intro X _ _ n hn2 hpow hshape
  rcases hpow with ⟨a, rfl⟩
  have ha1 : 1 ≤ a := by
    have h2 : 2 ≤ 2 ^ a := hn2
    by_contra h0
    have : a = 0 := by omega
    subst this
    norm_num at h2
  have hn_even : Even (2 ^ a) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  rcases hshape with ⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩ | ⟨A, B, gA, gB, ⟨e⟩, hA, hB⟩
  ·
    letI : Group A := gA
    letI : Group B := gB
    haveI : Finite A := CFSG.LieType.Simplicity.finite_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hA)
    haveI : Finite B := CFSG.LieType.Simplicity.finite_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hB)
    haveI : IsSimpleGroup A :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA
    haveI : IsSimpleGroup B :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hB
    have hZA : Subgroup.center A = ⊥ := center_eq_bot_of_lieModel_psl2 hA
    have hZB : Subgroup.center B = ⊥ := center_eq_bot_of_lieModel_psl2 hB
    have hOutA : IsPGroup 2 (Outer A) :=
      IsPGroup.of_card_dvd_pow (n := a) (by simpa using card_outer_dvd_of_isL2 hA)
    have hOutB : IsPGroup 2 (Outer B) :=
      IsPGroup.of_card_dvd_pow (n := a) (by simpa using card_outer_dvd_of_isL2 hB)
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    obtain ⟨eA⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField 2 (2 ^ a))
      2 (2 ^ a) (by omega) (GaloisField.card 2 (2 ^ a) (by omega)) hA
    obtain ⟨eB⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField 2 (2 ^ a))
      2 (2 ^ a) (by omega) (GaloisField.card 2 (2 ^ a) (by omega)) hB
    let eAB : B ≃* A := eB.trans eA.symm
    let eProd : A × B ≃* A × A := MulEquiv.prodCongr (MulEquiv.refl A) eAB
    have hOutAA : IsPGroup 2 (Outer (A × A)) :=
      isPGroup_outer_square
        (fun N hN => @IsSimpleGroup.eq_bot_or_eq_top_of_normal A _ _ N hN)
        (fun x hx => by
          have hxc : x ∈ Subgroup.center A :=
            Subgroup.mem_center_iff.mpr (fun c => (hx c).symm)
          rwa [hZA, Subgroup.mem_bot] at hxc)
        (exists_ne (1 : A)) hZA hOutA
    exact hOutAA.of_equiv (equivalence (e.trans eProd)).symm
  ·
    letI : Group A := gA
    letI : Group B := gB
    haveI : Finite A := CFSG.LieType.Simplicity.finite_of_statedClassicalModel
      (CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by norm_num) hA)
    haveI : Finite B := CFSG.LocalAnalysis.EvenBN.GMSK.finite_of_lieModel_PSU3 hB
    haveI : IsSimpleGroup A :=
      CFSG.Blueprint.LieModel.isSimpleGroup_of_mem_classicalTags (by decide) hA
    haveI : IsSimpleGroup B := CFSG.LocalAnalysis.EvenBN.GMSK.isSimpleGroup_of_lieModel_PSU3 hB
    have hZA : Subgroup.center A = ⊥ := center_eq_bot_of_lieModel_psl2 hA
    have hZB : Subgroup.center B = ⊥ := center_eq_bot_of_isU3 hB
    have hOutA : IsPGroup 2 (Outer A) :=
      IsPGroup.of_card_dvd_pow (n := a) (by simpa using card_outer_dvd_of_isL2 hA)
    have hOutB : IsPGroup 2 (Outer B) := by
      have hgcd : Nat.gcd 3 (2 ^ (2 ^ a) + 1) = 1 :=
        Nat.Coprime.gcd_eq_one
          ((Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr
            (CFSG.LocalAnalysis.UniquenessCase.UC6S898.not_three_dvd_two_pow_add_one_of_even
              hn_even))
      have hcard : Nat.card (Outer B) = 2 ^ (a + 1) := by
        rw [CFSG.LocalAnalysis.EvenBN.GMSK.SporadicBender.card_outer_of_lieModel_PSU3 hB,
          hgcd, mul_one]
        rw [show 2 * 2 ^ a = 2 ^ (a + 1) by rw [pow_succ]; ring]
      exact IsPGroup.of_card hcard
    have hcardAB : Nat.card A ≠ Nat.card B :=
      card_isL2_ne_card_isU3 (n := 2 ^ a) hn2 hn_even hA hB
    have hOutAB : IsPGroup 2 (Outer (A × B)) :=
      isPGroup_outer_prod_of_card_ne hcardAB hZA hZB hOutA hOutB
    exact hOutAB.of_equiv (equivalence e).symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
