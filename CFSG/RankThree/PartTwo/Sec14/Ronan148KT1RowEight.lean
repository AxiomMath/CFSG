module

public import CFSG.RankThree.PartTwo.Sec14.Ronan148KT1RowSpor2
public import CFSG.RankThree.PartTwo.Sec4.RonanEpsRowGF2
public import CFSG.RankThree.PartTwo.Sec4.Item47Unitary
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherL52
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoOtherU54
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434SmallTwoIIISp62
public import CFSG.RankThree.PartTwo.KFacts.KS21FusionL44
public import CFSG.RankThree.PartTwo.Sec19.Step1919EndProof
public import CFSG.LocalAnalysis.EvenSmallLie.OmegaEightMinus.NativeAut

public section

namespace CFSG.RankThree.PartTwo.Sec14.Ronan148K

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo
open CFSG.ComponentClassification.OuterAutomorphisms (Outer)
open CFSG.Assembly.RankThreeEven (projSL projSU projSp projOmegaPlus projOmegaMinus)

set_option linter.unusedSectionVars false

theorem card_projSL_five_two_gf2 : Nat.card (projSL 5 (GaloisField 2 1)) = 9999360 := by
  rw [← Nat.card_congr (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.slEquivProjSL
    (by norm_num : 1 ≤ 5)).toEquiv, CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.L52.card_SL5]

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound) in
theorem card_outer_projSL_gf2_dvd_two {n : ℕ} (hn : 3 ≤ n) :
    Nat.card (Outer (projSL n (GaloisField 2 1))) ∣ 2 := by
  have hd := higher_linear_outer_order_divides_field_gcd_bound
    (k := GaloisField 2 1) Nat.prime_two le_rfl hn (GaloisField.card 2 1 one_ne_zero)
  have h1 : 2 * 1 * Nat.gcd n (2 ^ 1 - 1) = 2 := by norm_num
  rw [h1] at hd
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (CFSG.RankThree.PartTwo.Sec4.projSLEquivProjectiveSL n (GaloisField 2 1))).toEquiv]
  exact hd

open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  (higher_linear_outer_order_divides_field_gcd_bound) in
theorem card_outer_projSL_gf4_dvd_four :
    Nat.card (Outer (projSL 4 (GaloisField 2 2))) ∣ 4 := by
  have hd := higher_linear_outer_order_divides_field_gcd_bound
    (k := GaloisField 2 2) (p := 2) (f := 2) (n := 4) Nat.prime_two (by norm_num)
    (by norm_num) (GaloisField.card 2 2 (by norm_num))
  have h4 : 2 * 2 * Nat.gcd 4 (2 ^ 2 - 1) = 4 := by norm_num
  rw [h4] at hd
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (CFSG.RankThree.PartTwo.Sec4.projSLEquivProjectiveSL 4 (GaloisField 2 2))).toEquiv]
  exact hd

theorem card_outer_projSp_four_two_le_two :
    Nat.card (Outer (projSp 4 (GaloisField 2 1))) ≤ 2 := by
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    (CFSG.PGLModel.projSpEquivStatedProj 4 (GaloisField 2 1))).toEquiv]
  have hK : Nat.card (GaloisField 2 1)ˣ = 1 := by
    rw [Nat.card_units, GaloisField.card 2 1 one_ne_zero]
    norm_num
  have h1 := CFSG.RankThree.PartTwo.Sec19.Step1919EndProof.card_outer_statedSp_le
    (r := 4) (by norm_num) hK
  have h2 := CFSG.RankThree.PartTwo.Sec19.Step1919EndProof.card_ringEquiv_le (GaloisField 2 1)
  rw [GaloisField.card 2 1 one_ne_zero, pow_one] at h2
  exact h1.trans h2

theorem card_outer_dvd_sixty_of_le_six {X : Type} [Group X] [Finite X]
    (h : Nat.card (Outer X) ≤ 6) : Nat.card (Outer X) ∣ 60 := by
  haveI : Finite (MulAut X) :=
    Finite.of_injective (fun φ : MulAut X => (φ : X → X)) DFunLike.coe_injective
  have hpos : 0 < Nat.card (Outer X) := Nat.card_pos
  have key : ∀ n : ℕ, n < 7 → 0 < n → n ∣ 60 := by decide
  exact key _ (by omega) hpos

theorem card_outer_projOmegaPlus_four_two_dvd :
    Nat.card (Outer (projOmegaPlus 4 (GaloisField 2 1))) ∣ 60 := by
  have hmodel : CFSG.Open.StatedClassicalModel (projOmegaPlus 4 (GaloisField 2 1))
      .POmegaPlus 4 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, le_refl 4⟩, GaloisField 2 1, inferInstance, inferInstance,
      GaloisField.card 2 1 one_ne_zero,
      ⟨CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIV.statedOmegaPlusEquiv.symm⟩⟩
  haveI : Finite (projOmegaPlus 4 (GaloisField 2 1)) :=
    Nat.finite_of_card_ne_zero (by
      rw [CFSG.RankThree.PartTwo.Sec4.RonanEps.card_projOmegaPlus_four_two_gf2]; norm_num)
  exact card_outer_dvd_sixty_of_le_six (CFSG.EvenSmallLie.OmegaEight.card_outer_le_six hmodel)

theorem card_outer_projOmegaMinus_four_two_le_two {b c : GaloisField 2 1}
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) :
    Nat.card (Outer (projOmegaMinus 3 (GaloisField 2 1) b c)) ≤ 2 := by
  have hK : Nat.card (GaloisField 2 1) = 2 ^ 1 := GaloisField.card 2 1 one_ne_zero
  have e₀ : projOmegaMinus 3 (GaloisField 2 1) b c ≃*
      CFSG.Open.StatedProj (CFSG.Open.StatedOmega
        (CFSG.Open.StatedQuadMinus 4 (GaloisField 2 1) b c)) :=
    ((CFSG.Adapters.RankTwoModelTransports.statedProjEquivMapMk _).trans
      (MulEquiv.subgroupCongr
        (CFSG.RankThree.PartOne.projImage_statedOmegaMinus_eq_projOmegaMinus 4 _ b c))).symm
  have hmod : CFSG.Open.StatedClassicalModel (projOmegaMinus 3 (GaloisField 2 1) b c)
      .POmegaMinus 4 2 1 :=
    ⟨⟨Nat.prime_two, le_rfl, le_rfl⟩, GaloisField 2 1, inferInstance, inferInstance, hK, b, c, hbc,
      ⟨e₀⟩⟩
  exact CFSG.EvenSmallLie.OmegaEightMinus.card_outer_le_two hmod

theorem card_outer_projSp_three_two : Nat.card (Outer (projSp 3 (GaloisField 2 1))) = 1 := by
  rw [Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence
    CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.sp62Equiv).toEquiv]
  exact CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoIII.card_outer_H6

section Row143


theorem rowOf143_eight_SL5 : RowOf143 (projSL 5 (GaloisField 2 1)) := by
  have hX := card_projSL_five_two_gf2
  haveI : Finite (projSL 5 (GaloisField 2 1)) :=
    Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  refine rowOf143_of_outer_dvd (k := 2)
    (card_outer_projSL_gf2_dvd_two (n := 5) (by norm_num)) ?_
  rw [hX]
  exact not_suzukiOrder_dvd_of_check (B := 5) (by norm_num) (by norm_num) (by decide)

theorem rowOf143_eight_SU5 : RowOf143 (projSU 5 2 1) := by
  have hX := CFSG.RankThree.PartTwo.Sec4.RonanEps.card_projSU_five_two_gf2
  haveI : Finite (projSU 5 2 1) := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have hout : Nat.card (Outer (projSU 5 2 1)) ∣ 6 := by
    have h := CFSG.RankThree.PartTwo.Sec4.card_outer_projSU_dvd 5 2 1 le_rfl
      (by norm_num) (by norm_num)
    have h6 : 2 * 1 * (2 ^ 1 + 1) = 6 := by norm_num
    rw [h6] at h
    exact h
  refine rowOf143_of_outer_dvd (k := 6) hout ?_
  rw [hX]
  exact not_suzukiOrder_dvd_of_check (B := 6) (by norm_num) (by norm_num) (by decide)

theorem rowOf143_eight_SL6 : RowOf143 (projSL 6 (GaloisField 2 1)) := by
  have hX := CFSG.RankThree.PartTwo.Sec4.RonanEps.card_projSL_six_two_gf2
  haveI : Finite (projSL 6 (GaloisField 2 1)) :=
    Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  refine rowOf143_of_outer_dvd (k := 2)
    (card_outer_projSL_gf2_dvd_two (n := 6) (by norm_num)) ?_
  rw [hX]
  exact not_suzukiOrder_dvd_of_check (B := 8) (by norm_num) (by norm_num) (by decide)

theorem rowOf143_eight_SU6 : RowOf143 (projSU 6 2 1) := by
  have hX := CFSG.RankThree.PartTwo.Sec4.RonanEps.card_projSU_six_two_gf2
  haveI : Finite (projSU 6 2 1) := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have hout : Nat.card (Outer (projSU 6 2 1)) ∣ 6 := by
    have h := CFSG.RankThree.PartTwo.Sec4.card_outer_projSU_dvd 6 2 1 le_rfl
      (by norm_num) (by norm_num)
    have h6 : 2 * 1 * (2 ^ 1 + 1) = 6 := by norm_num
    rw [h6] at h
    exact h
  refine rowOf143_of_outer_dvd (k := 6) hout ?_
  rw [hX]
  exact not_suzukiOrder_dvd_of_check (B := 8) (by norm_num) (by norm_num) (by decide)

theorem rowOf143_eight_SL7 : RowOf143 (projSL 7 (GaloisField 2 1)) := by
  have hX := CFSG.RankThree.PartTwo.Sec4.RonanEps.card_projSL_seven_two_gf2
  haveI : Finite (projSL 7 (GaloisField 2 1)) :=
    Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  refine rowOf143_of_outer_dvd (k := 2)
    (card_outer_projSL_gf2_dvd_two (n := 7) (by norm_num)) ?_
  rw [hX]
  exact not_suzukiOrder_dvd_of_check (B := 11) (by norm_num) (by norm_num) (by decide)

theorem rowOf143_eight_Sp6 : RowOf143 (projSp 3 (GaloisField 2 1)) := by
  have hX := CFSG.RankThree.PartTwo.Sec4.RonanEps.card_projSp_three_two_gf2
  haveI : Finite (projSp 3 (GaloisField 2 1)) :=
    Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  refine rowOf143_of_outer_dvd (k := 1) (by simp [card_outer_projSp_three_two]) ?_
  rw [hX]
  exact not_suzukiOrder_dvd_of_check (B := 4) (by norm_num) (by norm_num) (by decide)

theorem rowOf143_eight_Sp8 : RowOf143 (projSp 4 (GaloisField 2 1)) := by
  have hX := CFSG.RankThree.PartTwo.Sec4.RonanEps.card_projSp_four_two_gf2
  haveI : Finite (projSp 4 (GaloisField 2 1)) :=
    Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  refine rowOf143_of_outer_dvd (k := 2)
    (card_outer_dvd_two_of_le_two card_outer_projSp_four_two_le_two) ?_
  rw [hX]
  exact not_suzukiOrder_dvd_of_check (B := 8) (by norm_num) (by norm_num) (by decide)

theorem rowOf143_eight_OmegaPlus : RowOf143 (projOmegaPlus 4 (GaloisField 2 1)) := by
  have hX := CFSG.RankThree.PartTwo.Sec4.RonanEps.card_projOmegaPlus_four_two_gf2
  haveI : Finite (projOmegaPlus 4 (GaloisField 2 1)) :=
    Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  refine rowOf143_of_outer_dvd (k := 60) card_outer_projOmegaPlus_four_two_dvd ?_
  rw [hX]
  exact not_suzukiOrder_dvd_of_check (B := 7) (by norm_num) (by norm_num) (by decide)

theorem rowOf143_eight_OmegaMinus (b c : GaloisField 2 1)
    (hbc : ∀ s : GaloisField 2 1, s ^ 2 + b * s + c ≠ 0) :
    RowOf143 (projOmegaMinus 3 (GaloisField 2 1) b c) := by
  have hX := CFSG.RankThree.PartTwo.Sec4.RonanEps.card_projOmegaMinus_four_two_gf2 hbc
  haveI : Finite (projOmegaMinus 3 (GaloisField 2 1) b c) :=
    Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  refine rowOf143_of_outer_dvd (k := 2)
    (card_outer_dvd_two_of_le_two (card_outer_projOmegaMinus_four_two_le_two hbc)) ?_
  rw [hX]
  exact not_suzukiOrder_dvd_of_check (B := 6) (by norm_num) (by norm_num) (by decide)

theorem rowOf143_eight_SL4 : RowOf143 (projSL 4 (GaloisField 2 2)) := by
  have hX : Nat.card (projSL 4 (GaloisField 2 2)) = 987033600 :=
    ((Nat.card_congr CFSG.RankThree.PartTwo.KFacts.KS21.L44.equivSL.toEquiv).trans
      CFSG.RankThree.PartTwo.KFacts.KS21.L44.card_M_eq).trans (by norm_num)
  haveI : Finite (projSL 4 (GaloisField 2 2)) :=
    Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  refine rowOf143_of_outer_dvd (k := 4) card_outer_projSL_gf4_dvd_four ?_
  rw [hX]
  exact not_suzukiOrder_dvd_of_check (B := 7) (by norm_num) (by norm_num) (by decide)

theorem rowOf143_eight_SU5_4 : RowOf143 (projSU 5 2 2) := by
  have hX : Nat.card (projSU 5 2 2) = 53443952640000 :=
    (CFSG.RankThree.PartTwo.Sec4.Item434SmallTwoOther.U54.card_U54).trans (by norm_num)
  haveI : Finite (projSU 5 2 2) := Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have hout : Nat.card (Outer (projSU 5 2 2)) ∣ 20 := by
    have h := CFSG.RankThree.PartTwo.Sec4.card_outer_projSU_dvd 5 2 2
      (by norm_num) (by norm_num) (by norm_num)
    have h20 : 2 * 2 * (2 ^ 2 + 1) = 20 := by norm_num
    rw [h20] at h
    exact h
  refine rowOf143_of_outer_dvd (k := 20) hout ?_
  rw [hX]
  exact not_suzukiOrder_dvd_of_check (B := 11) (by norm_num) (by norm_num) (by decide)

theorem rowOf143_seven_Tits
    (ht : TauCeti.LieTypeIndex.tits.Valid) :
    RowOf143 (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group := by
  have hm : CFSG.Blueprint.ReeTitsModel (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group .Tits 2 1 :=
    CFSG.RankThree.PartTwo.Sec4.Census.bridgeExceptional46.tits ht
  obtain ⟨e⟩ := CFSG.Sporadic.Schreier.Tits.titsModelEquiv _ 2 1 hm
  have hX : Nat.card (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group = 17971200 :=
    (Nat.card_congr e.toEquiv).trans CFSG.Sporadic.Schreier.Tits.card_titsD
  haveI : Finite (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group :=
    Nat.finite_of_card_ne_zero (by rw [hX]; norm_num)
  have hout : Nat.card (Outer (TauCeti.CFSGIndex.lie ⟨.tits, ht⟩).Group) = 2 :=
    (Nat.card_congr (CFSG.ComponentClassification.OuterAutomorphisms.equivalence e).toEquiv).trans
      CFSG.Sporadic.Schreier.Tits.card_outer_titsD
  refine rowOf143_of_outer_dvd (k := 2) (by simp [hout]) ?_
  rw [hX]
  exact not_suzukiOrder_dvd_of_check (B := 5) (by norm_num) (by norm_num) (by decide)

end Row143

end CFSG.RankThree.PartTwo.Sec14.Ronan148K
