module

public import CFSG.RankThree.PartTwo.Sec13.KF135Fam2
public import CFSG.RankThree.PartTwo.Sec4.Census.BridgeG2
import CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerpSmQ3LG2
import CFSG.Models.PGLOrders
public import CFSG.RankThree.SteinbergR3ELinearUnitaryOuterOrder

public section

namespace CFSG.RankThree.PartTwo.Sec13.KF135Proof

open CFSG Subgroup
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.ComponentClassification.OuterAutomorphisms (inner Outer)
open CFSG.RankThree.PartTwo.Sec4 (g2ThreeIndex)

namespace FamOdd

theorem card_outer_dvd_two_of_le {S : Type} [Group S] [Finite S]
    (h : Nat.card (Outer S) ≤ 2) : Nat.card (Outer S) ∣ 2 := by
  have h0 : 0 < Nat.card (Outer S) := Nat.card_pos
  interval_cases (Nat.card (Outer S)) <;> norm_num

theorem card_SL_four_three :
    Nat.card (Matrix.SpecialLinearGroup (Fin 4) (GaloisField 3 1)) = 12130560 := by
  haveI : Fintype (GaloisField 3 1) := Fintype.ofFinite _
  have hq : Fintype.card (GaloisField 3 1) = 3 := by
    rw [Fintype.card_eq_nat_card, GaloisField.card 3 1 (by norm_num), pow_one]
  rw [Matrix.card_SL_field, hq]
  simp [Fin.prod_univ_four]

theorem psl4Three_hyp_false {S : Type} [Group S] [Finite S] {p : ℕ} {P : Subgroup (MulAut S)}
    {x u : MulAut S} {V : Subgroup (MulAut S)} (φ : S ≃* projSL 4 (GaloisField 3 1))
    (h : KF135Hyp S p P x u V) : False := by
  have hadm : CFSG.Open.StatedLieAdmissible .PSL 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by simp, by simp⟩
  have hS := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSL hadm φ
  obtain ⟨hout, -⟩ :=
    CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound (Or.inl rfl)
      (by norm_num) Nat.prime_three le_rfl hS
  have hout4 : Nat.card (Outer S) ∣ 4 :=
    hout.trans (by norm_num [CFSG.RankThree.OuterOrder.determinantParameter])
  have hcard : Nat.card S ∣ 12130560 := by
    rw [Nat.card_congr φ.toEquiv, ← card_SL_four_three]
    exact (Subgroup.card_dvd_of_le (projSL_le_range_toPGL3 4 (GaloisField 3 1))).trans
      (Subgroup.card_range_dvd _)
  refine false_of_card_dvd h (a := 10) (b := 6) (m := 65) (by norm_num) (by norm_num) ?_
  calc Nat.card (Outer S) * Nat.card S ∣ 4 * 12130560 := mul_dvd_mul hout4 hcard
    _ = 2 ^ 10 * 3 ^ 6 * 65 := by norm_num

theorem psu4Three_hyp_false {S : Type} [Group S] [Finite S] {p : ℕ} {P : Subgroup (MulAut S)}
    {x u : MulAut S} {V : Subgroup (MulAut S)} (φ : S ≃* projSU 4 3 1)
    (h : KF135Hyp S p P x u V) : False := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hadm : CFSG.Open.StatedLieAdmissible .PSU 4 3 1 :=
    ⟨Nat.prime_three, le_rfl, by norm_num, by simp⟩
  have hS := CFSG.PGLModel.statedClassicalModel_of_mulEquiv_projSU hadm φ
  obtain ⟨hout, -⟩ :=
    CFSG.RankThree.OuterOrder.higher_linear_unitary_outer_order_determinant_bound (Or.inr rfl)
      (by norm_num) Nat.prime_three le_rfl hS
  have hout8 : Nat.card (Outer S) ∣ 8 :=
    hout.trans (by norm_num [CFSG.RankThree.OuterOrder.determinantParameter])
  have hcard : Nat.card S = 3265920 := by
    rw [Nat.card_congr φ.toEquiv]
    exact CFSG.PGLModel.card_projSU_four_three
  refine false_of_card_dvd h (a := 10) (b := 6) (m := 35) (by norm_num) (by norm_num) ?_
  rw [hcard]
  calc Nat.card (Outer S) * 3265920 ∣ 8 * 3265920 := mul_dvd_mul_right hout8 _
    _ = 2 ^ 10 * 3 ^ 6 * 35 := by norm_num

section G2Three


theorem g2Three_hyp_false {S : Type} [Group S] [Finite S] {p : ℕ} {P : Subgroup (MulAut S)}
    {x u : MulAut S} {V : Subgroup (MulAut S)}
    (φ : S ≃* (TauCeti.CFSGIndex.lie g2ThreeIndex).Group) (h : KF135Hyp S p P x u V) :
    False := by
  let q : TauCeti.PrimePower := ⟨3, 1, Nat.prime_three, Nat.one_pos⟩
  obtain ⟨hadm, K, hKf, hKfin, hK, ⟨ψ⟩⟩ :=
    Sec4.Census.chevalleyExceptionalModel_G2_three q g2ThreeIndex.2 rfl rfl
  have hCS : CFSG.Blueprint.ChevalleyExceptionalModel S .G2 3 1 :=
    ⟨hadm, K, hKf, hKfin, hK, ⟨φ.trans ψ⟩⟩
  have hout : Nat.card (Outer S) ∣ 2 :=
    card_outer_dvd_two_of_le
      (CFSG.ClassicalInvolution.Q3.PhilipHall.Frame.TwinPerp.Small.Q3L.card_outer_le_two_g23
        (Or.inr (Or.inl ⟨rfl, by decide, hCS⟩)))
  have hcard : Nat.card S ∣ 4245696 := by
    rw [Nat.card_congr (φ.trans ψ).toEquiv]
    have h1 := Subgroup.card_quotient_dvd_card
      (Subgroup.center ↥(CFSG.Blueprint.Chevalley.adjointGroup .G2 K))
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK, pow_one] at h1
    exact h1.trans (by norm_num [CFSG.Open.ordG2])
  refine false_of_card_dvd h (a := 7) (b := 6) (m := 91) (by norm_num) (by norm_num) ?_
  calc Nat.card (Outer S) * Nat.card S ∣ 2 * 4245696 := mul_dvd_mul hout hcard
    _ = 2 ^ 7 * 3 ^ 6 * 91 := by norm_num

end G2Three

end FamOdd

section Fam9


theorem kF135At_fam9 : KF135At Fam9 := by
  intro S _ _ p P x u V hF h
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  rcases hF with ⟨e, he1, he3, hφ | hφ⟩ | hφ | hφ | hφ
  · obtain ⟨φ⟩ := hφ
    exact (FamOdd.psl3_hyp_false (by norm_num) he1 he3 φ h).elim
  · obtain ⟨φ⟩ := hφ
    exact (FamOdd.psu3_hyp_false (by norm_num) he1 he3 φ h).elim
  · obtain ⟨φ⟩ := hφ
    exact (FamOdd.g2Three_hyp_false φ h).elim
  · obtain ⟨φ⟩ := hφ
    exact (FamOdd.psl4Three_hyp_false φ h).elim
  · obtain ⟨φ⟩ := hφ
    exact (FamOdd.psu4Three_hyp_false φ h).elim

end Fam9

end CFSG.RankThree.PartTwo.Sec13.KF135Proof
