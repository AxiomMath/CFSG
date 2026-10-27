module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section21.StatementsEleven
public import CFSG.LocalAnalysis.StandardType.GGRecipeFieldSpUSp
public import CFSG.RankThree.PartTwo.KFacts.AutPSp4FieldFixed
public import CFSG.RankThree.PartTwo.KFacts.AutPSUFieldFixed

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

private theorem apply_symm_fixed_of_congr_fixed {X P : Type*} [Group X] [Group P] (e : X ≃* P)
    (θ : MulAut X) {y : P} (hy : MulAut.congr e θ y = y) : θ (e.symm y) = e.symm y := by
  apply e.injective
  calc e (θ (e.symm y)) = MulAut.congr e θ y := rfl
    _ = y := hy
    _ = e (e.symm y) := (MulEquiv.apply_symm_apply e y).symm

section Sp4

open CFSG.LocalAnalysis.ComponentInitial.SymplecticHigher
open CFSG.RankThree.PartTwo.KFacts (IsInnerAut isInnerAut_congr conjAut_mem_inner_of_charTwo
  exists_orderOf_three_fieldAut_fixed)

private theorem conjAut_mul_fieldAut_mul_inv_apply {K : Type} [Field K] (H : gsp 2 K)
    (σ : K ≃+* K) {x : StatedProj (StatedSp 2 K)}
    (hx : fieldAut 2 K σ x = x) :
    (conjAut 2 K H * fieldAut 2 K σ * (conjAut 2 K H)⁻¹) (conjAut 2 K H x) =
      conjAut 2 K H x := by
  simp only [MulAut.mul_apply]
  rw [MulAut.inv_apply_self, hx]

theorem kFieldCent_sp4 :
    ∀ (X : Type) [Group X] [Finite X] (a r : ℕ), IsSp4 X a → r.Prime → r ≠ 2 →
      ∀ θ : MulAut X, orderOf θ = r → θ ∉ (MulAut.conj : X →* MulAut X).range →
        r ∣ a ∧ ∃ x : X, orderOf x = 3 ∧ θ x = x := by
  intro X _ _ a r hX hr hr2 θ hθ hθN
  obtain ⟨⟨-, -, -⟩, K, hField, hFin, hK, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  letI : Field K := hField
  letI : Finite K := hFin
  haveI : Fintype K := Fintype.ofFinite K
  haveI : CharP K 2 := by
    haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
    exact charP_of_card_eq_prime_pow (p := 2) (f := a)
      (by rw [← Nat.card_eq_fintype_card, hK])
  have hθr : θ ^ r = 1 := by rw [← hθ]; exact pow_orderOf_eq_one θ
  let α : MulAut (StatedProj (StatedSp 2 K)) := MulAut.congr e θ
  have hαp : α ^ r = 1 := by
    rw [show α = MulAut.congr e θ from rfl, ← map_pow, hθr, map_one]
  have hodd : Odd r := hr.odd_of_ne_two hr2
  obtain ⟨A, σ, hAσ⟩ := (mem_spSemilinearAutGroup_iff (r := 2) (K := K)).1
    (CFSG.RankThree.PartOne.CTP.mem_spSemilinearAutGroup_of_odd_pow hodd hαp)
  have hσ1 : σ ≠ 1 := by
    intro hσ
    apply hθN
    have hαin : IsInnerAut α := by
      rw [hAσ, hσ, map_one, mul_one]
      exact conjAut_mem_inner_of_charTwo A
    exact (isInnerAut_congr e θ).1 hαin
  have hAσpow : (conjAut 2 K A * fieldAut 2 K σ) ^ r = 1 := by
    rw [← hAσ]
    exact hαp
  obtain ⟨hσord, H, hH⟩ :=
    CFSG.StandardType.RecipeFieldSpU.conjAut_mul_fieldAut_of_pow_eq_one
      (r := 2) (K := K) (by norm_num) hr A σ hσ1 hAσpow
  have hdvd : r ∣ a := by
    have hcard := (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic
      Nat.prime_two K hK).1
    rw [← hσord, ← hcard]
    exact orderOf_dvd_natCard σ
  obtain ⟨x₀, hx₀ord, hx₀fix⟩ := exists_orderOf_three_fieldAut_fixed K σ
  refine ⟨hdvd, e.symm (conjAut 2 K H x₀), ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq e.symm, MulEquiv.orderOf_eq (conjAut 2 K H), hx₀ord]
  · refine apply_symm_fixed_of_congr_fixed e θ ?_
    rw [show MulAut.congr e θ = α from rfl, hAσ, hH]
    exact conjAut_mul_fieldAut_mul_inv_apply H σ hx₀fix

end Sp4

section U3

open CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
open CFSG.RankThree.PartTwo.KFacts

theorem kFieldCent_u3 :
    ∀ (X : Type) [Group X] [Finite X] (a r : ℕ), IsU3 X a → r.Prime → r ≠ 2 →
      ∀ θ : MulAut X, orderOf θ = r → θ ∉ CFSG.ASVolI.ChA.innDiagSubgroup X →
        r ∣ a ∧ ∃ x : X, orderOf x = 3 ∧ θ x = x := by
  intro X _ _ a r hX hr hr2 θ hθ hinn
  obtain ⟨⟨-, ha1, -, hne⟩, K, _, _, hKcard, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel hX (by decide)
  have hU : UnitaryFieldData 2 a K :=
    ⟨Nat.prime_two, ha1, by rw [hKcard, ← pow_mul, mul_comm]⟩
  haveI : Finite K := hU.finite
  have h2a : 2 ^ a ≠ 2 := fun h => hne (by rw [h])
  have ha2 : 2 ≤ a := by
    rcases Nat.lt_or_ge a 2 with h | h
    · have h1 : a = 1 := by omega
      exact absurd (by rw [h1, pow_one]) h2a
    · exact h
  have hq : 2 < 2 ^ a :=
    calc 2 < 2 ^ 2 := by norm_num
      _ ≤ 2 ^ a := Nat.pow_le_pow_right (by norm_num) ha2
  let e' : X ≃* unitaryPSU hU 3 :=
    e.trans (unitaryPSUEquiv hU (by norm_num : 1 ≤ 3)).symm
  have hodd : Odd (orderOf θ) := by rw [hθ]; exact hr.odd_of_ne_two hr2
  have hout : MulAut.congr e' θ ∉ (psuConj hU).range :=
    not_mem_range_psuConj_of_not_mem_innDiagSubgroup hU e' hinn
  obtain ⟨A, σ, hAσ, hσ1, -⟩ := exists_psuConj_mul_psuField_prime hU hq e' θ hodd hout
  have hα : (psuConj hU A * psuField hU σ) ^ r = 1 := by
    rw [← hAσ, ← map_pow, ← hθ, pow_orderOf_eq_one, map_one]
  obtain ⟨hσord, H, hH⟩ :=
    exists_psuConj_conj_psuField_of_prime hU hq A σ hr hr2 hσ1 hα
  have hcard : Nat.card K = 2 ^ (2 * a) := by rw [hKcard, ← pow_mul, mul_comm]
  have hAut : Nat.card (RingAut K) = 2 * a :=
    (CFSG.LocalAnalysis.ComponentInitial.card_ringAut_and_isCyclic Nat.prime_two K hcard).1
  have hdvd : r ∣ a := by
    have h1 : r ∣ 2 * a := by
      rw [← hAut, ← hσord]
      exact orderOf_dvd_natCard σ
    rcases (hr.dvd_mul).mp h1 with h2 | h2
    · rcases (Nat.dvd_prime Nat.prime_two).1 h2 with h3 | h3
      · exact absurd h3 hr.ne_one
      · exact absurd h3 hr2
    · exact h2
  obtain ⟨x₀, hx₀ord, hx₀fix⟩ := exists_orderOf_three_psuField_fixed hU σ
  refine ⟨hdvd, e'.symm (psuConj hU H x₀), ?_, ?_⟩
  · rw [MulEquiv.orderOf_eq e'.symm, MulEquiv.orderOf_eq (psuConj hU H), hx₀ord]
  · refine apply_symm_fixed_of_congr_fixed e' θ ?_
    rw [hAσ, hH, MulAut.mul_apply, MulAut.mul_apply, MulAut.inv_apply_self, hx₀fix]

end U3

theorem kFieldCent_holds : KFieldCent :=
  ⟨kFieldCent_sp4, kFieldCent_u3⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
