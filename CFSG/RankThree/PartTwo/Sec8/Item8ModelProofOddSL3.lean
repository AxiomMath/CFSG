module

public import CFSG.RankThree.PartTwo.Sec8.Item8KFactsProofOddSL3
import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofOrders
public import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofOddArith
import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofOddModels
import CFSG.RankThree.PartTwo.Sec4.Census.Interface46
import CFSG.Timmesfeld.Orders.ExceptionalUntwisted
import CFSG.Timmesfeld.Orders.ExceptionalTwisted
import CFSG.RankThree.SteinbergR3ELargeReeOrder
import CFSG.RankThree.PartTwo.Census.Suzuki
public import CFSG.RankThree.PartTwo.Sec4.Item47Bridges

public section

namespace CFSG.RankThree.PartTwo.Sec8

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.KFacts CFSG.RankThree.PartTwo.Sec4
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Assembly.LowTwoRank
open CFSG.Open (ordG2 ordTrialityD4 ordSuzuki ordTwistedF4)
open Matrix

namespace Item8ModelProof

theorem prod_Icc_two_three (q : ℕ) :
    ∏ j ∈ Finset.Icc 2 3, (q ^ j - 1) = (q ^ 2 - 1) * (q ^ 3 - 1) := by
  rw [show Finset.Icc 2 3 = {2, 3} from rfl, Finset.prod_pair (by norm_num)]

theorem prod_Icc_two_four (q : ℕ) :
    ∏ j ∈ Finset.Icc 2 4, (q ^ j - 1) = (q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1) := by
  rw [show Finset.Icc 2 4 = {2, 3, 4} from rfl, Finset.prod_insert (by decide),
    Finset.prod_pair (by norm_num)]
  ring

theorem eq_one_or_three_of_dvd {d : ℕ} (h : d ∣ 3) : d = 1 ∨ d = 3 :=
  (Nat.dvd_prime Nat.prime_three).mp h

theorem l3Data_of {X : Type} [Group X] {p e : ℕ} [Fact p.Prime] (hp3 : 3 < p) (he1 : 1 ≤ e)
    (he2 : e ≤ 2) (hX : IsSLThreePiAt X (p ^ e) ∨ IsoLThreePi X p e) :
    L3Data (Nat.card X) p e := by
  have hp : p.Prime := Fact.out
  have hp4 : p ≠ 4 := by
    rintro rfl
    exact absurd hp (by decide)
  refine ⟨hp, by omega, he1, he2, ?_⟩
  rcases hX with ⟨K, _, _, ⟨hK, -, ⟨eX⟩⟩ | ⟨hK, -, ⟨eX⟩⟩⟩ | ⟨-, ⟨eX⟩⟩ | ⟨-, ⟨eX⟩⟩
  · refine ⟨1, _, Or.inl rfl, Or.inl rfl, ?_⟩
    rw [mul_one, Nat.card_congr eX.toEquiv, CFSG.SectionRank.OddCover.card_statedSL_three, hK,
      mul_assoc]
  · have : Fintype K := Fintype.ofFinite K
    have : CharP K p := charP_of_card_eq_prime_pow (f := e * 2)
      (by rw [← Nat.card_eq_fintype_card, hK, ← pow_mul])
    refine ⟨1, _, Or.inl rfl, Or.inr rfl, ?_⟩
    rw [mul_one, Nat.card_congr eX.toEquiv, CFSG.SectionRank.OddCover.card_statedSU_three hK,
      mul_assoc]
  · have hc := card_psl_mul_gcd (K := GaloisField p e) (n := 3) (by norm_num)
    rw [GaloisField.card p e (by omega), show 3 * (3 - 1) / 2 = 3 by norm_num,
      prod_Icc_two_three] at hc
    refine ⟨Nat.gcd (p ^ e - 1) 3, _, eq_one_or_three_of_dvd (Nat.gcd_dvd_right _ _), Or.inl rfl,
      ?_⟩
    rw [Nat.card_congr (eX.trans (projSLEquivPSLn 3 _)).toEquiv, hc]
  · have h₀ : UnitaryFieldData p e (GaloisField p (2 * e)) :=
      ⟨hp, he1, GaloisField.card p _ (by omega)⟩
    have hc := card_unitaryPSU_three_mul_gcd h₀
    refine ⟨Nat.gcd 3 (p ^ e + 1), _, eq_one_or_three_of_dvd (Nat.gcd_dvd_left _ _), Or.inr rfl,
      ?_⟩
    rw [Nat.card_congr (eX.trans ((Census.statedSUEquivProjSU 3 p e).symm.trans
      (unitaryPSUEquiv h₀ (by norm_num)).symm)).toEquiv, hc, mul_assoc]

theorem dims_cases {m f e : ℕ} (hm : 3 ≤ m) (hf : 1 ≤ f) (he2 : e ≤ 2)
    (ha : f * (m * (m - 1) / 2) = 3 * e) : (m = 3 ∧ f = e) ∨ (m = 4 ∧ f = 1 ∧ e = 2) := by
  set T := m * (m - 1) / 2 with hT
  have h2T : 2 * T = m * (m - 1) := Nat.mul_div_cancel' (Nat.even_mul_pred_self m).two_dvd
  have hT6 : T ≤ 6 := by nlinarith
  have hm4 : m ≤ 4 := by
    by_contra h
    have : 5 * 4 ≤ m * (m - 1) := Nat.mul_le_mul (by omega) (by omega)
    omega
  rcases (by omega : m = 3 ∨ m = 4) with rfl | rfl
  · left
    have : T = 3 := by omega
    exact ⟨rfl, by rw [this] at ha; omega⟩
  · right
    have : T = 6 := by omega
    rw [this] at ha
    exact ⟨rfl, by omega, by omega⟩

end Item8ModelProof

open Item8ModelProof


theorem kF82OddSL3Model_holds : KF82OddSL3Model := by
  intro G _ _ L x p e _ k hp3 he1 he2 hX hx
  have hL := l3Data_of hp3 he1 he2 hX
  have hM : ∀ {M : Type} [Group M], (L ⧸ aschbacherSolvableCore 3 L ≃* M) →
      L3Data (Nat.card M) p e := fun e' => (Nat.card_congr e'.toEquiv) ▸ hL
  cases hx with
  | psl2 K h =>
    obtain ⟨e', -⟩ := h
    have hc := card_psl_mul_gcd (K := K) (n := 2) (by norm_num)
    rw [show 2 * (2 - 1) / 2 = 1 by norm_num, show Finset.Icc 2 2 = {2} from rfl,
      Finset.prod_singleton, pow_one] at hc
    exact ((hM e').false_of_psl2 Finite.one_lt_card (Nat.gcd_le_right _ (by norm_num)) hc).elim
  | psl m K hm h =>
    obtain ⟨e', -⟩ := id h
    obtain ⟨ℓ, f, hℓ, hf, hK, -⟩ := exists_card_prime_pow K
    obtain ⟨hℓp, ha⟩ := (hM e').eq_of_modelPart (modelPart_projectiveSL hm hℓ hf hK)
    subst ℓ
    rcases dims_cases hm hf he2 ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Or.inl ⟨K, inferInstance, inferInstance, hK, Or.inl h⟩
    · exfalso
      have hlt := (hM e').sl4_lt rfl
      have hSL := LinearFlag.card_SL_eq (K := K) (n := 4) (by norm_num)
      rw [hK, pow_one, show 4 * (4 - 1) / 2 = 6 by norm_num, prod_Icc_two_four] at hSL
      have hle : Nat.card (LinearFlag.projectiveSL 4 K) ≤
          Nat.card (SpecialLinearGroup (Fin 4) K) := by
        rw [(LinearFlag.scalars 4 K).card_eq_card_quotient_mul_card_subgroup]
        exact Nat.le_mul_of_pos_right _ Nat.card_pos
      omega
  | sl m K hm h =>
    obtain ⟨e', -, -⟩ := id h
    obtain ⟨ℓ, f, hℓ, hf, hK, -⟩ := exists_card_prime_pow K
    obtain ⟨hℓp, ha⟩ := (hM e').eq_of_modelPart (modelPart_SL hm hℓ hf hK)
    subst ℓ
    rcases dims_cases hm hf he2 ha with ⟨rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact Or.inl ⟨K, inferInstance, inferInstance, hK, Or.inr h⟩
    · exfalso
      have hlt := (hM e').sl4_lt rfl
      have hSL := LinearFlag.card_SL_eq (K := K) (n := 4) (by norm_num)
      rw [hK, pow_one, show 4 * (4 - 1) / 2 = 6 by norm_num, prod_Icc_two_four] at hSL
      omega
  | @psu3 p' f K _ hK hq h =>
    obtain ⟨e', -⟩ := id h
    obtain ⟨hℓp, ha⟩ := (hM e').eq_of_modelPart (modelPart_unitaryPSU hK)
    subst p'
    obtain rfl : f = e := by omega
    exact Or.inr ⟨K, inferInstance, hK, hq, Or.inl h⟩
  | @su3 p' f K _ hK hq h =>
    obtain ⟨e', -, -⟩ := id h
    obtain ⟨hℓp, ha⟩ := (hM e').eq_of_modelPart (modelPart_unitarySU hK)
    subst p'
    obtain rfl : f = e := by omega
    exact Or.inr ⟨K, inferInstance, hK, hq, Or.inr h⟩
  | psp r K hr h =>
    obtain ⟨e', -⟩ := h
    obtain ⟨ℓ, f, hℓ, hf, hK, hchar⟩ := exists_card_prime_pow K
    have hr2 : 2 ≤ r := by rcases hr with hr | ⟨rfl, -⟩ <;> omega
    obtain ⟨-, ha⟩ := (hM e').eq_of_modelPart (modelPart_statedSp hr2 hℓ hf hK hchar)
    exfalso
    rcases (by omega : r = 2 ∨ 3 ≤ r) with rfl | hr3
    · omega
    · have : 9 ≤ r ^ 2 := by nlinarith
      have : 9 ≤ f * r ^ 2 := le_trans this (Nat.le_mul_of_pos_left _ (by omega))
      omega
  | psp4even F h =>
    obtain ⟨e', -⟩ := h
    obtain ⟨ℓ, f, hℓ, hf, hK, hchar⟩ := exists_card_prime_pow F
    obtain ⟨hℓp, -⟩ := (hM e').eq_of_modelPart (modelPart_statedSp le_rfl hℓ hf hK hchar)
    have h2 : ringChar F = 2 := ringChar.eq F 2
    omega
  | g2 K hK3 hK4 h =>
    obtain ⟨e', -⟩ := h
    obtain ⟨ℓ, f, hℓ, hf, hK, -⟩ := exists_card_prime_pow K
    have hL' := hM e'
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2, hK] at hL'
    obtain ⟨hℓp, ha⟩ := hL'.eq_of_modelPart (modelPart_ordG2 hℓ hf)
    subst ℓ
    obtain rfl : e = 2 := by omega
    obtain rfl : f = 1 := by omega
    have hlt := hL'.g2_lt rfl
    rw [pow_one, ordG2, mul_assoc] at hlt
    exact (lt_irrefl _ hlt).elim
  | sz a K ha hK h =>
    obtain ⟨e', -⟩ := h
    have : Finite K := Nat.finite_of_card_ne_zero (by rw [hK]; positivity)
    have hL' := hM e'
    rw [Nat.card_congr
        (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK).toEquiv,
      CFSG.RankThree.PartTwo.Census.card_suzukiMatrixGroup (by omega), suzuki_eq_ordSuzuki]
      at hL'
    obtain ⟨hp2, -⟩ := hL'.eq_of_modelPart (modelPart_ordSuzuki (f := 2 * a + 1) (by omega))
    omega
  | triality f hf K hK σ hσ h =>
    obtain ⟨e', -, -⟩ := h
    have hL' := hM e'
    rw [CFSG.Timmesfeld.ExceptionalOrders.card_graphFixedRootGroup_D4_two hf hK σ.toRingHom
      hσ] at hL'
    obtain ⟨hp2, -⟩ := hL'.eq_of_modelPart (modelPart_ordTrialityD4 hf)
    omega
  | largeRee a ha K hK h =>
    obtain ⟨e', -⟩ := h
    have hL' := hM e'
    rw [(CFSG.RankThree.LargeReeOrder.large_Ree_exact_native_order_and_prime_factor_exhaustion
      a K hK).1, ree_native_eq_ordTwistedF4 Nat.one_le_two_pow] at hL'
    obtain ⟨hp2, -⟩ := hL'.eq_of_modelPart (modelPart_ordTwistedF4 (f := 2 * a + 1) (by omega))
    omega

theorem kF82OddSLThree_holds : KF82OddSLThree :=
  kF82OddSLThree_of kF82OddSL3Model_holds

end CFSG.RankThree.PartTwo.Sec8
