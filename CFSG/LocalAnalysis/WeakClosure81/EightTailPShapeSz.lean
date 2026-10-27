module

import CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.L6LeavesKFactParabolicLeviSubUArith
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LieType.Ree.SuzukiOrder
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
public import CFSG.LocalAnalysis.WeakClosure81.SevenKDefs
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels
public import CFSG.Timmesfeld.Orders.ClassicalLinear

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup
open CFSG.LocalAnalysis.WeakClosure81.SevenK

private theorem wc85sz_not_three_dvd_card_of_isSzGp
    {Y : Type} [Group Y] {n : ℕ} (h : IsSzGp Y n) : ¬ 3 ∣ Nat.card Y := by
  obtain ⟨-, a, -, K, _, _, hn, hK, ⟨e⟩⟩ := h
  subst hn
  rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK]
  have hq3' : 2 ^ (2 * a + 1) % 3 = 2 := by
    rw [pow_succ, pow_mul, Nat.mul_mod, Nat.pow_mod]
    norm_num
  set q := 2 ^ (2 * a + 1)
  have hq3 : q % 3 = 2 := hq3'
  have hsq : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq3]
  intro h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h3 with h | h
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).1 h with h' | h'
    · have := Nat.mod_eq_zero_of_dvd h'
      omega
    · have := Nat.mod_eq_zero_of_dvd h'
      omega
  · have := Nat.mod_eq_zero_of_dvd h
    omega

private theorem wc85sz_three_dvd_card_of_isSpGp {Y : Type} [Group Y] {m n : ℕ}
    (hm : 3 < m) (h : IsSpGp Y m n) : 3 ∣ Nat.card Y := by
  obtain ⟨k, hk, F, hFld, hFin, hFcard, ⟨e⟩⟩ := h
  have hk2 : 2 ≤ k := by omega
  rw [Nat.card_congr e.toEquiv,
    @CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp F hFld hFin k, hFcard]
  have h3 : 3 ∣ (2 ^ n) ^ 2 - 1 := by
    have h : (2 ^ n) ^ 2 = 4 ^ n := by
      rw [← pow_mul, mul_comm, pow_mul]
      norm_num
    rw [h]
    have h2 := Nat.sub_one_dvd_pow_sub_one 4 n
    norm_num at h2
    exact h2
  have hmem : 1 ∈ Finset.Icc 1 k := Finset.mem_Icc.2 ⟨le_rfl, by omega⟩
  have hdvd : ((2 ^ n) ^ (2 * 1) - 1) ∣
      ∏ j ∈ Finset.Icc 1 k, ((2 ^ n) ^ (2 * j) - 1) :=
    Finset.dvd_prod_of_mem _ hmem
  have h3' : 3 ∣ (2 ^ n) ^ (2 * 1) - 1 := by simpa using h3
  have hprod : 3 ∣ ∏ j ∈ Finset.Icc 1 k, ((2 ^ n) ^ (2 * j) - 1) := h3'.trans hdvd
  exact dvd_mul_of_dvd_right hprod _

private theorem wc85sz_three_dvd_card_of_isPSUGp {Y : Type} [Group Y] {m n : ℕ}
    (hm : 3 < m) (h : IsPSUGp Y m n) : 3 ∣ Nat.card Y := by
  obtain ⟨-, hf, -, -⟩ := CFSG.Blueprint.LieModel.admissible h
  obtain ⟨⟨-, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega) h
  have hY : Nat.card Y = ordTwistedA (m - 1) (2 ^ n) := by
    rw [Nat.card_congr e.toEquiv,
      CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hf hK
        (by omega : 2 ≤ m),
      ordTwistedA, Nat.sub_add_cancel (by omega : 1 ≤ m), mul_comm (m - 1) m]
  rw [hY]
  exact CFSG.LocalAnalysis.RankFourTheoremC.PEmpty.KPLeviSub.three_dvd_ordTwistedA hf
    (by omega : 2 ≤ m)

theorem not_isSpGp_or_isPSUGp_of_isSzGp {Y : Type} [Group Y]
    {n : ℕ} (h : IsSzGp Y n) : ¬ ∃ m n' : ℕ, 3 < m ∧ (IsSpGp Y m n' ∨ IsPSUGp Y m n') := by
  rintro ⟨m, n', hm, hsp | hpsu⟩
  · exact wc85sz_not_three_dvd_card_of_isSzGp h (wc85sz_three_dvd_card_of_isSpGp hm hsp)
  · exact wc85sz_not_three_dvd_card_of_isSzGp h (wc85sz_three_dvd_card_of_isPSUGp hm hpsu)

end CFSG.LocalAnalysis.WeakClosure81

end
