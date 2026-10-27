module

public import CFSG.Quasithin.Background.GoldschmidtS146RArith2
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
import CFSG.Adapters.StatedClassicalSmallOrders

public section

namespace CFSG.Quasithin.S146zX

open CFSG.Quasithin CFSG.Assembly.LowTwoRank

theorem card_isPSL_two_even {n : ℕ} {X : Type} [Group X] (h : IsPSL 2 2 n X) :
    Nat.card X = 2 ^ n * ((2 ^ n) ^ 2 - 1) := by
  have hn : 1 ≤ n := h.1.2.1
  have hodd : Odd (2 ^ n - 1) := by
    have h1 := CFSG.Quasithin.GoldS146R.odd_two_pow_pow_sub_one' (n := n) (k := 1) hn le_rfl
    simpa using h1
  have hg : Nat.gcd 2 (2 ^ n - 1) = 1 := Nat.coprime_two_left.mpr hodd
  rw [CFSG.Quasithin.GoldS146R.card_of_isPSL h, show 2 - 1 = 1 from rfl,
    CFSG.Quasithin.GoldS146R.ordA_one_eq, hg, Nat.div_one]

theorem two_mul_card_isPSL_two_odd {q : ℕ} (hq : Odd q) {X : Type} [Group X]
    (h : IsPSL 2 q 1 X) : 2 * Nat.card X = q * (q ^ 2 - 1) := by
  obtain ⟨m, hm⟩ := hq
  have hg : Nat.gcd 2 (q - 1) = 2 := by
    rw [hm, Nat.add_sub_cancel]
    exact Nat.gcd_eq_left (dvd_mul_right 2 m)
  have h2 : 2 ∣ q ^ 2 - 1 := by
    have h1 := Nat.sq_sub_sq q 1
    rw [one_pow] at h1
    rw [h1, hm, Nat.add_sub_cancel]
    exact Dvd.dvd.mul_left (dvd_mul_right 2 m) _
  rw [CFSG.Quasithin.GoldS146R.card_of_isPSL h, show 2 - 1 = 1 from rfl, pow_one,
    CFSG.Quasithin.GoldS146R.ordA_one_eq, hg]
  exact Nat.mul_div_cancel' (Dvd.dvd.mul_left h2 q)

theorem three_dvd_mul_sq_sub_one (q : ℕ) : 3 ∣ q * (q ^ 2 - 1) := by
  have h3 : q % 3 = 0 ∨ q % 3 = 1 ∨ q % 3 = 2 := by omega
  rcases h3 with h | h | h
  · exact Dvd.dvd.mul_right (Nat.dvd_of_mod_eq_zero h) _
  · refine Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero ?_) _
    have : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h]
    omega
  · refine Dvd.dvd.mul_left (Nat.dvd_of_mod_eq_zero ?_) _
    have : q ^ 2 % 3 = 1 := by rw [Nat.pow_mod, h]
    omega

theorem three_dvd_card_isPSL_two_odd {q : ℕ} (hq : Odd q) {X : Type} [Group X]
    (h : IsPSL 2 q 1 X) : 3 ∣ Nat.card X := by
  have h1 := two_mul_card_isPSL_two_odd hq h
  have h2 : 3 ∣ 2 * Nat.card X := by rw [h1]; exact three_dvd_mul_sq_sub_one q
  exact (Nat.Coprime.dvd_of_dvd_mul_left (by norm_num : Nat.Coprime 3 2) h2)

theorem card_isSz {n : ℕ} {X : Type} [Group X] (h : IsSz n X) :
    ∃ a : ℕ, 1 ≤ a ∧ n = 2 * a + 1 ∧
      Nat.card X = ((2 ^ n) ^ 2 + 1) * (2 ^ n) ^ 2 * (2 ^ n - 1) := by
  obtain ⟨-, a, ha, K, hF, hfin, hn, hK, ⟨e⟩⟩ := h
  refine ⟨a, ha, hn, ?_⟩
  have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [hK, hn]
  rw [Nat.card_congr (e.trans
      (CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK')).toEquiv,
    CFSG.SectionRank.card_suzukiMatrixGroup a (by omega), hn]

theorem not_three_dvd_sz_order (a : ℕ) :
    ¬ 3 ∣ ((2 ^ (2 * a + 1)) ^ 2 + 1) * (2 ^ (2 * a + 1)) ^ 2 * (2 ^ (2 * a + 1) - 1) := by
  have h4 : 4 ^ a % 3 = 1 := by rw [Nat.pow_mod]; norm_num
  have hq : 2 ^ (2 * a + 1) = 2 * 4 ^ a := by
    rw [pow_succ, pow_mul]; norm_num; ring
  set t := 4 ^ a with ht
  have h1 : 1 ≤ t := Nat.one_le_pow _ _ (by norm_num)
  rw [hq]
  have hq3 : (2 * t) % 3 = 2 := by omega
  have hsq : (2 * t) ^ 2 % 3 = 1 := by rw [Nat.pow_mod, hq3]
  intro h
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h with h' | h'
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h' with h'' | h''
    · omega
    · omega
  · omega

theorem not_three_dvd_card_isSz {n : ℕ} {X : Type} [Group X] (h : IsSz n X) :
    ¬ 3 ∣ Nat.card X := by
  obtain ⟨a, -, hn, hcard⟩ := card_isSz h
  rw [hcard, hn]
  exact not_three_dvd_sz_order a

theorem card_isAlt_five {X : Type} [Group X] (h : IsAlt 5 X) : Nat.card X = 60 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem card_isAlt_seven {X : Type} [Group X] (h : IsAlt 7 X) : Nat.card X = 2520 := by
  obtain ⟨e⟩ := h
  rw [Nat.card_congr e.toEquiv, Nat.card_eq_fintype_card, card_alternatingGroup]
  simp [Nat.factorial]

theorem card_isPSL_three_two {X : Type} [Group X] (h : IsPSL 3 2 1 X) : Nat.card X = 168 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_two h

theorem card_isPSL_four_two {X : Type} [Group X] (h : IsPSL 4 2 1 X) : Nat.card X = 20160 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_four_two h

theorem card_isPSL_five_two {X : Type} [Group X] (h : IsPSL 5 2 1 X) : Nat.card X = 9999360 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_five_two h

theorem card_isPSL_three_five {X : Type} [Group X] (h : IsPSL 3 5 1 X) : Nat.card X = 372000 :=
  CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_three_five h

theorem card_eq_of_mulEquiv_statedSL_three {X : Type} [Group X] {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = 5) (e : X ≃* ↥(StatedSL 3 K)) : Nat.card X = 372000 := by
  rw [Nat.card_congr (e.trans (specialLinearGroupEquivStatedSL 3 K).symm).toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.LinearFlag.card_SL_eq (by norm_num), hK]
  decide

theorem card_dvd_factorial_of_isSporadic_M22 {X : Type} [Group X]
    (h : IsSporadic TauCeti.SporadicName.M22 X) : Nat.card X ∣ Nat.factorial 22 := by
  obtain ⟨e⟩ := h
  have h1 : Nat.card X = Nat.card ↥CFSG.Blueprint.NativeSporadic.M22 :=
    Nat.card_congr e.toEquiv
  have h2 := Subgroup.card_subgroup_dvd_card CFSG.Blueprint.NativeSporadic.M22
  rw [Nat.card_perm, Nat.card_fin] at h2
  rw [h1]
  exact h2

end CFSG.Quasithin.S146zX
