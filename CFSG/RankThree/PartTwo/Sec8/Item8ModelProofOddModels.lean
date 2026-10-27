module

public import CFSG.RankThree.PartTwo.Sec8.Item8ModelProofOddArith
public import CFSG.RankThree.PartTwo.KFacts.K71OddChar
import CFSG.RankThree.PartTwo.KFacts.K71IdentSU3
import CFSG.RankThree.PartTwo.KFacts.K71OddCharArith
import CFSG.ClassicalInvolution.Orders.Symplectic
import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8ModelProof

open CFSG CFSG.RankThree.PartTwo.KFacts CFSG.ClassicalGroups.UnitaryFlag
open CFSG.LocalAnalysis.ComponentInitial CFSG.Assembly.LowTwoRank
open CFSG.Open (ordG2 ordTrialityD4 ordSuzuki ordTwistedF4)
open Matrix

theorem exists_card_prime_pow (K : Type*) [Field K] [Finite K] :
    ∃ ℓ f : ℕ, ℓ.Prime ∧ 1 ≤ f ∧ Nat.card K = ℓ ^ f ∧ ringChar K = ℓ := by
  have := Fintype.ofFinite K
  obtain ⟨ℓ, hc, n, hℓ, hn⟩ := FiniteField.card' K
  exact ⟨ℓ, n, hℓ, n.pos, by rw [Nat.card_eq_fintype_card, hn], ringChar.eq K ℓ⟩

theorem not_dvd_prod_sub_one {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) {s : Finset ℕ} {g : ℕ → ℕ}
    (hg : ∀ j ∈ s, 1 ≤ g j) : ¬ ℓ ∣ ∏ j ∈ s, ((ℓ ^ f) ^ g j - 1) := by
  rw [(Nat.Prime.prime hℓ).dvd_finsetProd_iff]
  rintro ⟨j, hj, h⟩
  exact not_dvd_pow_pow_sub_one hℓ hf (hg j hj) h

theorem su3Order_lt {q : ℕ} (hq : 2 ≤ q) : q ^ 3 * (q ^ 2 - 1) * (q ^ 3 + 1) < q ^ 8 := by
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 2 := ⟨q - 2, by omega⟩
  have h1 : 1 ≤ (t + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  zify [h1]
  have : (0 : ℤ) < ((t : ℤ) + 2) ^ 8 -
      ((t : ℤ) + 2) ^ 3 * (((t : ℤ) + 2) ^ 2 - 1) * (((t : ℤ) + 2) ^ 3 + 1) := by
    ring_nf
    positivity
  linarith

theorem ordG2_lt {q : ℕ} (hq : 2 ≤ q) : ordG2 q < q ^ 14 := by
  rw [ordG2]
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 2 := ⟨q - 2, by omega⟩
  have h1 : 1 ≤ (t + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ (t + 2) ^ 6 := Nat.one_le_pow _ _ (by omega)
  zify [h1, h6]
  have : (0 : ℤ) < ((t : ℤ) + 2) ^ 14 -
      ((t : ℤ) + 2) ^ 6 * (((t : ℤ) + 2) ^ 6 - 1) * (((t : ℤ) + 2) ^ 2 - 1) := by
    ring_nf
    positivity
  linarith

theorem ordSuzuki_lt {q : ℕ} (hq : 2 ≤ q) : ordSuzuki q < q ^ 5 := by
  rw [ordSuzuki]
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 2 := ⟨q - 2, by omega⟩
  zify [(by omega : 1 ≤ t + 2)]
  have : (0 : ℤ) < ((t : ℤ) + 2) ^ 5 -
      ((t : ℤ) + 2) ^ 2 * (((t : ℤ) + 2) ^ 2 + 1) * (((t : ℤ) + 2) - 1) := by
    ring_nf
    positivity
  linarith

theorem ordTrialityD4_lt {q : ℕ} (hq : 2 ≤ q) : ordTrialityD4 q < q ^ 29 := by
  rw [ordTrialityD4]
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 2 := ⟨q - 2, by omega⟩
  have h2 : 1 ≤ (t + 2) ^ 2 := Nat.one_le_pow _ _ (by omega)
  have h6 : 1 ≤ (t + 2) ^ 6 := Nat.one_le_pow _ _ (by omega)
  zify [h2, h6]
  have : (0 : ℤ) < ((t : ℤ) + 2) ^ 29 - ((t : ℤ) + 2) ^ 12 *
      (((t : ℤ) + 2) ^ 8 + ((t : ℤ) + 2) ^ 4 + 1) * (((t : ℤ) + 2) ^ 6 - 1) *
      (((t : ℤ) + 2) ^ 2 - 1) := by
    ring_nf
    positivity
  linarith

theorem ordTwistedF4_lt {q : ℕ} (hq : 2 ≤ q) : ordTwistedF4 q < q ^ 28 := by
  rw [ordTwistedF4]
  obtain ⟨t, rfl⟩ : ∃ t, q = t + 2 := ⟨q - 2, by omega⟩
  have h4 : 1 ≤ (t + 2) ^ 4 := Nat.one_le_pow _ _ (by omega)
  zify [h4, (by omega : 1 ≤ t + 2)]
  have : (0 : ℤ) < ((t : ℤ) + 2) ^ 28 - ((t : ℤ) + 2) ^ 12 * (((t : ℤ) + 2) ^ 6 + 1) *
      (((t : ℤ) + 2) ^ 4 - 1) * (((t : ℤ) + 2) ^ 3 + 1) * (((t : ℤ) + 2) - 1) := by
    ring_nf
    positivity
  linarith

theorem spOrd_le (q r : ℕ) :
    q ^ (r ^ 2) * ∏ j ∈ Finset.Icc 1 r, (q ^ (2 * j) - 1) ≤ q ^ (2 * r ^ 2 + r) := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [CFSG.RankThree.PartTwo.KFacts.OddChar.spOrd_succ]
    calc q ^ (r ^ 2) * (∏ j ∈ Finset.Icc 1 r, (q ^ (2 * j) - 1)) *
          (q ^ (2 * (r + 1) - 1) * (q ^ (2 * (r + 1)) - 1))
        ≤ q ^ (2 * r ^ 2 + r) * (q ^ (2 * (r + 1) - 1) * q ^ (2 * (r + 1))) :=
          Nat.mul_le_mul ih (Nat.mul_le_mul_left _ (Nat.sub_le _ _))
      _ = q ^ (2 * (r + 1) ^ 2 + (r + 1)) := by
          rw [← pow_add, ← pow_add]
          congr 1
          rw [show 2 * (r + 1) - 1 = 2 * r + 1 by omega]
          ring

theorem cube_lt_of_le {N q a b : ℕ} (hq : 2 ≤ q) (hN : N ≤ q ^ b) (hab : 3 * b < 8 * a) :
    N ^ 3 < q ^ (8 * a) :=
  calc N ^ 3 ≤ (q ^ b) ^ 3 := Nat.pow_le_pow_left hN 3
    _ = q ^ (3 * b) := by rw [← pow_mul, mul_comm]
    _ < q ^ (8 * a) := Nat.pow_lt_pow_right (by omega) hab

theorem cube_lt_of_lt {N q a b : ℕ} (hq : 2 ≤ q) (hN : N < q ^ b) (hab : 3 * b ≤ 8 * a) :
    N ^ 3 < q ^ (8 * a) :=
  calc N ^ 3 < (q ^ b) ^ 3 := Nat.pow_lt_pow_left hN (by norm_num)
    _ = q ^ (3 * b) := by rw [← pow_mul, mul_comm]
    _ ≤ q ^ (8 * a) := Nat.pow_le_pow_right (by omega) hab

theorem three_mul_le_eight_mul {m f : ℕ} (hm : 3 ≤ m) :
    3 * (f * (m ^ 2 - 1)) ≤ 8 * (f * (m * (m - 1) / 2)) := by
  have hT : 2 * (m * (m - 1) / 2) = m * (m - 1) :=
    Nat.mul_div_cancel' (Nat.even_mul_pred_self m).two_dvd
  have h4 : 3 * (m ^ 2 - 1) ≤ 4 * (m * (m - 1)) := by
    have e : m * (m - 1) = m ^ 2 - m := by
      rw [Nat.mul_sub, mul_one, sq]
    rw [e]
    have : m * 4 ≤ m ^ 2 + 3 := by nlinarith
    have : m ≤ m ^ 2 := Nat.le_self_pow (by norm_num) m
    have : 1 ≤ m ^ 2 := Nat.one_le_pow _ _ (by omega)
    omega
  calc 3 * (f * (m ^ 2 - 1)) = f * (3 * (m ^ 2 - 1)) := by ring
    _ ≤ f * (4 * (m * (m - 1))) := Nat.mul_le_mul_left f h4
    _ = 8 * (f * (m * (m - 1) / 2)) := by
        rw [show 4 * (m * (m - 1)) = 8 * (m * (m - 1) / 2) by omega]
        ring

theorem modelPart_projectiveSL {K : Type} [Field K] [Finite K] {m ℓ f : ℕ} (hm : 3 ≤ m)
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) :
    ModelPart (Nat.card (LinearFlag.projectiveSL m K)) ℓ (f * (m * (m - 1) / 2)) := by
  have := Fintype.ofFinite K
  have h := card_projectiveSL_mul_card_scalars (K := K) (n := m) (by omega)
  have hdvd := LinearFlag.card_scalars_dvd (K := K) (n := m) (by omega)
  rw [hK] at h hdvd
  have h2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  refine ⟨hℓ, ⟨Nat.card (LinearFlag.scalars m K),
    ∏ j ∈ Finset.Icc 2 m, ((ℓ ^ f) ^ j - 1), ?_, ?_, by rw [h, ← pow_mul]⟩, ?_⟩
  · intro hd
    have := not_dvd_pow_pow_sub_one hℓ hf (j := 1) le_rfl
    rw [pow_one] at this
    exact this (hd.trans hdvd)
  · exact not_dvd_prod_sub_one hℓ hf fun j hj => by simp at hj; omega
  · have hP : Nat.card (LinearFlag.projectiveSL m K) < (ℓ ^ f) ^ (m ^ 2 - 1) := by
      have h1 := card_SL_lt_pow_sub_one (K := K) (n := m) (by omega)
      rw [← Nat.card_eq_fintype_card, hK] at h1
      have h3 : Nat.card (LinearFlag.projectiveSL m K) ≤
          Nat.card (SpecialLinearGroup (Fin m) K) := by
        rw [(LinearFlag.scalars m K).card_eq_card_quotient_mul_card_subgroup]
        exact Nat.le_mul_of_pos_right _ Nat.card_pos
      omega
    rw [← pow_mul] at hP
    exact cube_lt_of_lt hℓ.two_le hP (three_mul_le_eight_mul hm)

theorem modelPart_SL {K : Type} [Field K] [Finite K] {m ℓ f : ℕ} (hm : 3 ≤ m)
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) :
    ModelPart (Nat.card (SpecialLinearGroup (Fin m) K)) ℓ (f * (m * (m - 1) / 2)) := by
  have := Fintype.ofFinite K
  have h := LinearFlag.card_SL_eq (K := K) (n := m) (by omega)
  rw [hK] at h
  refine ⟨hℓ, ⟨1, ∏ j ∈ Finset.Icc 2 m, ((ℓ ^ f) ^ j - 1), fun h1 => hℓ.one_lt.ne'
    (Nat.dvd_one.mp h1), ?_, by rw [mul_one, h, ← pow_mul]⟩, ?_⟩
  · exact not_dvd_prod_sub_one hℓ hf fun j hj => by simp at hj; omega
  · have h1 := card_SL_lt_pow_sub_one (K := K) (n := m) (by omega)
    rw [← Nat.card_eq_fintype_card, hK, ← pow_mul] at h1
    exact cube_lt_of_lt hℓ.two_le h1 (three_mul_le_eight_mul hm)

theorem modelPart_unitaryPSU {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) :
    ModelPart (Nat.card (unitaryPSU h 3)) ℓ (3 * f) := by
  have hc := card_unitaryPSU_three_mul_gcd h
  have hℓ := h.prime
  have hf := h.one_le
  have h2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  refine ⟨hℓ, ⟨Nat.gcd 3 (ℓ ^ f + 1), ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1), ?_, ?_, ?_⟩, ?_⟩
  · intro hd
    have := not_dvd_pow_pow_add_one hℓ hf (j := 1) le_rfl
    rw [pow_one] at this
    exact this (hd.trans (Nat.gcd_dvd_right _ _))
  · intro hd
    rcases hℓ.dvd_mul.mp hd with hd | hd
    · exact not_dvd_pow_pow_sub_one hℓ hf (by norm_num) hd
    · exact not_dvd_pow_pow_add_one hℓ hf (by norm_num) hd
  · rw [hc]
    ring
  · have hg : 0 < Nat.gcd 3 (ℓ ^ f + 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
    have hlt : Nat.card (unitaryPSU h 3) < (ℓ ^ f) ^ 8 :=
      calc Nat.card (unitaryPSU h 3) ≤ Nat.card (unitaryPSU h 3) * Nat.gcd 3 (ℓ ^ f + 1) :=
            Nat.le_mul_of_pos_right _ hg
        _ = (ℓ ^ f) ^ 3 * ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1) := hc
        _ < (ℓ ^ f) ^ 8 := su3Order_lt h2
    rw [← pow_mul] at hlt
    exact cube_lt_of_lt hℓ.two_le hlt (by omega)

theorem modelPart_unitarySU {ℓ f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData ℓ f K) :
    ModelPart (Nat.card (unitarySU ℓ f K 3)) ℓ (3 * f) := by
  have hc := card_unitarySU_three h
  have hℓ := h.prime
  have hf := h.one_le
  have h2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  refine ⟨hℓ, ⟨1, ((ℓ ^ f) ^ 2 - 1) * ((ℓ ^ f) ^ 3 + 1), fun h1 => hℓ.one_lt.ne'
    (Nat.dvd_one.mp h1), ?_, ?_⟩, ?_⟩
  · intro hd
    rcases hℓ.dvd_mul.mp hd with hd | hd
    · exact not_dvd_pow_pow_sub_one hℓ hf (by norm_num) hd
    · exact not_dvd_pow_pow_add_one hℓ hf (by norm_num) hd
  · rw [mul_one, hc]
    ring
  · have hlt : Nat.card (unitarySU ℓ f K 3) < (ℓ ^ f) ^ 8 := by
      rw [hc]
      exact su3Order_lt h2
    rw [← pow_mul] at hlt
    exact cube_lt_of_lt hℓ.two_le hlt (by omega)

theorem modelPart_statedSp {K : Type} [Field K] [Finite K] {r ℓ f : ℕ} (hr : 2 ≤ r)
    (hℓ : ℓ.Prime) (hf : 1 ≤ f) (hK : Nat.card K = ℓ ^ f) (hchar : ringChar K = ℓ) :
    ModelPart (Nat.card (StatedProj (StatedSp r K))) ℓ (f * r ^ 2) := by
  have hY : ¬ ℓ ∣ ∏ j ∈ Finset.Icc 1 r, ((ℓ ^ f) ^ (2 * j) - 1) :=
    not_dvd_prod_sub_one hℓ hf fun j hj => by simp at hj; omega
  have hsmall : ∀ d, 0 < d → Nat.card (StatedProj (StatedSp r K)) * d =
      (ℓ ^ f) ^ (r ^ 2) * ∏ j ∈ Finset.Icc 1 r, ((ℓ ^ f) ^ (2 * j) - 1) →
      Nat.card (StatedProj (StatedSp r K)) ^ 3 < ℓ ^ (8 * (f * r ^ 2)) := by
    intro d hd hN
    have hle : Nat.card (StatedProj (StatedSp r K)) ≤ (ℓ ^ f) ^ (2 * r ^ 2 + r) :=
      (Nat.le_mul_of_pos_right _ hd).trans
        (hN ▸ spOrd_le _ r)
    rw [← pow_mul] at hle
    refine cube_lt_of_le hℓ.two_le hle ?_
    have h1 : 3 * (2 * r ^ 2 + r) < 8 * r ^ 2 := by nlinarith
    calc 3 * (f * (2 * r ^ 2 + r)) = f * (3 * (2 * r ^ 2 + r)) := by ring
      _ < f * (8 * r ^ 2) := Nat.mul_lt_mul_of_pos_left h1 (by omega)
      _ = 8 * (f * r ^ 2) := by ring
  by_cases hℓ2 : ℓ = 2
  · subst hℓ2
    have : CharP K 2 := ringChar.of_eq hchar
    have hc := CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSp_of_charTwo (K := K) r
    rw [hK] at hc
    refine ⟨Nat.prime_two, ⟨1, _, fun h1 => by norm_num at h1, hY,
      by rw [mul_one, hc, ← pow_mul]⟩, hsmall 1 one_pos (by rw [mul_one, hc])⟩
  · have h2 : (2 : K) ≠ 0 := Ring.two_ne_zero (by rw [hchar]; exact hℓ2)
    have hc := CFSG.ClassicalInvolution.card_statedProj_statedSp_of_two_ne_zero h2
      (by omega : 1 ≤ r)
    rw [hK] at hc
    refine ⟨hℓ, ⟨2, _, fun h1 => hℓ2 ((Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).mp h1), hY,
      by rw [hc, ← pow_mul]⟩, hsmall 2 two_pos hc⟩

theorem modelPart_ordG2 {ℓ f : ℕ} (hℓ : ℓ.Prime) (hf : 1 ≤ f) :
    ModelPart (ordG2 (ℓ ^ f)) ℓ (f * 6) := by
  have h2 : 2 ≤ ℓ ^ f := le_trans hℓ.two_le (Nat.le_self_pow (by omega) ℓ)
  refine ⟨hℓ, ⟨1, ((ℓ ^ f) ^ 6 - 1) * ((ℓ ^ f) ^ 2 - 1), fun h1 => hℓ.one_lt.ne'
    (Nat.dvd_one.mp h1), ?_, ?_⟩, ?_⟩
  · intro hd
    rcases hℓ.dvd_mul.mp hd with hd | hd
    · exact not_dvd_pow_pow_sub_one hℓ hf (by norm_num) hd
    · exact not_dvd_pow_pow_sub_one hℓ hf (by norm_num) hd
  · rw [mul_one, ordG2, pow_mul, mul_assoc]
  · have hle := (ordG2_lt h2).le
    rw [← pow_mul] at hle
    exact cube_lt_of_le hℓ.two_le hle (by omega)

theorem modelPart_two {N m : ℕ} (h : ∃ r, Odd r ∧ N = 2 ^ m * r) (hs : N ^ 3 < 2 ^ (8 * m)) :
    ModelPart N 2 m := by
  obtain ⟨r, hr, hN⟩ := h
  exact ⟨Nat.prime_two, ⟨1, r, by norm_num, hr.not_two_dvd_nat, by rw [mul_one, hN]⟩, hs⟩

theorem modelPart_ordSuzuki {f : ℕ} (hf : 1 ≤ f) : ModelPart (ordSuzuki (2 ^ f)) 2 (f * 2) := by
  have h2 : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.le_self_pow (by omega) 2)
  refine modelPart_two (CFSG.Timmesfeld.Orders.profile_ordSuzuki hf).two ?_
  have hle := (ordSuzuki_lt h2).le
  rw [← pow_mul] at hle
  exact cube_lt_of_le (by norm_num) hle (by omega)

theorem modelPart_ordTrialityD4 {f : ℕ} (hf : 1 ≤ f) :
    ModelPart (ordTrialityD4 (2 ^ f)) 2 (f * 12) := by
  have h2 : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.le_self_pow (by omega) 2)
  refine modelPart_two (CFSG.Timmesfeld.Orders.profile_ordTrialityD4 hf).two ?_
  have hle := (ordTrialityD4_lt h2).le
  rw [← pow_mul] at hle
  exact cube_lt_of_le (by norm_num) hle (by omega)

theorem modelPart_ordTwistedF4 {f : ℕ} (hf : 1 ≤ f) :
    ModelPart (ordTwistedF4 (2 ^ f)) 2 (f * 12) := by
  have h2 : 2 ≤ 2 ^ f := le_trans (by norm_num) (Nat.le_self_pow (by omega) 2)
  refine modelPart_two (CFSG.Timmesfeld.Orders.profile_ordTwistedF4 hf).two ?_
  have hle := (ordTwistedF4_lt h2).le
  rw [← pow_mul] at hle
  exact cube_lt_of_le (by norm_num) hle (by omega)

end CFSG.RankThree.PartTwo.Sec8.Item8ModelProof
