module

public import CFSG.RankThree.PartOne.S13K.AllSplitRows
public import CFSG.RankThree.PartOne.S15K.LayerTypes
public import CFSG.RankThree.PartOne.HNB.RowOrders
public import CFSG.Timmesfeld.Orders.Classical

public section

namespace CFSG.RankThree.PartOne.S13K

open CFSG CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S15K CFSG.RankThree CFSG.RankThree.LocalRank
  CFSG.RankThree.GroupTheory CFSG.Open CFSG.Assembly.LowTwoRank
  CFSG.Timmesfeld CFSG.Timmesfeld.Orders

theorem ordA_three_eq {q : ℕ} (hq : Odd (q - 1)) :
    ordA 3 q = q ^ 6 * ((q ^ 2 - 1) * (q ^ 3 - 1) * (q ^ 4 - 1)) := by
  have hg : Nat.gcd 4 (q - 1) = 1 := by
    have : Nat.Coprime 2 (q - 1) := Nat.coprime_two_left.mpr hq
    exact (Nat.Coprime.pow_left 2 this : Nat.Coprime (2 ^ 2) (q - 1))
  unfold ordA
  rw [show 3 + 1 = 4 from rfl, hg, Nat.div_one, show 3 * 4 / 2 = 6 from rfl,
    show Finset.Icc 2 4 = {2, 3, 4} from by decide, Finset.prod_insert (by decide),
    Finset.prod_insert (by decide), Finset.prod_singleton]
  ring

theorem ordA_two_eq (q : ℕ) :
    ordA 2 q = q ^ 3 * ((q ^ 2 - 1) * (q ^ 3 - 1)) / Nat.gcd 3 (q - 1) := by
  unfold ordA
  rw [show 2 + 1 = 3 from rfl, show 2 * 3 / 2 = 3 from rfl,
    show Finset.Icc 2 3 = {2, 3} from by decide, Finset.prod_pair (by decide)]

theorem ordA_three_eq_ordA_two {f g : ℕ} (hf : 1 ≤ f) (hg : 1 ≤ g)
    (h : ordA 3 (2 ^ f) = ordA 2 (2 ^ g)) : f = 1 := by
  have hX := profile_ordA (n := 3) (by norm_num) hf
  have hY := profile_ordA (n := 2) (by norm_num) hg
  rw [← h] at hY
  have hN := (hX.transfer hY).1
  norm_num at hN
  have hg2 : g = 2 * f := by omega
  subst hg2
  set Q : ℕ := 2 ^ f with hQ
  have hQ2 : 2 ≤ Q := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ f := Nat.pow_le_pow_right (by norm_num) hf
  have hQg : 2 ^ (2 * f) = Q ^ 2 := by rw [hQ, ← pow_mul, mul_comm]
  have hodd : Odd (Q - 1) := by
    have : Even Q := by rw [hQ]; exact (Nat.even_pow.mpr ⟨even_two, by omega⟩)
    obtain ⟨k, hk⟩ := this
    exact ⟨k - 1, by omega⟩
  rw [ordA_three_eq hodd, hQg, ordA_two_eq] at h
  have hd : Nat.gcd 3 (Q ^ 2 - 1) = 1 ∨ Nat.gcd 3 (Q ^ 2 - 1) = 3 := by
    have hdvd : Nat.gcd 3 (Q ^ 2 - 1) ∣ 3 := Nat.gcd_dvd_left _ _
    rcases (Nat.dvd_prime Nat.prime_three).1 hdvd with h1 | h1 <;> simp [h1]
  have hdvd1 : Nat.gcd 3 (Q ^ 2 - 1) ∣ (Q ^ 2) ^ 3 * (((Q ^ 2) ^ 2 - 1) * ((Q ^ 2) ^ 3 - 1)) := by
    refine Dvd.dvd.mul_left ?_ _
    refine Dvd.dvd.mul_right ?_ _
    have : Q ^ 2 - 1 ∣ (Q ^ 2) ^ 2 - 1 := by
      have := Nat.sub_dvd_pow_sub_pow (Q ^ 2) 1 2
      simpa using this
    exact (Nat.gcd_dvd_right _ _).trans this
  have hd0 : 0 < Nat.gcd 3 (Q ^ 2 - 1) := Nat.gcd_pos_of_pos_left _ (by norm_num)
  have h' := ((Nat.eq_div_iff_mul_eq_left hd0.ne' hdvd1).1 h).symm
  have hQ1 : 1 ≤ Q := by omega
  have e2 : 1 ≤ Q ^ 2 := Nat.one_le_pow _ _ hQ1
  have e3 : 1 ≤ Q ^ 3 := Nat.one_le_pow _ _ hQ1
  have e4 : 1 ≤ Q ^ 4 := Nat.one_le_pow _ _ hQ1
  have e6 : 1 ≤ Q ^ 6 := Nat.one_le_pow _ _ hQ1
  have e22 : 1 ≤ (Q ^ 2) ^ 2 := Nat.one_le_pow _ _ e2
  have e23 : 1 ≤ (Q ^ 2) ^ 3 := Nat.one_le_pow _ _ e2
  have hz : ((Q : ℤ) ^ 6 * (((Q : ℤ) ^ 2 - 1) * ((Q : ℤ) ^ 3 - 1) * ((Q : ℤ) ^ 4 - 1))) *
      (Nat.gcd 3 (Q ^ 2 - 1) : ℤ) = ((Q : ℤ) ^ 2) ^ 3 * ((((Q : ℤ) ^ 2) ^ 2 - 1) *
        (((Q : ℤ) ^ 2) ^ 3 - 1)) := by
    have := congrArg (fun n : ℕ => (n : ℤ)) h'
    push_cast [Nat.cast_sub e2, Nat.cast_sub e3, Nat.cast_sub e4, Nat.cast_sub e22,
      Nat.cast_sub e23] at this
    exact this
  set d : ℤ := (Nat.gcd 3 (Q ^ 2 - 1) : ℤ) with hdd
  have hQz : (2 : ℤ) ≤ (Q : ℤ) := by exact_mod_cast hQ2
  have hkey : ((Q : ℤ) ^ 6 * (((Q : ℤ) ^ 4 - 1) * ((Q : ℤ) ^ 3 - 1))) *
      (((Q : ℤ) ^ 2 - 1) * d - ((Q : ℤ) ^ 3 + 1)) = 0 := by
    linear_combination hz
  have hne : ((Q : ℤ) ^ 6 * (((Q : ℤ) ^ 4 - 1) * ((Q : ℤ) ^ 3 - 1))) ≠ 0 := by
    have h1 : (0 : ℤ) < (Q : ℤ) ^ 6 := by positivity
    have h2 : (0 : ℤ) < (Q : ℤ) ^ 4 - 1 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℤ) ≤ 2) hQz 4]
    have h3 : (0 : ℤ) < (Q : ℤ) ^ 3 - 1 := by nlinarith [pow_le_pow_left₀ (by norm_num : (0:ℤ) ≤ 2) hQz 3]
    positivity
  have h4 : ((Q : ℤ) ^ 2 - 1) * d = (Q : ℤ) ^ 3 + 1 := by
    have := (mul_eq_zero.1 hkey).resolve_left hne
    linarith
  have hd' : d = 1 ∨ d = 3 := by
    rcases hd with h1 | h1
    · left; simp [hdd, h1]
    · right; simp [hdd, h1]
  rcases hd' with h1 | h1
  · rw [h1] at h4
    nlinarith [sq_nonneg (Q : ℤ), mul_pos (by linarith : (0:ℤ) < Q) (by linarith : (0:ℤ) < Q)]
  · rw [h1] at h4
    have h5 : ((Q : ℤ) - 2) ^ 2 * ((Q : ℤ) + 1) = 0 := by linear_combination -h4
    have h6 : (Q : ℤ) = 2 := by
      rcases mul_eq_zero.1 h5 with h | h
      · have := pow_eq_zero_iff (two_ne_zero) |>.1 h
        linarith
      · linarith
    have h7 : Q = 2 := by exact_mod_cast h6
    have h8 : 2 ^ f = 2 ^ 1 := by rw [← hQ, h7]; norm_num
    exact Nat.pow_right_injective (le_refl 2) h8

theorem kf158NoRowSixEight (hS13 : Sec13Avail) : KF158NoRowSixEight := by
  intro G _ _ p A c L E h15 hF hout J hJ hJI
  have h := h15.h12
  have hEA : E = A := by
    rcases hout with h | h
    · obtain ⟨-, -, -, -, -, hEA, -⟩ := h
      exact hEA
    · obtain ⟨-, -, -, -, -, hEA, -⟩ := h
      exact hEA
  have hnot5 : ¬ Outcome152Five p E A (lieGenerated p E) := by
    rintro ⟨-, -, -, -, -, -, hne, -⟩
    exact hne hEA
  have hF13 := hS13 G p A c L E h hnot5
  obtain ⟨b, hb, hb1, hJb⟩ := exists_mem_thetaComponentsAt_of_mem_thetaCompZeroE hJ.1
  obtain ⟨g, hg1, -, hg⟩ := layerTypes G p A c L E h15 hF hF13 hout b hb hb1 J hJb hJI
  have hp5 : 5 ≤ p := Sec12Three.five_le h
  constructor
  · intro hrow
    obtain ⟨f', hf'1, -, hm⟩ : ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f - 1 ∧
        StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSU 5 2 f := hrow
    have e2 : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordTwistedA 4 (2 ^ f') :=
      (card_statedClassicalModel_two hm).2.1 rfl
    rcases hg with hg | hg | hg | hg
    · have e1 : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordA 1 (2 ^ g) :=
        (card_statedClassicalModel_two hg).1 rfl
      exact ordA_ne_ordTwistedA (n := 1) le_rfl hg1 (by norm_num : 2 ≤ 4) hf'1 (e1.symm.trans e2)
    · have e1 : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordA 2 (2 ^ g) :=
        (card_statedClassicalModel_two hg).1 rfl
      exact ordA_ne_ordTwistedA (n := 2) (by norm_num) hg1 (by norm_num : 2 ≤ 4) hf'1
        (e1.symm.trans e2)
    · have e1 : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordBC 2 (2 ^ g) :=
        (card_statedClassicalModel_two hg).2.2.1 rfl
      exact S12K.ordTwistedA_ne_ordBC_two (by norm_num : 2 ≤ 4) hf'1 hg1 (e2.symm.trans e1)
    · have e1 : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordTwistedA 3 (2 ^ g) :=
        (card_statedClassicalModel_two hg).2.1 rfl
      exact HNB.ordTwistedA_three_ne_four hg1 hf'1 (e1.symm.trans e2)
  · intro hrow
    obtain ⟨f', hf'1, hpf', hm⟩ : ∃ f : ℕ, 1 ≤ f ∧ p ∣ 2 ^ f + 1 ∧
        StatedClassicalModel (↥J ⧸ Subgroup.center ↥J) .PSL 4 2 f := hrow
    have e2 : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordA 3 (2 ^ f') :=
      (card_statedClassicalModel_two hm).1 rfl
    rcases hg with hg | hg | hg | hg
    · have e1 : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordA 1 (2 ^ g) :=
        (card_statedClassicalModel_two hg).1 rfl
      exact S12K.ordA_ne_ordA_one (n := 3) (by norm_num) hf'1 hg1 (e2.symm.trans e1)
    · have e1 : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordA 2 (2 ^ g) :=
        (card_statedClassicalModel_two hg).1 rfl
      have hf1 : f' = 1 := ordA_three_eq_ordA_two hf'1 hg1 (e2.symm.trans e1)
      subst hf1
      have h3 : p ∣ 3 := by simpa using hpf'
      have := Nat.le_of_dvd (by norm_num) h3
      omega
    · have e1 : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordBC 2 (2 ^ g) :=
        (card_statedClassicalModel_two hg).2.2.1 rfl
      exact ordA_ne_ordBC_two (n := 3) (by norm_num) hf'1 hg1 (e2.symm.trans e1)
    · have e1 : Nat.card (↥J ⧸ Subgroup.center ↥J) = ordTwistedA 3 (2 ^ g) :=
        (card_statedClassicalModel_two hg).2.1 rfl
      exact ordA_ne_ordTwistedA (n := 3) (by norm_num) hf'1 (by norm_num : 2 ≤ 3) hg1
        (e2.symm.trans e1)

end CFSG.RankThree.PartOne.S13K
