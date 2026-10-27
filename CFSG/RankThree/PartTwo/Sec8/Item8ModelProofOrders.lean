module

public import CFSG.Timmesfeld.Orders.Distinct

public section

namespace CFSG.RankThree.PartTwo.Sec8.Item8ModelProof

open CFSG.Open (ordA ordTwistedA ordBC ordG2 ordTrialityD4 ordSuzuki ordTwistedF4)
open CFSG.Timmesfeld CFSG.Timmesfeld.Orders

theorem profA {m f : ℕ} (hm : 1 ≤ m) (hf : 1 ≤ f) :
    Profile (ordA m (2 ^ f)) (f * (m * (m + 1) / 2))
      (fun k => ∃ i ∈ Finset.Icc 2 (m + 1), k ∣ f * i) := by
  have hP : Odd (∏ i ∈ Finset.Icc 2 (m + 1), ((2 ^ f) ^ i - 1)) :=
    odd_prod fun i hi => odd_pow_sub_one hf (by simp at hi; omega)
  have hZ : ∀ p k, IsPrimitivePrimeDivisor p k → 0 < k →
      (p ∣ ∏ i ∈ Finset.Icc 2 (m + 1), ((2 ^ f) ^ i - 1) ↔
        ∃ i ∈ Finset.Icc 2 (m + 1), k ∣ f * i) := by
    intro p k hp hk
    rw [(Nat.Prime.prime hp.prime).dvd_finsetProd_iff]
    exact exists_congr fun i => and_congr_right fun _ => PrimDiv.dvd_pow_sub_one_iff hp hk f i
  have hmeq : ordA m (2 ^ f) = 2 ^ (f * (m * (m + 1) / 2)) *
      (∏ i ∈ Finset.Icc 2 (m + 1), ((2 ^ f) ^ i - 1)) / Nat.gcd (m + 1) (2 ^ f - 1) := by
    rw [ordA, pow_mul]
  rcases Nat.lt_or_ge m 2 with h1 | h2
  · have hm1 : m = 1 := by omega
    subst hm1
    refine Profile.of_div hmeq hP (c := 1) ?_ (by simp) (by norm_num) hZ
    rw [show (1 + 1 : ℕ) = 2 by rfl, Nat.coprime_two_left.mpr (odd_two_pow_sub_one hf)]
  · refine Profile.of_div hmeq hP (Nat.gcd_dvd_right _ _) ?_
      (Nat.gcd_pos_of_pos_left _ (by omega)) hZ
    have h23 : ({2, 3} : Finset ℕ) ⊆ Finset.Icc 2 (m + 1) := by
      intro x hx
      simp only [Finset.mem_insert, Finset.mem_singleton] at hx
      simp only [Finset.mem_Icc]; omega
    have := Finset.prod_dvd_prod_of_subset _ _ (fun i => (2 ^ f) ^ i - 1) h23
    rw [Finset.prod_pair (by norm_num)] at this
    exact (mul_dvd_mul (Nat.sub_one_dvd_pow_sub_one _ 2) (Nat.sub_one_dvd_pow_sub_one _ 3)).trans
      this

theorem profA2 {n : ℕ} (hn : 1 ≤ n) :
    Profile (ordA 2 (2 ^ n)) (n * 3) (fun k => k ∣ n * 2 ∨ k ∣ n * 3) := by
  have h := profA (m := 2) (f := n) (by norm_num) hn
  refine ⟨h.two, fun p k hp hk => (h.prim p k hp hk).trans ?_⟩
  constructor
  · rintro ⟨i, hi, hdvd⟩
    simp only [Finset.mem_Icc] at hi
    rcases (by omega : i = 2 ∨ i = 3) with rfl | rfl
    · exact Or.inl hdvd
    · exact Or.inr hdvd
  · rintro (h2 | h3)
    · exact ⟨2, by simp, h2⟩
    · exact ⟨3, by simp, h3⟩

theorem profBC {r f : ℕ} (hf : 1 ≤ f) :
    Profile (ordBC r (2 ^ f)) (f * (r * r)) (fun k => ∃ i ∈ Finset.Icc 1 r, k ∣ f * (2 * i)) := by
  have hP : Odd (∏ i ∈ Finset.Icc 1 r, ((2 ^ f) ^ (2 * i) - 1)) :=
    odd_prod fun i hi => odd_pow_sub_one hf (by simp at hi; omega)
  have hmeq : ordBC r (2 ^ f) = 2 ^ (f * (r * r)) * ∏ i ∈ Finset.Icc 1 r,
      ((2 ^ f) ^ (2 * i) - 1) := by
    rw [ordBC, Nat.coprime_two_left.mpr (odd_two_pow_sub_one hf), Nat.div_one,
      pow_mul 2 f (r * r)]
  refine Profile.of_eq hmeq hP (fun p k hp hk => ?_)
  rw [(Nat.Prime.prime hp.prime).dvd_finsetProd_iff]
  exact exists_congr fun i => and_congr_right fun _ => PrimDiv.dvd_pow_sub_one_iff hp hk f _

theorem profG2 {f : ℕ} (hf : 1 ≤ f) :
    Profile (ordG2 (2 ^ f)) (f * 6) (fun k => k ∣ f * 6 ∨ k ∣ f * 2) := by
  refine Profile.of_eq (ordG2_eq f)
    ((odd_pow_sub_one hf (by norm_num)).mul (odd_pow_sub_one hf (by norm_num)))
    (fun p k hp hk => ?_)
  rw [hp.prime.dvd_mul, PrimDiv.dvd_pow_sub_one_iff hp hk, PrimDiv.dvd_pow_sub_one_iff hp hk]

theorem profSz {f : ℕ} (hf : 1 ≤ f) :
    Profile (ordSuzuki (2 ^ f)) (f * 2) (fun k => (k ∣ 2 * (f * 2) ∧ ¬ k ∣ f * 2) ∨ k ∣ f) := by
  have hmeq : ordSuzuki (2 ^ f) = 2 ^ (f * 2) * (((2 ^ f) ^ 2 + 1) * (2 ^ f - 1)) := by
    rw [ordSuzuki, pow_mul, mul_assoc]
  refine Profile.of_eq hmeq ((odd_pow_add_one hf (by norm_num)).mul (odd_two_pow_sub_one hf))
    (fun p k hp hk => ?_)
  rw [hp.prime.dvd_mul, PrimDiv.dvd_pow_add_one_iff hp hk, hp.dvd_sub_one_iff hk]

theorem profD4 {f : ℕ} (hf : 1 ≤ f) :
    Profile (ordTrialityD4 (2 ^ f)) (f * 12)
      (fun k => (k ∣ f * 12 ∧ ¬ k ∣ f * 4) ∨ k ∣ f * 6 ∨ k ∣ f * 2) := by
  have hmeq : ordTrialityD4 (2 ^ f) = 2 ^ (f * 12) *
      (((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) * (((2 ^ f) ^ 6 - 1) * ((2 ^ f) ^ 2 - 1))) := by
    rw [ordTrialityD4, pow_mul]; ring
  have h1 : Odd ((2 ^ f) ^ 8 + (2 ^ f) ^ 4 + 1) := by
    have he : Even ((2 ^ f) ^ 8 + (2 ^ f) ^ 4) := by
      rw [← pow_mul, ← pow_mul]
      exact ((Nat.even_pow' (by omega)).mpr even_two).add ((Nat.even_pow' (by omega)).mpr even_two)
    exact he.add_one
  refine Profile.of_eq hmeq (h1.mul ((odd_pow_sub_one hf (by norm_num)).mul
    (odd_pow_sub_one hf (by norm_num)))) (fun p k hp hk => ?_)
  rw [hp.prime.dvd_mul, hp.prime.dvd_mul, PrimDiv.dvd_pow_sub_one_iff hp hk,
    PrimDiv.dvd_pow_sub_one_iff hp hk]
  constructor
  · rintro (h | h | h)
    · rcases PrimDiv.index_of_dvd_triality hp hk f h with h' | rfl
      · exact Or.inl h'
      · exact Or.inr (Or.inr ⟨f, by ring⟩)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)
  · rintro (h | h | h)
    · exact Or.inl (PrimDiv.dvd_triality_of hp hk f h.1 h.2)
    · exact Or.inr (Or.inl h)
    · exact Or.inr (Or.inr h)

theorem prof2F4 {f : ℕ} (hf : 1 ≤ f) :
    Profile (ordTwistedF4 (2 ^ f)) (f * 12)
      (fun k => (k ∣ 2 * (f * 6) ∧ ¬ k ∣ f * 6) ∨ k ∣ f * 4 ∨
        (k ∣ 2 * (f * 3) ∧ ¬ k ∣ f * 3) ∨ k ∣ f) := by
  have hmeq : ordTwistedF4 (2 ^ f) = 2 ^ (f * 12) * (((2 ^ f) ^ 6 + 1) * (((2 ^ f) ^ 4 - 1) *
      (((2 ^ f) ^ 3 + 1) * (2 ^ f - 1)))) := by
    rw [ordTwistedF4, pow_mul]; ring
  refine Profile.of_eq hmeq ((odd_pow_add_one hf (by norm_num)).mul
    ((odd_pow_sub_one hf (by norm_num)).mul ((odd_pow_add_one hf (by norm_num)).mul
    (odd_two_pow_sub_one hf)))) (fun p k hp hk => ?_)
  simp only [hp.prime.dvd_mul, PrimDiv.dvd_pow_add_one_iff hp hk,
    PrimDiv.dvd_pow_sub_one_iff hp hk, hp.dvd_sub_one_iff hk]

theorem ree_native_eq_ordTwistedF4 {q : ℕ} (hq : 1 ≤ q) :
    q ^ 12 * (q - 1) ^ 2 * (q + 1) ^ 2 * (q ^ 2 + 1) ^ 2 * (q ^ 2 - q + 1) *
      (q ^ 4 - q ^ 2 + 1) = ordTwistedF4 q := by
  have h1 : q ≤ q ^ 2 := Nat.le_self_pow (by norm_num) q
  have h2 : q ^ 2 ≤ q ^ 4 := Nat.pow_le_pow_right hq (by norm_num)
  have h4 : 1 ≤ q ^ 4 := Nat.one_le_pow _ _ hq
  rw [ordTwistedF4]
  zify [hq, h1, h2, h4]
  ring

theorem suzuki_eq_ordSuzuki (q : ℕ) : (q ^ 2 + 1) * q ^ 2 * (q - 1) = ordSuzuki q := by
  rw [ordSuzuki]
  ring

theorem eq_of_ordA_eq_ordA_two {m f n : ℕ} (hm : 1 ≤ m) (hf : 1 ≤ f) (hn : 2 ≤ n)
    (h : ordA m (2 ^ f) = ordA 2 (2 ^ n)) : (m = 2 ∧ f = n) ∨ (m = 3 ∧ f = 1 ∧ n = 2) := by
  have P1 := profA hm hf
  rw [h] at P1
  obtain ⟨hN, hZ⟩ := P1.transfer (profA2 (by omega))
  set T := m * (m + 1) / 2 with hT
  have h2T : 2 * T = m * (m + 1) := by
    rw [hT]
    exact Nat.mul_div_cancel' (Nat.even_mul_succ_self m).two_dvd
  rcases Nat.lt_or_ge n 3 with hn3 | hn3
  · obtain rfl : n = 2 := by omega
    have hfT : f * T = 6 := by omega
    have hT6 : T ≤ 6 := by nlinarith
    have hm3 : m ≤ 3 := by nlinarith
    rcases (by omega : m = 1 ∨ m = 2 ∨ m = 3) with rfl | rfl | rfl
    · exfalso
      have hT1 : T = 1 := by omega
      have hf6 : f = 6 := by rw [hT1] at hfT; omega
      subst hf6
      rcases (hZ 12 (by norm_num) (by norm_num)).mp ⟨2, by simp, by norm_num⟩ with h12 | h12 <;>
        norm_num at h12
    · left
      have hT3 : T = 3 := by omega
      exact ⟨rfl, by rw [hT3] at hfT; omega⟩
    · right
      have hT6' : T = 6 := by omega
      exact ⟨rfl, by rw [hT6'] at hfT; omega, rfl⟩
  · obtain ⟨i, hi, hdvd⟩ := (hZ (3 * n) (by omega) (by omega)).mpr (Or.inr ⟨1, by ring⟩)
    simp only [Finset.mem_Icc] at hi
    have hle : 3 * n ≤ f * (m + 1) :=
      (Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hdvd).trans
        (Nat.mul_le_mul_left _ hi.2)
    have hfT : f * T = n * 3 := hN
    have hTm : T ≤ m + 1 := by
      by_contra hc
      have : f * (m + 1) < f * T := Nat.mul_lt_mul_of_pos_left (by omega) (by omega)
      omega
    have hm2 : m ≤ 2 := by nlinarith
    rcases (by omega : m = 1 ∨ m = 2) with rfl | rfl
    · exfalso
      have hT1 : T = 1 := by omega
      have hf3 : f = 3 * n := by rw [hT1] at hfT; omega
      rcases (hZ (6 * n) (by omega) (by omega)).mp ⟨2, by simp, ⟨1, by rw [hf3]; ring⟩⟩ with
          h6 | h6 <;>
        · have := Nat.le_of_dvd (by omega) h6
          omega
    · left
      have hT3 : T = 3 := by omega
      exact ⟨rfl, by rw [hT3] at hfT; omega⟩

theorem ordBC_ne_ordA_two {r f n : ℕ} (hr : 3 ≤ r) (hf : 1 ≤ f) (hn : 1 ≤ n) :
    ordBC r (2 ^ f) ≠ ordA 2 (2 ^ n) := by
  intro h
  have P1 := profBC (r := r) hf
  rw [h] at P1
  obtain ⟨hN, hZ⟩ := P1.transfer (profA2 hn)
  have hrr : 9 ≤ r * r := Nat.mul_le_mul hr hr
  have hN' : f * (r * r) = n * 3 := hN
  have h9 : 9 ≤ n * 3 := by
    rw [← hN']
    calc 9 ≤ r * r := hrr
      _ ≤ f * (r * r) := Nat.le_mul_of_pos_left _ (by omega)
  obtain ⟨i, hi, hdvd⟩ := (hZ (3 * n) (by omega) (by omega)).mpr (Or.inr ⟨1, by ring⟩)
  simp only [Finset.mem_Icc] at hi
  have hle : 3 * n ≤ f * (2 * r) :=
    (Nat.le_of_dvd (Nat.mul_pos (by omega) (by omega)) hdvd).trans
      (Nat.mul_le_mul_left _ (by omega))
  have : f * (2 * r) < f * (r * r) := Nat.mul_lt_mul_of_pos_left (by nlinarith) (by omega)
  omega

theorem ordG2_ne_ordA_two {f n : ℕ} (hf : 1 ≤ f) (hn : 1 ≤ n) : ordG2 (2 ^ f) ≠ ordA 2 (2 ^ n) := by
  intro h
  have P1 := profG2 hf
  rw [h] at P1
  obtain ⟨hN, hZ⟩ := P1.transfer (profA2 hn)
  have hn2 : n = 2 * f := by have : f * 6 = n * 3 := hN; omega
  rcases (hZ (2 * n) (by omega) (by omega)).mpr (Or.inl ⟨1, by ring⟩) with ⟨c, hc⟩ | ⟨c, hc⟩
  · have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f)
      (show f * 6 = f * (4 * c) by rw [hc, hn2]; ring)
    omega
  · have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f)
      (show f * 2 = f * (4 * c) by rw [hc, hn2]; ring)
    omega

theorem ordSuzuki_ne_ordA_two {f n : ℕ} (hf : 3 ≤ f) (hn : 1 ≤ n) :
    ordSuzuki (2 ^ f) ≠ ordA 2 (2 ^ n) := by
  intro h
  have P1 := profSz (f := f) (by omega)
  rw [h] at P1
  obtain ⟨hN, hZ⟩ := P1.transfer (profA2 hn)
  have hN' : f * 2 = n * 3 := hN
  by_cases hn2 : n = 2
  · subst hn2
    have hf3 : f = 3 := by omega
    subst hf3
    revert h
    decide
  · rcases (hZ (3 * n) (by omega) (by omega)).mpr (Or.inr ⟨1, by ring⟩) with ⟨-, hnot⟩ | hdvd
    · exact hnot ⟨1, by omega⟩
    · have := Nat.le_of_dvd (by omega) hdvd
      omega

theorem ordTrialityD4_ne_ordA_two {f n : ℕ} (hf : 1 ≤ f) (hn : 1 ≤ n) :
    ordTrialityD4 (2 ^ f) ≠ ordA 2 (2 ^ n) := by
  intro h
  have P1 := profD4 hf
  rw [h] at P1
  obtain ⟨hN, hZ⟩ := P1.transfer (profA2 hn)
  have hn4 : n = 4 * f := by have : f * 12 = n * 3 := hN; omega
  rcases (hZ (2 * n) (by omega) (by omega)).mpr (Or.inl ⟨1, by ring⟩) with ⟨⟨c, hc⟩, -⟩ |
      ⟨c, hc⟩ | ⟨c, hc⟩
  · have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f)
      (show f * 12 = f * (8 * c) by rw [hc, hn4]; ring)
    omega
  · have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f)
      (show f * 6 = f * (8 * c) by rw [hc, hn4]; ring)
    omega
  · have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f)
      (show f * 2 = f * (8 * c) by rw [hc, hn4]; ring)
    omega

theorem ordTwistedF4_ne_ordA_two {f n : ℕ} (hf : 1 ≤ f) (hn : 1 ≤ n) :
    ordTwistedF4 (2 ^ f) ≠ ordA 2 (2 ^ n) := by
  intro h
  have P1 := prof2F4 hf
  rw [h] at P1
  obtain ⟨hN, hZ⟩ := P1.transfer (profA2 hn)
  have hn4 : n = 4 * f := by have : f * 12 = n * 3 := hN; omega
  rcases (hZ (2 * n) (by omega) (by omega)).mpr (Or.inl ⟨1, by ring⟩) with ⟨⟨c, hc⟩, -⟩ |
      ⟨c, hc⟩ | ⟨⟨c, hc⟩, -⟩ | ⟨c, hc⟩
  · have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f)
      (show f * 12 = f * (8 * c) by rw [show f * 12 = 2 * (f * 6) by ring, hc, hn4]; ring)
    omega
  · have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f)
      (show f * 4 = f * (8 * c) by rw [hc, hn4]; ring)
    omega
  · have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f)
      (show f * 6 = f * (8 * c) by rw [show f * 6 = 2 * (f * 3) by ring, hc, hn4]; ring)
    omega
  · have := Nat.eq_of_mul_eq_mul_left (by omega : 0 < f)
      (show f * 1 = f * (8 * c) from
        calc f * 1 = f := mul_one f
          _ = 2 * n * c := hc
          _ = f * (8 * c) := by rw [hn4]; ring)
    omega

end CFSG.RankThree.PartTwo.Sec8.Item8ModelProof
