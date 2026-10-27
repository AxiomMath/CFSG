module

public import CFSG.RankThree.Chevalley.SteinbergBID4RegularCentralizer

public section

namespace CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.RankThree.Chevalley

theorem digits_eq_zero {q : ℤ} (hq : 7 ≤ q) {d₀ d₁ d₂ : ℤ} (h₀ : |d₀| ≤ 4) (h₁ : |d₁| ≤ 4)
    (h₂ : |d₂| ≤ 4) (hdvd : q ^ 3 - 1 ∣ d₀ + d₁ * q + d₂ * q ^ 2) :
    d₀ = 0 ∧ d₁ = 0 ∧ d₂ = 0 := by
  obtain ⟨m, hm⟩ := hdvd
  rw [abs_le] at h₀ h₁ h₂
  have hq0 : 0 < q := by omega
  have hb1 : d₀ + d₁ * q + d₂ * q ^ 2 ≤ 4 + 4 * q + 4 * q ^ 2 := by nlinarith
  have hb2 : -(4 + 4 * q + 4 * q ^ 2) ≤ d₀ + d₁ * q + d₂ * q ^ 2 := by nlinarith
  have hlt : 4 + 4 * q + 4 * q ^ 2 < q ^ 3 - 1 := by nlinarith
  have hm0 : m = 0 := by
    rcases lt_trichotomy m 0 with hm' | hm' | hm'
    · have : (q ^ 3 - 1) * m ≤ -(q ^ 3 - 1) := by nlinarith
      linarith
    · exact hm'
    · have : q ^ 3 - 1 ≤ (q ^ 3 - 1) * m := by nlinarith
      linarith
  rw [hm0, mul_zero] at hm
  have hd₀ : d₀ = 0 := by
    have hdiv : q ∣ d₀ := ⟨-(d₁ + d₂ * q), by linear_combination hm⟩
    obtain ⟨k, hk⟩ := hdiv
    rcases lt_trichotomy k 0 with hk' | hk' | hk'
    · nlinarith
    · rw [hk', mul_zero] at hk
      exact hk
    · nlinarith
  subst hd₀
  have hd₁ : d₁ = 0 := by
    have hdiv : q ∣ d₁ := ⟨-d₂, by
      have : q * (d₁ + d₂ * q) = 0 := by linear_combination hm
      rcases mul_eq_zero.1 this with h | h
      · omega
      · linear_combination h⟩
    obtain ⟨k, hk⟩ := hdiv
    rcases lt_trichotomy k 0 with hk' | hk' | hk'
    · nlinarith
    · rw [hk', mul_zero] at hk
      exact hk
    · nlinarith
  subst hd₁
  refine ⟨rfl, rfl, ?_⟩
  have : d₂ * q ^ 2 = 0 := by linear_combination hm
  rcases mul_eq_zero.1 this with h | h
  · exact h
  · exact absurd h (by positivity)

abbrev n0 : Fin TwistTag.D4.tag.rank := ⟨0, by decide⟩
abbrev n1 : Fin TwistTag.D4.tag.rank := ⟨1, by decide⟩
abbrev n3 : Fin TwistTag.D4.tag.rank := ⟨3, by decide⟩

@[expose] def pairK (k : Fin TwistTag.D4.tag.rank) (v : Fin TwistTag.D4.tag.rank → ℤ) : ℤ :=
  ∑ j, v j * TwistTag.D4.tag.cartan k j

@[expose] def colOf (e : ℕ) (i : Fin TwistTag.D4.tag.rank) : Fin TwistTag.D4.tag.rank → ℤ :=
  d4RootVec (d4Dig i (d4TupCode e))

@[expose] def shortExp (q : ℤ) (j : Fin TwistTag.D4.tag.rank) : ℤ :=
  TwistTag.D4.tag.cartan n0 j + q * TwistTag.D4.tag.cartan n1 j +
    q ^ 2 * TwistTag.D4.tag.cartan n3 j

@[expose] def shortVal (q : ℤ) (v : Fin TwistTag.D4.tag.rank → ℤ) : ℤ :=
  ∑ j, v j * shortExp q j

theorem shortVal_eq (q : ℤ) (v : Fin TwistTag.D4.tag.rank → ℤ) :
    shortVal q v = pairK n0 v + q * pairK n1 v + q ^ 2 * pairK n3 v := by
  simp only [shortVal, shortExp, pairK, Finset.mul_sum]
  rw [← Finset.sum_add_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

theorem shortExp_eq (q : ℤ) (i : Fin TwistTag.D4.tag.rank) :
    shortExp q i = pairK n0 (Pi.single i 1) + q * pairK n1 (Pi.single i 1) +
      q ^ 2 * pairK n3 (Pi.single i 1) := by
  rw [← shortVal_eq]
  simp only [shortVal, Pi.single_apply]
  rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
  simp

@[expose] def digitBoundCheck : Bool :=
  d4WeylTab.all fun e => decide (∀ i : Fin TwistTag.D4.tag.rank, ∀ k : Fin TwistTag.D4.tag.rank,
    |pairK k (colOf e i)| ≤ 2)

theorem digitBoundCheck_eq : digitBoundCheck = true := by decide +kernel

@[expose] def shortGenCheck : Bool :=
  d4WeylTab.all fun e =>
    decide (¬ ∀ i : Fin TwistTag.D4.tag.rank, pairK n3 (colOf e i) = TwistTag.D4.tag.cartan n0 i ∧
        pairK n0 (colOf e i) = TwistTag.D4.tag.cartan n1 i ∧
        pairK n1 (colOf e i) = TwistTag.D4.tag.cartan n3 i) &&
    decide (¬ ∀ i : Fin TwistTag.D4.tag.rank, pairK n1 (colOf e i) = TwistTag.D4.tag.cartan n0 i ∧
        pairK n3 (colOf e i) = TwistTag.D4.tag.cartan n1 i ∧
        pairK n0 (colOf e i) = TwistTag.D4.tag.cartan n3 i)

theorem shortGenCheck_eq : shortGenCheck = true := by decide +kernel

@[expose] def shortSmallCheck (q : ℤ) : Bool :=
  d4WeylTab.all fun e =>
    decide (¬ ∀ i : Fin TwistTag.D4.tag.rank, (q * shortVal q (colOf e i) - shortExp q i) %
        (q ^ 3 - 1) = 0) &&
    decide (¬ ∀ i : Fin TwistTag.D4.tag.rank, (q ^ 2 * shortVal q (colOf e i) - shortExp q i) %
        (q ^ 3 - 1) = 0)

theorem shortSmallCheck_two : shortSmallCheck 2 = true := by decide +kernel

theorem shortSmallCheck_four : shortSmallCheck 4 = true := by decide +kernel

theorem shortSmallCheck_five : shortSmallCheck 5 = true := by decide +kernel

theorem not_short_weyl {q : ℤ} (hq : q = 2 ∨ q = 4 ∨ q = 5 ∨ 7 ≤ q) {s : ℕ} (hs : s = 1 ∨ s = 2)
    (w : WeylGroup TwistTag.D4.tag) :
    ¬ ∀ i, q ^ 3 - 1 ∣ q ^ s * shortVal q (w • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ)) -
      shortExp q i := by
  intro hall
  obtain ⟨e, he, hw⟩ := exists_mem_d4WeylTab w
  have hcol : ∀ i, w • (Pi.single i 1 : Fin TwistTag.D4.tag.rank → ℤ) = colOf e i := hw
  simp only [hcol] at hall
  rcases hq with rfl | rfl | rfl | hq7
  · have h := List.all_eq_true.1 shortSmallCheck_two e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases hs with rfl | rfl
    · exact h.1 fun i => Int.emod_eq_zero_of_dvd (by simpa using hall i)
    · exact h.2 fun i => Int.emod_eq_zero_of_dvd (by simpa using hall i)
  · have h := List.all_eq_true.1 shortSmallCheck_four e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases hs with rfl | rfl
    · exact h.1 fun i => Int.emod_eq_zero_of_dvd (by simpa using hall i)
    · exact h.2 fun i => Int.emod_eq_zero_of_dvd (by simpa using hall i)
  · have h := List.all_eq_true.1 shortSmallCheck_five e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at h
    rcases hs with rfl | rfl
    · exact h.1 fun i => Int.emod_eq_zero_of_dvd (by simpa using hall i)
    · exact h.2 fun i => Int.emod_eq_zero_of_dvd (by simpa using hall i)
  ·
    have hb := List.all_eq_true.1 digitBoundCheck_eq e he
    simp only [decide_eq_true_eq] at hb
    have hg := List.all_eq_true.1 shortGenCheck_eq e he
    simp only [Bool.and_eq_true, decide_eq_true_eq] at hg
    have hcart : ∀ i k : Fin TwistTag.D4.tag.rank, |TwistTag.D4.tag.cartan k i| ≤ 2 := by decide
    have hsingle : ∀ k i : Fin TwistTag.D4.tag.rank,
        pairK k (Pi.single i 1) = TwistTag.D4.tag.cartan k i := by
      intro k i
      simp only [pairK, Pi.single_apply]
      rw [Finset.sum_eq_single i (fun j _ hj => by simp [hj]) (by simp)]
      simp
    have key : ∀ i, |pairK n0 (colOf e i)| ≤ 2 ∧ |pairK n1 (colOf e i)| ≤ 2 ∧
        |pairK n3 (colOf e i)| ≤ 2 := fun i => ⟨hb i n0, hb i n1, hb i n3⟩
    have habs : ∀ {x y : ℤ}, |x| ≤ 2 → |y| ≤ 2 → |x - y| ≤ 4 := fun hx hy => by
      rw [abs_le] at hx hy ⊢
      constructor <;> linarith [hx.1, hx.2, hy.1, hy.2]
    rcases hs with rfl | rfl
    · refine hg.1 fun i => ?_
      have hd := hall i
      rw [shortVal_eq, shortExp_eq, hsingle, hsingle, hsingle] at hd
      obtain ⟨k0, k1, k3⟩ := key i
      have hd' : q ^ 3 - 1 ∣ (pairK n3 (colOf e i) - TwistTag.D4.tag.cartan n0 i) +
          (pairK n0 (colOf e i) - TwistTag.D4.tag.cartan n1 i) * q +
          (pairK n1 (colOf e i) - TwistTag.D4.tag.cartan n3 i) * q ^ 2 := by
        have e1 : (pairK n3 (colOf e i) - TwistTag.D4.tag.cartan n0 i) +
            (pairK n0 (colOf e i) - TwistTag.D4.tag.cartan n1 i) * q +
            (pairK n1 (colOf e i) - TwistTag.D4.tag.cartan n3 i) * q ^ 2 =
            (q ^ 1 * (pairK n0 (colOf e i) + q * pairK n1 (colOf e i) +
              q ^ 2 * pairK n3 (colOf e i)) -
              (TwistTag.D4.tag.cartan n0 i + q * TwistTag.D4.tag.cartan n1 i +
                q ^ 2 * TwistTag.D4.tag.cartan n3 i)) -
            (q ^ 3 - 1) * pairK n3 (colOf e i) := by ring
        rw [e1]
        exact dvd_sub hd (dvd_mul_right _ _)
      obtain ⟨z0, z1, z2⟩ := digits_eq_zero hq7 (habs k3 (hcart i n0)) (habs k0 (hcart i n1))
        (habs k1 (hcart i n3)) hd'
      exact ⟨by linarith, by linarith, by linarith⟩
    · refine hg.2 fun i => ?_
      have hd := hall i
      rw [shortVal_eq, shortExp_eq, hsingle, hsingle, hsingle] at hd
      obtain ⟨k0, k1, k3⟩ := key i
      have hd' : q ^ 3 - 1 ∣ (pairK n1 (colOf e i) - TwistTag.D4.tag.cartan n0 i) +
          (pairK n3 (colOf e i) - TwistTag.D4.tag.cartan n1 i) * q +
          (pairK n0 (colOf e i) - TwistTag.D4.tag.cartan n3 i) * q ^ 2 := by
        have e1 : (pairK n1 (colOf e i) - TwistTag.D4.tag.cartan n0 i) +
            (pairK n3 (colOf e i) - TwistTag.D4.tag.cartan n1 i) * q +
            (pairK n0 (colOf e i) - TwistTag.D4.tag.cartan n3 i) * q ^ 2 =
            (q ^ 2 * (pairK n0 (colOf e i) + q * pairK n1 (colOf e i) +
              q ^ 2 * pairK n3 (colOf e i)) -
              (TwistTag.D4.tag.cartan n0 i + q * TwistTag.D4.tag.cartan n1 i +
                q ^ 2 * TwistTag.D4.tag.cartan n3 i)) -
            (q ^ 3 - 1) * (pairK n1 (colOf e i) + q * pairK n3 (colOf e i)) := by ring
        rw [e1]
        exact dvd_sub hd (dvd_mul_right _ _)
      obtain ⟨z0, z1, z2⟩ := digits_eq_zero hq7 (habs k1 (hcart i n0)) (habs k3 (hcart i n1))
        (habs k0 (hcart i n3)) hd'
      exact ⟨by linarith, by linarith, by linarith⟩

end CFSG.RankThree.PartTwo.Sec11.KS11Lie5Proof
