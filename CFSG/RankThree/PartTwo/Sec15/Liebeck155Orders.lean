module

public import CFSG.RankThree.PartTwo.Sec14.Item14ListStatements
import CFSG.Adapters.StatedClassicalSmallOrders
import CFSG.RankThree.PartTwo.KFacts.KS14Orders

public section

namespace CFSG.RankThree.PartTwo.Sec15.Liebeck155

open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.Assembly.RankThreeEven (projSL projSU)
open CFSG.RankThree.PartTwo.Sec14 (IsLThreeEpsAt)
open CFSG.RankThree.PartTwo.KFacts.KS14 (card_alternatingGroup_five_seven_ten card_nativeM12
  card_nativeM22 card_projSL_three_mul_gcd card_projSU_three_mul_gcd)

private theorem two_pow_card_ne (j : ℕ) {M : ℕ}
    (hM : M = 2520 ∨ M = 1814400 ∨ M = 443520 ∨ M = 95040) :
    2 ^ j * ((2 ^ j) ^ 2 - 1) ≠ M := by
  intro h
  by_cases hj : j ≤ 7
  · interval_cases j <;> rcases hM with rfl | rfl | rfl | rfl <;> norm_num at h
  · have h8 : 2 ^ 8 ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) (by omega)
    have h9 : 2 ^ 8 * ((2 ^ 8) ^ 2 - 1) ≤ 2 ^ j * ((2 ^ j) ^ 2 - 1) :=
      Nat.mul_le_mul h8 (Nat.sub_le_sub_right (Nat.pow_le_pow_left h8 2) 1)
    norm_num at h9
    rcases hM with rfl | rfl | rfl | rfl <;> omega

private theorem pow_three_le_of_dvd {j p n : ℕ} (hj : 1 ≤ j) (hp : p.Prime) (hn : 1 ≤ n)
    (h : (p ^ n) ^ 3 ∣ 2 ^ j * ((2 ^ j) ^ 2 - 1)) : (p ^ n) ^ 3 ≤ 2 ^ j + 1 := by
  have hq : 2 ≤ 2 ^ j := by
    calc 2 = 2 ^ 1 := by norm_num
      _ ≤ 2 ^ j := Nat.pow_le_pow_right (by norm_num) hj
  have hev : Even (2 ^ j) := Nat.even_pow.mpr ⟨even_two, by omega⟩
  have hodd1 : Odd (2 ^ j - 1) := Nat.Even.sub_odd (by omega) hev odd_one
  have hodd : Odd ((2 ^ j) ^ 2 - 1) :=
    Nat.Even.sub_odd (Nat.one_le_pow _ _ (by omega)) (Nat.even_pow.mpr ⟨hev, by norm_num⟩) odd_one
  rcases eq_or_ne p 2 with rfl | hp2
  · have hcop : Nat.Coprime ((2 ^ n) ^ 3) ((2 ^ j) ^ 2 - 1) :=
      ((Nat.coprime_two_left.mpr hodd).pow_left n).pow_left 3
    have h2 : (2 ^ n) ^ 3 ∣ 2 ^ j := hcop.dvd_of_dvd_mul_right h
    exact (Nat.le_of_dvd (by positivity) h2).trans (Nat.le_succ _)
  · have hcop : Nat.Coprime ((p ^ n) ^ 3) (2 ^ j) :=
      (((Nat.coprime_primes hp Nat.prime_two).mpr hp2).pow n j).pow_left 3
    have h2 : (p ^ n) ^ 3 ∣ (2 ^ j) ^ 2 - 1 := hcop.dvd_of_dvd_mul_left h
    have h3 : (2 ^ j) ^ 2 - 1 = (2 ^ j + 1) * (2 ^ j - 1) := by
      simpa using Nat.sq_sub_sq (2 ^ j) 1
    rw [h3] at h2
    have hcop2 : Nat.Coprime (2 ^ j + 1) (2 ^ j - 1) := by
      have h4 : 2 ^ j + 1 = 2 + (2 ^ j - 1) := by omega
      rw [h4, Nat.coprime_add_self_left]
      exact Nat.coprime_two_left.mpr hodd1
    have hpp : IsPrimePow ((p ^ n) ^ 3) := (hp.isPrimePow.pow (by omega)).pow (by norm_num)
    rcases (hcop2.isPrimePow_dvd_mul hpp).mp h2 with h5 | h5
    · exact Nat.le_of_dvd (by omega) h5
    · exact (Nat.le_of_dvd (by omega) h5).trans (by omega)

private theorem false_of_size {q r g c : ℕ} (hr : 2 ≤ r) (hq : r ^ 3 ≤ q + 1) (hg : 1 ≤ g)
    (hc : c ≤ r ^ 3 + 1) (h : q * (q ^ 2 - 1) * g = r ^ 3 * ((r ^ 2 - 1) * c)) : False := by
  have hR8 : 8 ≤ r ^ 3 := by
    calc 8 = 2 ^ 3 := by norm_num
      _ ≤ r ^ 3 := Nat.pow_le_pow_left hr 3
  have hRS : 2 * r ^ 2 ≤ r ^ 3 :=
    calc 2 * r ^ 2 ≤ r * r ^ 2 := Nat.mul_le_mul_right _ hr
      _ = r ^ 3 := by ring
  have hS : 4 ≤ r ^ 2 := by
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ r ^ 2 := Nat.pow_le_pow_left hr 2
  generalize r ^ 3 = R at *
  obtain ⟨S1, hS1⟩ : ∃ S1, r ^ 2 = S1 + 1 := ⟨r ^ 2 - 1, by omega⟩
  obtain ⟨u, rfl⟩ : ∃ u, q = u + 1 := ⟨q - 1, by omega⟩
  have hu : (u + 1) ^ 2 - 1 = u * (u + 2) := Nat.sub_eq_of_eq_add (by ring)
  rw [hu, hS1, Nat.add_sub_cancel] at h
  rw [hS1] at hRS
  obtain ⟨w, rfl⟩ : ∃ w, R = w + 2 := ⟨R - 2, by omega⟩
  have hwu : w ≤ u := by omega
  have h1 : (w + 1) * (w * (w + 2)) ≤ (u + 1) * (u * (u + 2)) :=
    Nat.mul_le_mul (by omega) (Nat.mul_le_mul hwu (by omega))
  have h2 : (u + 1) * (u * (u + 2)) ≤ (u + 1) * (u * (u + 2)) * g := Nat.le_mul_of_pos_right _ hg
  have h3 : (w + 2) * (S1 * c) ≤ (w + 2) * (S1 * (w + 3)) :=
    Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ (by omega))
  have h4 : S1 * (w + 3) < (w + 1) * w := by nlinarith
  have h5 : (w + 2) * (S1 * (w + 3)) < (w + 2) * ((w + 1) * w) :=
    Nat.mul_lt_mul_of_pos_left h4 (by omega)
  nlinarith

private theorem false_of_card_360 {r g c : ℕ} (hr : 2 ≤ r) (hg1 : 1 ≤ g) (hg3 : g ≤ 3)
    (hc1 : r ^ 3 - 1 ≤ c) (hc2 : c ≤ r ^ 3 + 1)
    (h : 360 * g = r ^ 3 * ((r ^ 2 - 1) * c)) : False := by
  rcases Nat.lt_or_ge r 3 with h3 | h3
  · obtain rfl : r = 2 := by omega
    norm_num at h hc2
    omega
  · have h2 : 27 ≤ r ^ 3 := by
      calc 27 = 3 ^ 3 := by norm_num
        _ ≤ r ^ 3 := Nat.pow_le_pow_left h3 3
    have h4 : 9 ≤ r ^ 2 := by
      calc 9 = 3 ^ 2 := by norm_num
        _ ≤ r ^ 2 := Nat.pow_le_pow_left h3 2
    have h5 : 27 * ((9 - 1) * (27 - 1)) ≤ r ^ 3 * ((r ^ 2 - 1) * c) :=
      Nat.mul_le_mul h2
        (Nat.mul_le_mul (Nat.sub_le_sub_right h4 1) ((Nat.sub_le_sub_right h2 1).trans hc1))
    omega

private def OrderCases (N : ℕ) : Prop :=
  (∃ j : ℕ, 3 ≤ j ∧ N = 2 ^ j * ((2 ^ j) ^ 2 - 1)) ∨ N = 360

private theorem orderCases_of_model {K : Type} [Group K]
    (h : (∃ j : ℕ, 3 ≤ j ∧ StatedClassicalModel K .PSL 2 2 j) ∨
      StatedClassicalModel K .PSL 2 3 2) : OrderCases (Nat.card K) := by
  rcases h with ⟨j, hj, hK⟩ | hK
  · exact Or.inl ⟨j, hj, CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_two hK⟩
  · exact Or.inr (CFSG.Open.StatedAPI.card_of_statedClassicalModel_psl_two_nine hK)

private theorem false_of_orderCases {N p n g c : ℕ} (hN : OrderCases N) (hp : p.Prime)
    (hn : 1 ≤ n) (hg : Nat.Coprime (p ^ n) g) (hg3 : g ≤ 3) (hc1 : (p ^ n) ^ 3 - 1 ≤ c)
    (hc2 : c ≤ (p ^ n) ^ 3 + 1) (h : N * g = (p ^ n) ^ 3 * (((p ^ n) ^ 2 - 1) * c)) : False := by
  have hr2 : 2 ≤ p ^ n := (hp.two_le).trans (Nat.le_self_pow (by omega) p)
  have hg1 : 1 ≤ g := by
    rcases Nat.eq_zero_or_pos g with rfl | hg0
    · rw [Nat.coprime_zero_right] at hg
      omega
    · exact hg0
  rcases hN with ⟨j, hj, rfl⟩ | rfl
  · have hdvd : (p ^ n) ^ 3 ∣ 2 ^ j * ((2 ^ j) ^ 2 - 1) :=
      (hg.pow_left 3).dvd_of_dvd_mul_right (Dvd.intro _ h.symm)
    exact false_of_size hr2 (pow_three_le_of_dvd (by omega) hp hn hdvd) hg1 hc2 h
  · exact false_of_card_360 hr2 hg1 hg3 hc1 hc2 h

private theorem isEmpty_mulEquiv_of_card {K X : Type} [Group K] [Group X] {M : ℕ}
    (hX : Nat.card X = M) (hM : M = 2520 ∨ M = 1814400 ∨ M = 443520 ∨ M = 95040)
    (hK : OrderCases (Nat.card K)) : IsEmpty (K ≃* X) := by
  refine ⟨fun e => ?_⟩
  have h : Nat.card K = M := by rw [← hX]; exact Nat.card_congr e.toEquiv
  rcases hK with ⟨j, -, hj⟩ | h360
  · exact two_pow_card_ne j hM (hj ▸ h)
  · rcases hM with rfl | rfl | rfl | rfl <;> omega

private theorem isEmpty_mulEquiv_projSL_three {K : Type} [Group K]
    (hK : OrderCases (Nat.card K)) (F : Type) [Field F] [Finite F] :
    IsEmpty (K ≃* projSL 3 F) := by
  refine ⟨fun e => ?_⟩
  have hc := card_projSL_three_mul_gcd F
  rw [← Nat.card_congr e.toEquiv] at hc
  obtain ⟨p, n, hp, hn, hpn⟩ : IsPrimePow (Nat.card F) := by
    have := Fintype.ofFinite F
    rw [Nat.card_eq_fintype_card]
    exact FiniteField.isPrimePow_card F
  rw [← hpn] at hc
  have hr2 : 2 ≤ p ^ n :=
    ((Nat.prime_iff.mpr hp).two_le).trans (Nat.le_self_pow (by omega) p)
  refine false_of_orderCases hK (Nat.prime_iff.mpr hp) hn ?_ (Nat.gcd_le_left _ (by norm_num))
    le_rfl (by omega) hc
  exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 _)
    ((Nat.coprime_self_sub_right (by omega)).mpr (Nat.coprime_one_right _))

private theorem isEmpty_mulEquiv_projSU_three {K : Type} [Group K]
    (hK : OrderCases (Nat.card K)) (p f : ℕ) [Fact p.Prime] (hf : 1 ≤ f) :
    IsEmpty (K ≃* projSU 3 p f) := by
  refine ⟨fun e => ?_⟩
  have hc := card_projSU_three_mul_gcd p f hf
  rw [← Nat.card_congr e.toEquiv] at hc
  refine false_of_orderCases hK Fact.out hf ?_ (Nat.gcd_le_left _ (by norm_num))
    (by omega) le_rfl hc
  exact Nat.Coprime.coprime_dvd_right (Nat.gcd_dvd_right 3 _)
    (Nat.coprime_self_add_right.mpr (Nat.coprime_one_right _))

theorem isEmpty_mulEquiv_alternatingGroup_seven_of_model {K : Type} [Group K]
    (h : (∃ j : ℕ, 3 ≤ j ∧ StatedClassicalModel K .PSL 2 2 j) ∨
      StatedClassicalModel K .PSL 2 3 2) : IsEmpty (K ≃* alternatingGroup (Fin 7)) :=
  isEmpty_mulEquiv_of_card card_alternatingGroup_five_seven_ten.2.1 (by norm_num)
    (orderCases_of_model h)

theorem isEmpty_mulEquiv_alternatingGroup_ten_of_model {K : Type} [Group K]
    (h : (∃ j : ℕ, 3 ≤ j ∧ StatedClassicalModel K .PSL 2 2 j) ∨
      StatedClassicalModel K .PSL 2 3 2) : IsEmpty (K ≃* alternatingGroup (Fin 10)) :=
  isEmpty_mulEquiv_of_card card_alternatingGroup_five_seven_ten.2.2 (by norm_num)
    (orderCases_of_model h)

theorem isEmpty_mulEquiv_M22_of_model {K : Type} [Group K]
    (h : (∃ j : ℕ, 3 ≤ j ∧ StatedClassicalModel K .PSL 2 2 j) ∨
      StatedClassicalModel K .PSL 2 3 2) :
    IsEmpty (K ≃* CFSG.Blueprint.NativeSporadic.M22) :=
  isEmpty_mulEquiv_of_card card_nativeM22 (by norm_num) (orderCases_of_model h)

theorem isEmpty_mulEquiv_M12_of_model {K : Type} [Group K]
    (h : (∃ j : ℕ, 3 ≤ j ∧ StatedClassicalModel K .PSL 2 2 j) ∨
      StatedClassicalModel K .PSL 2 3 2) :
    IsEmpty (K ≃* CFSG.Blueprint.NativeSporadic.M12) :=
  isEmpty_mulEquiv_of_card card_nativeM12 (by norm_num) (orderCases_of_model h)

theorem not_isLThreeEpsAt_of_model {K : Type} [Group K]
    (h : (∃ j : ℕ, 3 ≤ j ∧ StatedClassicalModel K .PSL 2 2 j) ∨
      StatedClassicalModel K .PSL 2 3 2) (p f : ℕ) [Fact p.Prime] : ¬ IsLThreeEpsAt K p f := by
  rintro (⟨⟨e⟩⟩ | ⟨hq, ⟨e⟩⟩)
  · exact (isEmpty_mulEquiv_projSL_three (orderCases_of_model h) (GaloisField p f)).false e
  · have hf : 1 ≤ f := by
      rcases Nat.eq_zero_or_pos f with rfl | hf
      · simp at hq
      · exact hf
    exact (isEmpty_mulEquiv_projSU_three (orderCases_of_model h) p f hf).false e

theorem not_isoLThreePi_of_model {K : Type} [Group K]
    (h : (∃ j : ℕ, 3 ≤ j ∧ StatedClassicalModel K .PSL 2 2 j) ∨
      StatedClassicalModel K .PSL 2 3 2) (p e : ℕ) [Fact p.Prime] :
    ¬ Sec4.IsoLThreePi K p e := by
  rintro (⟨-, ⟨φ⟩⟩ | ⟨hq, ⟨φ⟩⟩)
  · exact (isEmpty_mulEquiv_projSL_three (orderCases_of_model h) (GaloisField p e)).false φ
  · have he : 1 ≤ e := by
      rcases Nat.eq_zero_or_pos e with rfl | he
      · simp at hq
      · exact he
    exact (isEmpty_mulEquiv_projSU_three (orderCases_of_model h) p e he).false φ

@[nolint unusedArguments]
theorem simpleOrderFacts_holds :
    ∀ (K : Type) [Group K] [Finite K], IsSimpleGroup K →
      ((∃ j : ℕ, 3 ≤ j ∧ StatedClassicalModel K .PSL 2 2 j) ∨ StatedClassicalModel K .PSL 2 3 2) →
      IsEmpty (K ≃* alternatingGroup (Fin 7)) ∧ IsEmpty (K ≃* alternatingGroup (Fin 10)) ∧
      (∀ (p f : ℕ) [Fact p.Prime], ¬ IsLThreeEpsAt K p f) ∧
      (∀ (p e : ℕ) [Fact p.Prime], ¬ Sec4.IsoLThreePi K p e) ∧
      IsEmpty (K ≃* CFSG.Blueprint.NativeSporadic.M22) ∧
      IsEmpty (K ≃* CFSG.Blueprint.NativeSporadic.M12) := by
  intro K _ _ _ h
  exact ⟨isEmpty_mulEquiv_alternatingGroup_seven_of_model h,
    isEmpty_mulEquiv_alternatingGroup_ten_of_model h, fun p f _ => not_isLThreeEpsAt_of_model h p f,
    fun p e _ => not_isoLThreePi_of_model h p e, isEmpty_mulEquiv_M22_of_model h,
    isEmpty_mulEquiv_M12_of_model h⟩

end CFSG.RankThree.PartTwo.Sec15.Liebeck155
