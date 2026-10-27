module

public import CFSG.Timmesfeld.Orders.ExceptionalWeylData

public noncomputable section

namespace CFSG.RankThree.PartOne.KFU

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.Timmesfeld.ExceptionalOrders

@[expose] def f4cA1 : OrbitCert .F4 where
  lam := 34951
  pts := [
    34966, 35447]
  parents := [
    1]
  table := [
    256, 0]
  lens := [
    0, 1]

@[expose] def f4cA2 : OrbitCert .F4 where
  lam := 30856
  pts := [
    27016, 30616, 31097, 34697]
  parents := [
    2, 17, 34]
  table := [
    65536, 512, 196864, 131840]
  lens := [
    0, 1, 2, 3]

@[expose] def f4cA3 : OrbitCert .F4 where
  lam := 34679
  pts := [
    39047, 31111, 34711, 35192, 38792, 30856]
  parents := [
    3, 18, 33, 50, 67]
  table := [
    16777216, 131328, 33620736, 50594304, 84083712, 67437824]
  lens := [
    0, 1, 2, 3, 4, 5]

@[expose] def f4cB3 : OrbitCert .F4 where
  lam := 39048
  pts := [
    42888, 27016]
  parents := [
    3]
  table := [
    16777216, 257]
  lens := [
    0, 1]

@[expose] def f4cC2 : OrbitCert .F4 where
  lam := 30856
  pts := [
    27016, 30616]
  parents := [
    2]
  table := [
    65536, 1]
  lens := [
    0, 1]

@[expose] def f4cC3 : OrbitCert .F4 where
  lam := 43400
  pts := [
    47224, 23416, 34216]
  parents := [
    3, 18]
  table := [
    16777216, 131073, 33619970]
  lens := [
    0, 1, 2]

@[expose] def f4ChainC3 : List (ChainStep .F4) := [
  ⟨14, 6, f4cA3, [(6, 1)]⟩,
  ⟨6, 2, f4cA2, [(4, 1)]⟩,
  ⟨2, 0, f4cA1, [(2, 1)]⟩]

@[expose] def f4ChainA2A1 : List (ChainStep .F4) := [
  ⟨11, 3, f4cB3, [(2, 1)]⟩,
  ⟨3, 1, f4Cert2, [(3, 1)]⟩,
  ⟨1, 0, f4Cert1, [(2, 1)]⟩]

@[expose] def f4ChainA1A2 : List (ChainStep .F4) := [
  ⟨13, 5, f4cC3, [(3, 1)]⟩,
  ⟨5, 1, f4cC2, [(2, 1)]⟩,
  ⟨1, 0, f4Cert1, [(2, 1)]⟩]

@[expose] def f4ChainB3 : List (ChainStep .F4) := [
  ⟨7, 3, f4Cert3, [(4, 1), (2, 3)]⟩,
  ⟨3, 1, f4Cert2, [(3, 1)]⟩,
  ⟨1, 0, f4Cert1, [(2, 1)]⟩]

theorem f4ChainC3_check : chainCheck f4ChainC3 14 = true := by
  decide +kernel

theorem f4ChainA2A1_check : chainCheck f4ChainA2A1 11 = true := by
  decide +kernel

theorem f4ChainA1A2_check : chainCheck f4ChainA1A2 13 = true := by
  decide +kernel

theorem f4ChainB3_check : chainCheck f4ChainB3 7 = true := by
  decide +kernel

variable [Fintype (WeylGroup .F4)]

theorem parabolicSum_F4_two_C3 :
    parabolicSum .F4 (maskSet .F4 14) 2 = 2835 := by
  rw [parabolicSum_eq_of_chainCheck 2 _ _ f4ChainC3_check]
  simp [f4ChainC3, ChainStep.value, geomSum, Finset.sum_range_succ]

theorem parabolicSum_F4_two_A2A1 :
    parabolicSum .F4 (maskSet .F4 11) 2 = 63 := by
  rw [parabolicSum_eq_of_chainCheck 2 _ _ f4ChainA2A1_check]
  simp [f4ChainA2A1, ChainStep.value, geomSum, Finset.sum_range_succ]

theorem parabolicSum_F4_two_A1A2 :
    parabolicSum .F4 (maskSet .F4 13) 2 = 63 := by
  rw [parabolicSum_eq_of_chainCheck 2 _ _ f4ChainA1A2_check]
  simp [f4ChainA1A2, ChainStep.value, geomSum, Finset.sum_range_succ]

theorem parabolicSum_F4_two_B3 :
    parabolicSum .F4 (maskSet .F4 7) 2 = 2835 := by
  rw [parabolicSum_eq_of_chainCheck 2 _ _ f4ChainB3_check]
  simp [f4ChainB3, ChainStep.value, geomSum, Finset.sum_range_succ]

omit [Fintype (WeylGroup .F4)] in
theorem not_sq_dvd_two_values {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {n : ℕ}
    (hn : n = 2835 ∨ n = 63) : ¬ p ^ 2 ∣ n := by
  intro h
  have hn0 : 0 < n := by rcases hn with rfl | rfl <;> norm_num
  have hle : p ^ 2 ≤ n := Nat.le_of_dvd hn0 h
  have hp53 : p ≤ 53 := by
    by_contra hc
    push Not at hc
    have : 54 ^ 2 ≤ p ^ 2 := Nat.pow_le_pow_left hc 2
    rcases hn with rfl | rfl <;> omega
  interval_cases p <;>
    first
      | (norm_num at hp; done)
      | (rcases hn with rfl | rfl <;> norm_num at h)

theorem not_sq_dvd_parabolicSum_F4_two {p : ℕ} (hp : p.Prime) (hp5 : 5 ≤ p) {m : ℕ}
    (hm : m = 7 ∨ m = 11 ∨ m = 13 ∨ m = 14) : ¬ p ^ 2 ∣ parabolicSum .F4 (maskSet .F4 m) 2 := by
  rcases hm with rfl | rfl | rfl | rfl
  · rw [parabolicSum_F4_two_B3]
    exact not_sq_dvd_two_values hp hp5 (Or.inl rfl)
  · rw [parabolicSum_F4_two_A2A1]
    exact not_sq_dvd_two_values hp hp5 (Or.inr rfl)
  · rw [parabolicSum_F4_two_A1A2]
    exact not_sq_dvd_two_values hp hp5 (Or.inr rfl)
  · rw [parabolicSum_F4_two_C3]
    exact not_sq_dvd_two_values hp hp5 (Or.inl rfl)

end CFSG.RankThree.PartOne.KFU
