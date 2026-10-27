module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatTypeDetOrders
import CFSG.LocalAnalysis.SeitzReduction.UnitaryPilotCatTypeDet

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.QuasithinUnique Subgroup

private theorem wc85un_ordBC_two_pow (k n : ℕ) (hn : 1 ≤ n) :
    ordBC k (2 ^ n) = 2 ^ (n * k ^ 2) * ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i * n) - 1) := by
  have hgcd : Nat.gcd 2 (2 ^ n - 1) = 1 :=
    Nat.coprime_two_left.mpr (CFSG.Timmesfeld.Orders.odd_two_pow_sub_one hn)
  rw [ordBC, hgcd, Nat.div_one]
  have h1 : (2 ^ n) ^ (k * k) = 2 ^ (n * k ^ 2) := by
    rw [← pow_mul, show n * (k * k) = n * k ^ 2 by ring]
  have h2 : (∏ i ∈ Finset.Icc 1 k, ((2 ^ n) ^ (2 * i) - 1)) =
      ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i * n) - 1) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, show n * (2 * i) = 2 * i * n by ring]
  rw [h1, h2]

private theorem wc85un_card_of_isSpGp {Y : Type} [Group Y] {m n : ℕ} (hm : 3 < m)
    (h : IsSpGp Y m n) :
    ∃ k : ℕ, 2 ≤ k ∧ 1 ≤ n ∧ m = 2 * k ∧ Nat.card Y = ordBC k (2 ^ n) := by
  obtain ⟨k, hk, F, hFld, hFin, hFcard, ⟨e⟩⟩ := h
  haveI := hFld
  haveI := hFin
  have hn1 : 1 ≤ n := by
    have h2 : 1 < 2 ^ n := by rw [← hFcard]; exact Finite.one_lt_card
    rcases Nat.eq_zero_or_pos n with rfl | h
    · simp at h2
    · exact h
  have hk2 : 2 ≤ k := by omega
  refine ⟨k, hk2, hn1, hk, ?_⟩
  rw [Nat.card_congr e.toEquiv,
    @CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp F hFld hFin k, hFcard,
    wc85un_ordBC_two_pow k n hn1]
  have h1 : (2 ^ n) ^ (k ^ 2) = 2 ^ (n * k ^ 2) := by rw [← pow_mul]
  have h2 : (∏ j ∈ Finset.Icc 1 k, ((2 ^ n) ^ (2 * j) - 1)) =
      ∏ i ∈ Finset.Icc 1 k, (2 ^ (2 * i * n) - 1) := by
    apply Finset.prod_congr rfl
    intro i _
    rw [← pow_mul, show n * (2 * i) = 2 * i * n by ring]
  rw [h1, h2]

private theorem wc85un_card_of_isPSUGp {Y : Type} [Group Y] {m n : ℕ} (h : IsPSUGp Y m n) :
    3 ≤ m ∧ 1 ≤ n ∧ Nat.card Y = ordTwistedA (m - 1) (2 ^ n) := by
  have h1 := CFSG.Blueprint.LieModel.admissible h
  obtain ⟨-, hf, hm3, -⟩ := h1
  obtain ⟨⟨-, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega) h
  refine ⟨hm3, hf, ?_⟩
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hf hK
      (by omega : 2 ≤ m),
    ordTwistedA, Nat.sub_add_cancel (by omega : 1 ≤ m), mul_comm (m - 1) m]

theorem spPSU_unique {Y : Type} [Group Y] {m n m' n' : ℕ} (hm : 3 < m) (hm' : 3 < m')
    (h : IsSpGp Y m n ∨ IsPSUGp Y m n) (h' : IsSpGp Y m' n' ∨ IsPSUGp Y m' n') :
    m = m' ∧ n = n' ∧ ((IsSpGp Y m n ∧ IsSpGp Y m' n') ∨ (IsPSUGp Y m n ∧ IsPSUGp Y m' n')) := by
  rcases h with hSp | hPSU <;> rcases h' with hSp' | hPSU'
  · obtain ⟨k, hk2, hn1, hk, hcard⟩ := wc85un_card_of_isSpGp hm hSp
    obtain ⟨k', hk2', hn1', hk', hcard'⟩ := wc85un_card_of_isSpGp hm' hSp'
    have heq : ordBC k (2 ^ n) = ordBC k' (2 ^ n') := hcard.symm.trans hcard'
    obtain ⟨hkk, hnn⟩ :=
      CFSG.SeitzReduction.SymplecticPilot.ordBC_eq_ordBC hk2 hn1 hk2' hn1' heq
    exact ⟨by omega, hnn, Or.inl ⟨hSp, hSp'⟩⟩
  · obtain ⟨k, hk2, hn1, -, hcard⟩ := wc85un_card_of_isSpGp hm hSp
    obtain ⟨-, hn1', hcard'⟩ := wc85un_card_of_isPSUGp hPSU'
    have heq : ordTwistedA (m' - 1) (2 ^ n') = ordBC k (2 ^ n) := hcard'.symm.trans hcard
    exact absurd heq (CFSG.SeitzReduction.SymplecticPilot.ordTwistedA_ne_ordBC
      (by omega : 2 ≤ m' - 1) hn1' hk2 hn1)
  · obtain ⟨-, hn1, hcard⟩ := wc85un_card_of_isPSUGp hPSU
    obtain ⟨k', hk2', hn1', -, hcard'⟩ := wc85un_card_of_isSpGp hm' hSp'
    have heq : ordTwistedA (m - 1) (2 ^ n) = ordBC k' (2 ^ n') := hcard.symm.trans hcard'
    exact absurd heq (CFSG.SeitzReduction.SymplecticPilot.ordTwistedA_ne_ordBC
      (by omega : 2 ≤ m - 1) hn1 hk2' hn1')
  · obtain ⟨-, hn1, hcard⟩ := wc85un_card_of_isPSUGp hPSU
    obtain ⟨-, hn1', hcard'⟩ := wc85un_card_of_isPSUGp hPSU'
    have heq : ordTwistedA (m - 1) (2 ^ n) = ordTwistedA (m' - 1) (2 ^ n') :=
      hcard.symm.trans hcard'
    obtain ⟨hmm, hnn⟩ := CFSG.SeitzReduction.UnitaryPilot.ordTwistedA_inj_two_pow
      (by omega : 2 ≤ m - 1) (by omega : 2 ≤ m' - 1) hn1 hn1'
      (by
        intro hh
        have h1 : m - 1 = 2 := by simpa using congrArg Prod.fst hh
        omega : (m - 1, n) ≠ (2, 1))
      (by
        intro hh
        have h1 : m' - 1 = 2 := by simpa using congrArg Prod.fst hh
        omega : (m' - 1, n') ≠ (2, 1)) heq
    exact ⟨by omega, hnn, Or.inr ⟨hPSU, hPSU'⟩⟩

end CFSG.LocalAnalysis.WeakClosure81

end
