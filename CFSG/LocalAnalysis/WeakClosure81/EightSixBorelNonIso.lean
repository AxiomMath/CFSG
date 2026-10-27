module

public import CFSG.LocalAnalysis.WeakClosure81.EightFiveDefs
import CFSG.Timmesfeld.Orders.ClassicalLinear
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCatTypeDetOrders
import CFSG.GH74.GLS.Stage1.Thm3.Sec6.G2SylIASL2

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Open CFSG.Timmesfeld.Orders

variable {Y : Type} [Group Y] {m n : ℕ}

private theorem card_of_isSpGp {Y : Type} [Group Y] {m n : ℕ} (hn : 1 ≤ n) (h : IsSpGp Y m n) :
    ∃ k, m = 2 * k ∧ Nat.card Y = ordBC k (2 ^ n) := by
  obtain ⟨k, rfl, F, _, _, hcard, ⟨e⟩⟩ := h
  refine ⟨k, rfl, ?_⟩
  rw [Nat.card_congr e.toEquiv,
    CFSG.LocalAnalysis.ComponentInitial.SymplecticFlag.card_statedSp, hcard, ordBC,
    Nat.coprime_two_left.mpr (odd_two_pow_sub_one (by omega : 0 < n)), Nat.div_one, sq]

private theorem card_of_isPSUGp {Y : Type} [Group Y] {m n : ℕ} (h : IsPSUGp Y m n) :
    3 ≤ m ∧ 1 ≤ n ∧ (m, 2 ^ n) ≠ (3, 2) ∧ Nat.card Y = ordTwistedA (m - 1) (2 ^ n) := by
  have h1 := CFSG.Blueprint.LieModel.admissible h
  obtain ⟨-, hf, hm3, hne⟩ := h1
  obtain ⟨⟨-, -, -, -⟩, K, _, _, hK, ⟨e⟩⟩ :=
    CFSG.Blueprint.LieModel.statedClassicalModel_of_ne_zero (by omega) h
  refine ⟨hm3, hf, hne, ?_⟩
  rw [Nat.card_congr e.toEquiv,
    CFSG.Timmesfeld.ClassicalOrders.card_statedProj_statedSU Nat.prime_two hf hK (by omega : 2 ≤ m),
    ordTwistedA, Nat.sub_add_cancel (by omega : 1 ≤ m), mul_comm (m - 1) m]

private theorem card_of_isL2Gp {Y : Type} [Group Y] {n : ℕ} (h : IsL2Gp Y n) :
    1 ≤ n ∧ Nat.card Y = ordA 1 (2 ^ n) := by
  obtain ⟨F, _, _, hcard, ⟨e⟩⟩ := h
  have hn : 1 ≤ n := by
    have h1 : 1 < Nat.card F := Finite.one_lt_card
    rw [hcard] at h1
    exact Nat.one_le_iff_ne_zero.2 (Nat.one_lt_two_pow_iff.1 h1)
  refine ⟨hn, ?_⟩
  rw [Nat.card_congr e.toEquiv,
    CFSG.GH74.GLS.Stage1.Thm3.Sec6.G2Syl.IASL2.natCard_sl2, hcard, ordA,
    Nat.coprime_two_left.mpr (odd_two_pow_sub_one hn), Nat.div_one,
    show Finset.Icc 2 2 = {2} by decide, Finset.prod_singleton]
  norm_num

private theorem ordTwistedA_ne_ordTwistedA_one {u u' n : ℕ} (hu : 3 ≤ u) (hu' : 3 ≤ u')
    (hn : 2 ≤ n) : ordTwistedA u (2 ^ n) ≠ ordTwistedA u' (2 ^ 1) := by
  intro h
  obtain ⟨t, ht1, ht⟩ := exists_half (by omega : 2 ≤ u)
  obtain ⟨t', ht1', ht'⟩ := exists_half (by omega : 2 ≤ u')
  rcases Nat.lt_or_ge t' 2 with ht'lt | ht'2
  · have ht'1 : t' = 1 := by omega
    have hu'3 : u' = 3 := by rcases ht' with h | h <;> omega
    have h1 := profile_ordTwistedA (n := u) (g := n) (by omega : 2 ≤ u) (by omega : 1 ≤ n)
    have h2 := profile_ordTwistedA (n := u') (g := 1) (by omega : 2 ≤ u') le_rfl
    rw [h] at h1
    have hN := (h1.transfer h2).1
    have h6 : 6 ≤ u * (u + 1) / 2 := by
      have h12 : 12 ≤ u * (u + 1) := by nlinarith
      calc 6 = 12 / 2 := by norm_num
        _ ≤ u * (u + 1) / 2 := Nat.div_le_div_right h12
    rw [hu'3] at hN
    norm_num at hN
    nlinarith [hN, h6, hn]
  · have hw : zU u n (2 * (n * (2 * t + 1))) := zU_top ht ht1 (by omega : 0 < n)
    have hle : ∀ k, zU u n k → k ≤ 2 * (n * (2 * t + 1)) :=
      fun k hk => zU_le ht (by omega : 0 < n) hk
    have hw2 : 2 ≤ 2 * (n * (2 * t + 1)) := by
      have : 1 ≤ n * (2 * t + 1) := Nat.one_le_iff_ne_zero.mpr (by positivity)
      omega
    have hw6 : 2 * (n * (2 * t + 1)) ≠ 6 :=
      two_mul_ne_six (by omega : 1 ≤ n) ht1 (by rintro ⟨h1, -⟩; omega)
    obtain ⟨hw_eq, hN, -⟩ :=
      top_eq (h := profile_ordTwistedA (n := u) (g := n) (by omega : 2 ≤ u) (by omega : 1 ≤ n))
        hw hw2 hw6 hle (n := u') (g := 1) (t := t') (by omega : 2 ≤ u') le_rfl ht1' ht'
        (by rintro ⟨-, h1⟩; omega) h
    have hA : n * (2 * t + 1) = 2 * t' + 1 := by omega
    have hge : 2 * (2 * t + 1) ≤ n * (2 * t + 1) := Nat.mul_le_mul_right _ hn
    have ht'ge : 2 * t + 1 ≤ t' := by omega
    rcases ht with ht | ht <;> rcases ht' with ht' | ht'
    · rw [ht, ht', tri_even, tri_even] at hN
      have h2 : n * (t * (2 * t + 1)) = (2 * t' + 1) * t := by
        calc n * (t * (2 * t + 1)) = (n * (2 * t + 1)) * t := by ring
          _ = (2 * t' + 1) * t := by rw [hA]
      have h3 : 1 * (t' * (2 * t' + 1)) = (2 * t' + 1) * t' := by ring
      rw [h2, h3] at hN
      have : t = t' := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * t' + 1) hN
      omega
    · rw [ht, ht', tri_even, tri_odd] at hN
      have h2 : n * (t * (2 * t + 1)) = (2 * t' + 1) * t := by
        calc n * (t * (2 * t + 1)) = (n * (2 * t + 1)) * t := by ring
          _ = (2 * t' + 1) * t := by rw [hA]
      have h3 : 1 * ((2 * t' + 1) * (t' + 1)) = (2 * t' + 1) * (t' + 1) := by ring
      rw [h2, h3] at hN
      have : t = t' + 1 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * t' + 1) hN
      omega
    · rw [ht, ht', tri_odd, tri_even] at hN
      have h2 : n * ((2 * t + 1) * (t + 1)) = (2 * t' + 1) * (t + 1) := by
        calc n * ((2 * t + 1) * (t + 1)) = (n * (2 * t + 1)) * (t + 1) := by ring
          _ = (2 * t' + 1) * (t + 1) := by rw [hA]
      have h3 : 1 * (t' * (2 * t' + 1)) = (2 * t' + 1) * t' := by ring
      rw [h2, h3] at hN
      have : t + 1 = t' := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * t' + 1) hN
      omega
    · rw [ht, ht', tri_odd, tri_odd] at hN
      have h2 : n * ((2 * t + 1) * (t + 1)) = (2 * t' + 1) * (t + 1) := by
        calc n * ((2 * t + 1) * (t + 1)) = (n * (2 * t + 1)) * (t + 1) := by ring
          _ = (2 * t' + 1) * (t + 1) := by rw [hA]
      have h3 : 1 * ((2 * t' + 1) * (t' + 1)) = (2 * t' + 1) * (t' + 1) := by ring
      rw [h2, h3] at hN
      have : t + 1 = t' + 1 := Nat.eq_of_mul_eq_mul_left (by omega : 0 < 2 * t' + 1) hN
      omega

theorem not_isSpGp_one_of_isSpGp_or_isPSUGp (hm : 3 < m) (hn : 1 < n)
    (hY : IsSpGp Y m n ∨ IsPSUGp Y m n) (m' : ℕ) : ¬ IsSpGp Y m' 1 := by
  intro h
  obtain ⟨k', hk', hY'⟩ := card_of_isSpGp (n := 1) le_rfl h
  rcases hY with hSp | hU
  · obtain ⟨k, hk, hYc⟩ := card_of_isSpGp (n := n) (by omega) hSp
    have hk2 : 2 ≤ k := by omega
    rcases Nat.lt_or_ge k' 2 with hk'lt | hk'2
    · have h1 := profile_ordBC (n := k) (f := n) (by omega : 1 ≤ n)
      have h2 := profile_ordBC (n := k') (f := 1) le_rfl
      rw [← hYc] at h1
      rw [← hY'] at h2
      have hN := (h1.transfer h2).1
      have h8 : 8 ≤ n * (k * k) := by nlinarith [hk2, hn]
      have hk'k' : k' * k' ≤ 1 := by nlinarith
      omega
    · obtain ⟨-, hn1⟩ :=
        CFSG.SeitzReduction.SymplecticPilot.ordBC_eq_ordBC (n := k) (g := n) (m := k') (f := 1)
          (by omega : 2 ≤ k) (by omega : 1 ≤ n) hk'2 le_rfl (hYc.symm.trans hY')
      omega
  · obtain ⟨hm3, hf, hne, hYc⟩ := card_of_isPSUGp hU
    have hu2 : 2 ≤ m - 1 := by omega
    have hu3 : 3 ≤ m - 1 := by omega
    rcases Nat.lt_or_ge k' 2 with hk'lt | hk'2
    · have h1 := profile_ordTwistedA (n := m - 1) (g := n) hu2 (by omega : 1 ≤ n)
      have h2 := profile_ordBC (n := k') (f := 1) le_rfl
      rw [← hYc] at h1
      rw [← hY'] at h2
      have hN := (h1.transfer h2).1
      have h12 : 12 ≤ n * ((m - 1) * ((m - 1) + 1) / 2) := by
        have h6 : 6 ≤ (m - 1) * ((m - 1) + 1) / 2 := by
          have h12' : 12 ≤ (m - 1) * ((m - 1) + 1) := by nlinarith
          calc 6 = 12 / 2 := by norm_num
            _ ≤ (m - 1) * ((m - 1) + 1) / 2 := Nat.div_le_div_right h12'
        nlinarith [h6, hn]
      have hk'k' : k' * k' ≤ 1 := by nlinarith
      omega
    · exact (CFSG.SeitzReduction.SymplecticPilot.ordTwistedA_ne_ordBC
        (u := m - 1) (g := n) (m := k') (f := 1) hu2 (by omega : 1 ≤ n) hk'2 le_rfl)
        (hYc.symm.trans hY')

theorem not_isPSUGp_one_of_isSpGp_or_isPSUGp (hm : 3 < m) (hn : 1 < n)
    (hY : IsSpGp Y m n ∨ IsPSUGp Y m n) (m' : ℕ) : ¬ IsPSUGp Y m' 1 := by
  intro h
  obtain ⟨hm'3, hf', hne', hY'⟩ := card_of_isPSUGp h
  have hm'4 : 4 ≤ m' := by
    by_contra hlt
    have hm'eq : m' = 3 := by omega
    exact hne' (by rw [hm'eq]; norm_num)
  have hu' : 3 ≤ m' - 1 := by omega
  rcases hY with hSp | hU
  · obtain ⟨k, hk, hYc⟩ := card_of_isSpGp (n := n) (by omega) hSp
    exact (CFSG.SeitzReduction.SymplecticPilot.ordTwistedA_ne_ordBC
        (u := m' - 1) (g := 1) (m := k) (f := n) (by omega : 2 ≤ m' - 1) le_rfl
        (by omega : 2 ≤ k) (by omega : 1 ≤ n))
      (hY'.symm.trans hYc)
  · obtain ⟨hm3, hf, hne, hYc⟩ := card_of_isPSUGp hU
    exact ordTwistedA_ne_ordTwistedA_one (u := m - 1) (u' := m' - 1) (n := n)
      (by omega : 3 ≤ m - 1) hu' (by omega : 2 ≤ n) (hYc.symm.trans hY')

theorem not_isL2Gp_of_isSpGp_or_isPSUGp (hm : 3 < m) (hn : 1 < n)
    (hY : IsSpGp Y m n ∨ IsPSUGp Y m n) (n' : ℕ) : ¬ IsL2Gp Y n' := by
  intro h
  obtain ⟨hn', hY'⟩ := card_of_isL2Gp h
  rcases hY with hSp | hU
  · obtain ⟨k, hk, hYc⟩ := card_of_isSpGp (n := n) (by omega) hSp
    exact (CFSG.SeitzReduction.SymplecticPilot.ordA_ne_ordBC
        (r := 1) (g := n') (m := k) (f := n) le_rfl hn' (by omega : 2 ≤ k)
        (by omega : 1 ≤ n))
      (hY'.symm.trans hYc)
  · obtain ⟨hm3, hf, hne, hYc⟩ := card_of_isPSUGp hU
    exact (CFSG.Timmesfeld.Orders.ordA_ne_ordTwistedA
        (n := 1) (f := n') (u := m - 1) (g := n) le_rfl hn' (by omega : 2 ≤ m - 1)
        (by omega : 1 ≤ n))
      (hY'.symm.trans hYc)

end CFSG.LocalAnalysis.WeakClosure81

end
