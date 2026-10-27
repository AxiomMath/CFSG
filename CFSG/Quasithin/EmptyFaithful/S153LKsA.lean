module

public import CFSG.Quasithin.EmptyFaithful.S153LKsA2
public import CFSG.Quasithin.EmptyFaithful.S153LKsDef
import CFSG.Timmesfeld.Orders.Classical
import CFSG.LieType.Ree.SuzukiOrder

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace S153L

private theorem ksOrd_gcd_three_add {n : ℕ} (hodd : Odd n) : Nat.gcd 3 (2 ^ n + 1) = 3 :=
  Nat.gcd_eq_left (ks_three_dvd_two_pow_add_one hodd)

private theorem ksOrd_gcd_three_sub {n : ℕ} (hodd : Odd n) : Nat.gcd 3 (2 ^ n - 1) = 1 := by
  have h3 := ks_three_dvd_two_pow_add_one hodd
  have h1 : 1 ≤ 2 ^ n := Nat.one_le_two_pow
  have hnd : ¬ 3 ∣ 2 ^ n - 1 := by omega
  exact (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mpr hnd

theorem ksOrd_card_of_shape {Y : Type} [Group Y] {Ks : Subgroup Y}
    {n : ℕ} (hn : 3 ≤ n) (hodd : Odd n) (h : Shape15365 n Ks) : KsOrd (Nat.card ↥Ks) := by
  have hn0 : 0 < n := by omega
  rcases h with h | h | h | h | h
  ·
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
    refine ⟨n, hn, hodd, Or.inl ?_⟩
    rw [hc]
    have hg : Nat.gcd (1 + 1) (2 ^ n - 1) = 1 :=
      Nat.coprime_two_left.mpr (ks_odd_two_pow_sub_one hn0)
    unfold ordA
    rw [show (2 : ℕ) - 1 = 1 from rfl, show Finset.Icc 2 (1 + 1) = {2} by decide,
      Finset.prod_singleton, hg, Nat.div_one, show 1 * (1 + 1) / 2 = 1 from rfl, pow_one,
      pow_mul']
  ·
    obtain ⟨-, a, ha, K, _, _, hf, hK, ⟨e⟩⟩ := h
    have hK' : Nat.card K = 2 ^ (2 * a + 1) := by rw [← hf]; exact hK
    refine ⟨n, hn, hodd, Or.inr (Or.inl ?_)⟩
    rw [Nat.card_congr e.toEquiv, CFSG.LieType.Ree.suzuki_order hK', ← hf]
    ring
  ·
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h).2.1 rfl
    refine ⟨n, hn, hodd, Or.inr (Or.inr (Or.inl ?_))⟩
    rw [hc]
    unfold ordTwistedA
    have e2 : ((((2 ^ n : ℕ) : ℤ)) ^ 2 - (-1) ^ 2).toNat = 2 ^ (2 * n) - 1 := by
      have h1 : 1 ≤ 2 ^ (2 * n) := Nat.one_le_two_pow
      have h2 : ((((2 ^ n : ℕ) : ℤ)) ^ 2 - (-1) ^ 2) = ((2 ^ (2 * n) - 1 : ℕ) : ℤ) := by
        push_cast [Nat.cast_sub h1]
        ring
      rw [h2, Int.toNat_natCast]
    have e3 : ((((2 ^ n : ℕ) : ℤ)) ^ 3 - (-1) ^ 3).toNat = 2 ^ (3 * n) + 1 := by
      have h2 : ((((2 ^ n : ℕ) : ℤ)) ^ 3 - (-1) ^ 3) = ((2 ^ (3 * n) + 1 : ℕ) : ℤ) := by
        push_cast
        ring
      rw [h2, Int.toNat_natCast]
    rw [show (3 - 1 : ℕ) = 2 from rfl, show Finset.Icc 2 (2 + 1) = {2, 3} by decide,
      Finset.prod_pair (by norm_num), e2, e3, show 2 + 1 = 3 from rfl, ksOrd_gcd_three_add hodd,
      show 2 * (2 + 1) / 2 = 3 from rfl]
    congr 1
    ring
  ·
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h).1 rfl
    refine ⟨n, hn, hodd, Or.inr (Or.inr (Or.inr (Or.inl ?_)))⟩
    rw [hc]
    unfold ordA
    rw [show (3 - 1 : ℕ) = 2 from rfl, show Finset.Icc 2 (2 + 1) = {2, 3} by decide,
      Finset.prod_pair (by norm_num), show 2 + 1 = 3 from rfl, ksOrd_gcd_three_sub hodd,
      Nat.div_one, show 2 * (3 : ℕ) / 2 = 3 from rfl]
    ring_nf
  ·
    have h' : IsPSp4 2 n ↥Ks := by
      simpa [E2.IsSp4Prime, show n ≠ 1 by omega] using h
    have hc := (CFSG.Timmesfeld.card_statedClassicalModel_two h').2.2.1 rfl
    refine ⟨n, hn, hodd, Or.inr (Or.inr (Or.inr (Or.inr ?_)))⟩
    rw [hc]
    have hg : Nat.gcd 2 (2 ^ n - 1) = 1 :=
      Nat.coprime_two_left.mpr (ks_odd_two_pow_sub_one hn0)
    unfold ordBC
    rw [show Finset.Icc 1 2 = {1, 2} by decide, Finset.prod_pair (by norm_num), hg, Nat.div_one]
    ring_nf

private theorem ksOrd_isSimpleGroup_of_shape {Y : Type} [Group Y] {Ks : Subgroup Y} {n : ℕ}
    (hn : 3 ≤ n) (h : Shape15365 n Ks) : IsSimpleGroup ↥Ks := by
  rcases h with h | h | h | h | h
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 2 2 n h).2
  · exact (CFSG.LieType.Simplicity.fam_2b2_simplicity _ 2 n h).2
  · exact (CFSG.ClassicalGroups.Unitary.fam_PSU_simplicity _ 3 2 n h).2
  · exact (CFSG.LieType.Simplicity.fam_PSL_simplicity _ 3 2 n h).2
  · have h' : IsPSp4 2 n ↥Ks := by
      simpa [E2.IsSp4Prime, show n ≠ 1 by omega] using h
    exact CFSG.ClassicalGroups.Symplectic.isSimpleGroup_of_statedClassicalModel_PSp _ 2 2 n h'

theorem KsCover.card_data_eq {L : Type} [Group L] [Finite L]
    (h : KsCover L) : ∃ N : ℕ, KsOrd N ∧ Nat.card L = N * Nat.card ↥(Subgroup.center L) := by
  obtain ⟨Y, _, Ks, n, σ, hn, hodd, hKs, hs, hz⟩ := h
  have hord := ksOrd_card_of_shape hn hodd hKs
  have hsimple := ksOrd_isSimpleGroup_of_shape hn hKs
  have hcen : Subgroup.center ↥Ks = ⊥ := by
    rcases hsimple.eq_bot_or_eq_top_of_normal (Subgroup.center ↥Ks) with h0 | h0
    · exact h0
    · exfalso
      have : IsMulCommutative ↥Ks := Subgroup.center_eq_top_iff.mp h0
      exact ksOrd_not_prime hord (Group.is_simple_iff_prime_card.mp hsimple)
  have hker : σ.ker = Subgroup.center L := by
    refine le_antisymm hz fun z hz' => ?_
    rw [MonoidHom.mem_ker]
    have : σ z ∈ Subgroup.center ↥Ks := by
      rw [Subgroup.mem_center_iff]
      intro g
      obtain ⟨x, rfl⟩ := hs g
      rw [← map_mul, ← map_mul, Subgroup.mem_center_iff.mp hz' x]
    rwa [hcen, Subgroup.mem_bot] at this
  refine ⟨Nat.card ↥Ks, hord, ?_⟩
  rw [← hker, Subgroup.card_eq_card_quotient_mul_card_subgroup σ.ker,
    Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective σ hs).toEquiv]

end S153L

end CFSG.Quasithin
