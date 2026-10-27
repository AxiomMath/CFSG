module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.GGQ2Prime

open Subgroup CFSG.Open

theorem pRank_le_card {G : Type*} [Group G] [Finite G] (p : ℕ) (H : Subgroup G) (hp : 2 ≤ p) :
    pRank p H ≤ Nat.card G := by
  unfold pRank
  apply csSup_le'
  rintro k ⟨E, -, -, hE⟩
  have : k < Nat.card G := calc k < p ^ k := Nat.lt_pow_self (by omega)
    _ = Nat.card E := hE.symm
    _ ≤ Nat.card G := Subgroup.card_le_card_group E
  exact this.le

theorem le_twoLocalPrimeRank {G : Type*} [Group G]
    [Finite G] {p : ℕ} (hp : 2 ≤ p) (U E : Subgroup G) (hU : U ≠ ⊥)
    (h2 : IsPGroup 2 U) (hE : E ≤ normalizer (U : Set G)) (hEab : IsElemAbelian p E) {k : ℕ}
    (hk : Nat.card E = p ^ k) : k ≤ twoLocalPrimeRank p G := by
  have hk' : k ≤ pRank p (normalizer (U : Set G)) := by
    unfold pRank
    refine le_csSup ⟨Nat.card G, ?_⟩ ⟨E, hE, hEab, hk⟩
    rintro j ⟨F, -, -, hF⟩
    calc j ≤ p ^ j := (Nat.lt_pow_self (by omega)).le
      _ = Nat.card F := hF.symm
      _ ≤ Nat.card G := Subgroup.card_le_card_group F
  refine hk'.trans (le_csSup ⟨Nat.card G, ?_⟩ ⟨_, ⟨U, hU, h2, rfl⟩, rfl⟩)
  rintro j ⟨H, -, rfl⟩
  exact pRank_le_card p H hp

theorem inf_eq_bot_of_two_odd {G : Type*} [Group G]
    [Finite G] {T N : Subgroup G} (hT : IsPGroup 2 T)
    (hN : Odd (Nat.card N)) : T ⊓ N = ⊥ := by
  obtain ⟨n, hn⟩ := (hT.to_le (inf_le_left : T ⊓ N ≤ T)).exists_card_eq
  have hodd : Odd (Nat.card (T ⊓ N : Subgroup G)) :=
    Odd.of_dvd_nat hN (card_dvd_of_le inf_le_right)
  rw [hn] at hodd
  rcases n with _ | n
  · rw [pow_zero] at hn; exact card_eq_one.1 hn
  · exact absurd hodd (by simp [Nat.odd_iff, pow_succ, Nat.mul_mod_left])

theorem commute_of_comm_mem_odd {G : Type*} [Group G]
    [Finite G] {T E N : Subgroup G} (hT : IsPGroup 2 T)
    (hN : Odd (Nat.card N)) (hET : E ≤ normalizer (T : Set G))
    (hcomm : ∀ t ∈ T, ∀ e ∈ E, t * e * t⁻¹ * e⁻¹ ∈ N) :
    ∀ t ∈ T, ∀ e ∈ E, t * e = e * t := by
  intro t ht e he
  have h1 : e * t⁻¹ * e⁻¹ ∈ T := (mem_normalizer_iff.1 (hET he) t⁻¹).1 (inv_mem ht)
  have hcT : t * e * t⁻¹ * e⁻¹ ∈ T := by
    simpa [mul_assoc] using mul_mem ht h1
  have hc : t * e * t⁻¹ * e⁻¹ ∈ T ⊓ N := ⟨hcT, hcomm t ht e he⟩
  rw [inf_eq_bot_of_two_odd hT hN, mem_bot] at hc
  calc t * e = (t * e * t⁻¹ * e⁻¹) * (e * t) := by group
    _ = e * t := by rw [hc, one_mul]

end CFSG.GGQ2Prime
