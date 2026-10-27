module

public import CFSG.LieType.Chevalley.DiagramCoordinateFixedStructure

public section

namespace CFSG.StandardType

namespace ExcFrames

open CFSG.LieType.Chevalley CFSG.LocalAnalysis.ComponentInitial

section TwistedField

variable {K : Type} [Field K] [Finite K]

theorem card_fixSubfield_pow_two {n : ℕ} (hn : 1 ≤ n) (hK : Nat.card K = 2 ^ n)
    (δ : K ≃+* K) : orderOf δ ∣ n ∧ Nat.card (fixSubfield δ) = 2 ^ (n / orderOf δ) := by
  obtain ⟨-, -, -, -, -, hA⟩ :=
    finite_field_automorphism_fixed_field_cardinality Nat.prime_two hn hK
  obtain ⟨hdvd, S, hS, hcard⟩ := hA (Subgroup.zpowers δ)
  rw [Nat.card_zpowers] at hdvd hcard
  refine ⟨hdvd, ?_⟩
  have hSeq : fixSubfield δ = S := by
    ext c
    have hc : c ∈ S ↔ ∀ τ ∈ Subgroup.zpowers δ, τ c = c := by
      rw [← SetLike.mem_coe, hS]
      rfl
    rw [hc, mem_fixSubfield]
    constructor
    · intro h τ hτ
      have hle : Subgroup.zpowers δ ≤ MulAction.stabilizer (K ≃+* K) c := by
        rw [Subgroup.zpowers_le, MulAction.mem_stabilizer_iff]
        exact h
      exact hle hτ
    · intro h
      exact h δ (Subgroup.mem_zpowers δ)
  rw [hSeq]
  exact hcard

theorem exists_fixSubfield_twisted {f : ℕ} (hf : 1 ≤ f) (hK : Nat.card K = (2 ^ f) ^ 2) {p : ℕ}
    [Fact p.Prime] (hp2 : p ≠ 2) {δ : K ≃+* K} (hδ : δ ^ p = 1) :
    ∃ f₀ : ℕ, 1 ≤ f₀ ∧ Nat.card (fixSubfield δ) = (2 ^ f₀) ^ 2 ∧
      (∀ c : fixSubfield δ, (c : K) ^ 2 ^ f = (c : K) ^ 2 ^ f₀) ∧
      ((2 ^ f₀ : ℕ) : ZMod p) = ((2 ^ f : ℕ) : ZMod p) := by
  have hpp : p.Prime := Fact.out
  have hK' : Nat.card K = 2 ^ (2 * f) := by rw [hK, ← pow_mul, mul_comm]
  obtain ⟨hdvd, hcard⟩ := card_fixSubfield_pow_two (by omega : 1 ≤ 2 * f) hK' δ
  obtain ⟨d, hd⟩ : ∃ d, d = orderOf δ := ⟨_, rfl⟩
  rw [← hd] at hdvd hcard
  have hdp : d ∣ p := hd ▸ orderOf_dvd_of_pow_eq_one hδ
  have hd1p : d = 1 ∨ d = p := (Nat.dvd_prime hpp).1 hdp
  have hdf : d ∣ f := by
    rcases hd1p with rfl | rfl
    · exact one_dvd f
    · rcases (Nat.Prime.dvd_mul hpp).1 hdvd with h | h
      · exact absurd ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1 h) hp2
      · exact h
  have hdodd : Odd d := by
    rcases hd1p with rfl | rfl
    · exact odd_one
    · exact hpp.odd_of_ne_two hp2
  obtain ⟨f₀, hf₀⟩ := hdf
  have hf₀1 : 1 ≤ f₀ := by
    rcases Nat.eq_zero_or_pos f₀ with h | h
    · rw [h, mul_zero] at hf₀
      omega
    · exact h
  have hd0 : 0 < d := by
    rcases Nat.eq_zero_or_pos d with h | h
    · rw [h, zero_mul] at hf₀
      omega
    · exact h
  have hq : Nat.card (fixSubfield δ) = (2 ^ f₀) ^ 2 := by
    rw [hcard, ← pow_mul, show 2 * f = d * (2 * f₀) by rw [hf₀]; ring,
      Nat.mul_div_cancel_left _ hd0, mul_comm]
  refine ⟨f₀, hf₀1, hq, ?_, ?_⟩
  · intro c
    obtain ⟨j, hj⟩ := hdodd
    haveI : Fintype (fixSubfield δ) := Fintype.ofFinite _
    have hcardS : Fintype.card (fixSubfield δ) = (2 ^ f₀) ^ 2 := by
      rw [← Nat.card_eq_fintype_card]
      exact hq
    have h1 : c ^ (2 ^ f) = c ^ (2 ^ f₀) := by
      have h2 : 2 ^ f = 2 ^ f₀ * (Fintype.card (fixSubfield δ)) ^ j := by
        rw [hcardS, ← pow_mul, ← pow_mul, ← pow_add, hf₀, hj]
        congr 1
        ring
      rw [h2, pow_mul, FiniteField.pow_card_pow]
    have h3 := congrArg Subtype.val h1
    simpa using h3
  · have hfermat : ∀ x : ZMod p, x ^ d = x := by
      rcases hd1p with h | h
      · intro x
        rw [h, pow_one]
      · intro x
        rw [h]
        exact ZMod.pow_card x
    have h2 : (2 ^ f : ℕ) = (2 ^ f₀) ^ d := by
      rw [← pow_mul, hf₀, mul_comm]
    calc ((2 ^ f₀ : ℕ) : ZMod p) = ((2 ^ f₀ : ℕ) : ZMod p) ^ d := (hfermat _).symm
      _ = (((2 ^ f₀) ^ d : ℕ) : ZMod p) := (Nat.cast_pow _ _).symm
      _ = ((2 ^ f : ℕ) : ZMod p) := by rw [h2]

end TwistedField

end ExcFrames

end CFSG.StandardType
