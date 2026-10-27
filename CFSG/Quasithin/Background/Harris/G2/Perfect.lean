module

public import CFSG.Quasithin.Vol2.KGNatG2Order
public import CFSG.Quasithin.Background.JonesParshallG2Derived

public section

namespace CFSG.Quasithin.G11.Harris.G2

open CFSG.Open CFSG.Quasithin.Explicit

theorem not_prime_card_cayley {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) : ¬ (Nat.card ↥(cayleyGroup K)).Prime := by
  rw [CFSG.Quasithin.Vol2.KGNat.card_cayleyGroup, Nat.prime_mul_iff]
  have h1 : 4 ^ 6 ≤ Nat.card K ^ 6 := Nat.pow_le_pow_left hK 6
  have h2 : 4 ^ 2 ≤ Nat.card K ^ 2 := Nat.pow_le_pow_left hK 2
  rintro (⟨-, h⟩ | ⟨-, h⟩)
  · have : 15 ≤ Nat.card K ^ 6 - 1 := by omega
    have h3 : 15 ≤ Nat.card K ^ 2 - 1 := by omega
    nlinarith
  · omega

theorem commutator_eq_top_of_simple {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    (h : ¬ (Nat.card X).Prime) : commutator X = ⊤ := by
  have hnab : ∃ a b : X, a * b ≠ b * a := by
    by_contra hc
    push Not at hc
    let _ : CommGroup X := { (inferInstance : Group X) with mul_comm := hc }
    exact h (IsSimpleGroup.prime_card (α := X))
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (commutator X) with h1 | h1
  · exfalso
    obtain ⟨a, b, hab⟩ := hnab
    apply hab
    have h2 : a * b * a⁻¹ * b⁻¹ ∈ commutator X := by
      rw [commutator_def]
      exact Subgroup.commutator_mem_commutator (Subgroup.mem_top a) (Subgroup.mem_top b)
    rw [h1, Subgroup.mem_bot] at h2
    calc a * b = a * b * a⁻¹ * b⁻¹ * (b * a) := by group
      _ = b * a := by rw [h2, one_mul]
  · exact h1

theorem commutator_cayleyGroup_eq {K : Type} [Field K] [Finite K] [CharP K 2]
    (hK : 4 ≤ Nat.card K) [IsSimpleGroup ↥(cayleyGroup K)] :
    ⁅cayleyGroup K, cayleyGroup K⁆ = cayleyGroup K := by
  have h := commutator_eq_top_of_simple (X := ↥(cayleyGroup K)) (not_prime_card_cayley hK)
  have h2 : ⁅cayleyGroup K, cayleyGroup K⁆ = (commutator ↥(cayleyGroup K)).map
      (cayleyGroup K).subtype := by
    rw [_root_.commutator, Subgroup.map_commutator, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype]
  rw [h2, h, ← MonoidHom.range_eq_map, Subgroup.range_subtype]

end CFSG.Quasithin.G11.Harris.G2
