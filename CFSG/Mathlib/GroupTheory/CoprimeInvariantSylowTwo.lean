module

public import Mathlib.GroupTheory.Sylow

@[expose] public section

namespace CFSG.CoprimeInvariantSylowTwo

theorem exists_isPGroup_ne_bot_normalizer {G : Type*} [Group G] [Finite G] {Y E : Subgroup G}
    (hE : E ≤ Subgroup.normalizer (Y : Set G)) (hE3 : IsPGroup 3 E)
    (hY3 : ¬ 3 ∣ Nat.card Y) (hY2 : 2 ∣ Nat.card Y) :
    ∃ T : Subgroup G, T ≤ Y ∧ IsPGroup 2 T ∧ T ≠ ⊥ ∧ E ≤ Subgroup.normalizer (T : Set G) := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  let : MulDistribMulAction E Y :=
    MulDistribMulAction.compHom Y (Y.normalizerMonoidHom.comp (Subgroup.inclusion hE))
  let P₀ : Sylow 2 Y := default
  have : Finite (Sylow 2 Y) := Sylow.finite_of_finiteIndex P₀
  have hdiv : Nat.card (Sylow 2 Y) ∣ Nat.card Y := by
    rw [Sylow.card_eq_index_normalizer P₀]
    exact Subgroup.index_dvd_card (Subgroup.normalizer (P₀ : Set Y))
  have h3 : ¬ 3 ∣ Nat.card (Sylow 2 Y) := fun h => hY3 (h.trans hdiv)
  obtain ⟨P, hP⟩ := hE3.nonempty_fixed_point_of_prime_not_dvd_card (Sylow 2 Y) h3
  let T : Subgroup G := (P : Subgroup Y).map Y.subtype
  have hTle : T ≤ Y := Subgroup.map_subtype_le (P : Subgroup Y)
  have hT2 : IsPGroup 2 T := (P.isPGroup').map Y.subtype
  have h2T : 2 ∣ Nat.card T := by
    rw [Subgroup.card_map_of_injective Y.subtype_injective]
    exact Sylow.dvd_card_of_dvd_card P hY2
  have hTne : T ≠ ⊥ := by
    intro hbot
    rw [hbot, Subgroup.card_bot] at h2T
    exact absurd h2T (by norm_num)
  have hforward : ∀ (e : E) {t : G}, t ∈ T → (e : G) * t * (e : G)⁻¹ ∈ T := by
    intro e t ht
    rcases Subgroup.mem_map.mp ht with ⟨y, hy, rfl⟩
    refine Subgroup.mem_map.mpr ⟨e • y, ?_, rfl⟩
    have hmem := Subgroup.smul_mem_pointwise_smul y e (P : Subgroup Y) hy
    rwa [← Sylow.pointwise_smul_def, MulAction.mem_fixedPoints.mp hP e] at hmem
  refine ⟨T, hTle, hT2, hTne, ?_⟩
  intro e he
  rw [Subgroup.mem_normalizer_iff]
  intro t
  constructor
  · exact hforward ⟨e, he⟩
  · intro ht
    have h1 := hforward ⟨e⁻¹, E.inv_mem he⟩ ht
    simpa [mul_assoc] using h1

end CFSG.CoprimeInvariantSylowTwo

end
