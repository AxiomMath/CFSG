module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Coprime

public section

namespace CFSG.Quasithin.Fan86

variable {G : Type*} [Group G]

theorem exists_mul_of_relIndex_eq (K W C : Subgroup G) [Finite K] (hWK : W ≤ K)
    (h : C.relIndex K = C.relIndex W) : ∀ g ∈ K, ∃ w ∈ W, ∃ c ∈ C ⊓ K, g = w * c := by
  intro g hg
  have hfin : Finite W :=
    Finite.of_injective (Subgroup.inclusion hWK) (Subgroup.inclusion_injective _)
  have hbij : Function.Bijective (Subgroup.quotientSubgroupOfEmbeddingOfLE C hWK) := by
    refine Function.Injective.bijective_of_nat_card_le
      (Subgroup.quotientSubgroupOfEmbeddingOfLE C hWK).injective ?_
    exact h.le
  obtain ⟨q, hq⟩ := hbij.2 (QuotientGroup.mk (⟨g, hg⟩ : K))
  obtain ⟨w, rfl⟩ := QuotientGroup.mk_surjective q
  rw [Subgroup.quotientSubgroupOfEmbeddingOfLE_apply_mk] at hq
  have hc := QuotientGroup.eq.1 hq
  rw [Subgroup.mem_subgroupOf] at hc
  refine ⟨w, w.2, (w : G)⁻¹ * g, ⟨?_, ?_⟩, by group⟩
  · simpa using hc
  · exact K.mul_mem (K.inv_mem (hWK w.2)) hg

theorem ge_256_of_modEq {n : ℕ} (hpow : ∃ k, n = 2 ^ k) (hmod : n ≡ 1 [MOD 5]) (h16 : 16 ≤ n)
    (hne : n ≠ 16) : 256 ≤ n := by
  obtain ⟨k, rfl⟩ := hpow
  by_cases hk : k < 8
  · exfalso
    interval_cases k <;> simp_all [Nat.ModEq]
  · calc 256 = 2 ^ 8 := by norm_num
      _ ≤ 2 ^ k := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem relIndex_centralizer_ge_256 (K : Subgroup G) [Finite K] (hK : IsPGroup 2 K) {x : G}
    (hx : orderOf x = 5) (hxK : ∀ k ∈ K, x * k * x⁻¹ ∈ K)
    (h16 : 16 ≤ (Subgroup.centralizer ({x} : Set G)).relIndex K)
    (hne : (Subgroup.centralizer ({x} : Set G)).relIndex K ≠ 16) :
    256 ≤ (Subgroup.centralizer ({x} : Set G)).relIndex K := by
  obtain ⟨k, hk⟩ := hK.index ((Subgroup.centralizer ({x} : Set G)).subgroupOf K)
  exact ge_256_of_modEq ⟨k, hk⟩ (relIndex_centralizer_modEq K hK hx hxK) h16 hne

end CFSG.Quasithin.Fan86
