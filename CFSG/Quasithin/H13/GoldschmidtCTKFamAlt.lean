module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamCore
public import CFSG.Quasithin.H13.GoldschmidtCTKFamAltEight

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique

theorem not_core_of_not_dvd {S : Type} [Group S] (h : ¬ 960 ∣ Nat.card S) : ¬ A5Core S := by
  rintro ⟨K, V, -, -, hK, -⟩
  exact h (hK ▸ Subgroup.card_subgroup_dvd_card K)

theorem card_alternatingGroup_fin {n : ℕ} (hn : 2 ≤ n) :
    Nat.card ↥(alternatingGroup (Fin n)) = n.factorial / 2 := by
  have : Nontrivial (Fin n) := Fin.nontrivial_iff_two_le.2 hn
  rw [Nat.card_eq_fintype_card, card_alternatingGroup, Fintype.card_fin]

theorem not_core_alternatingGroup_small {S : Type} [Group S] {n : ℕ} (h5 : 5 ≤ n) (h7 : n ≤ 7)
    (e : S ≃* alternatingGroup (Fin n)) : ¬ A5Core S := by
  apply not_core_of_not_dvd
  rw [Nat.card_congr e.toEquiv, card_alternatingGroup_fin (by omega)]
  interval_cases n <;> decide

theorem not_core_alternatingGroup_eight {S : Type} [Group S]
    (e : S ≃* alternatingGroup (Fin 8)) : ¬ A5Core S := by
  rintro ⟨K, V, hVK, hKN, hK, hV, hel, -⟩
  obtain ⟨x, hxK, hx5⟩ := exists_orderOf_five_of_card_eq_960 hK
  let φ : S →* Equiv.Perm (Fin 8) := (alternatingGroup (Fin 8)).subtype.comp e.toMonoidHom
  have hφ : Function.Injective φ := Subtype.val_injective.comp e.injective
  have hxN : x ∈ Subgroup.normalizer (V : Set S) := hKN hxK
  have hxN' : x⁻¹ ∈ Subgroup.normalizer (V : Set S) := inv_mem hxN
  refine AltEight.false_of_five (V := V.map φ) (x := φ x) ?_ ?_ ?_ ?_ ?_
  · rw [orderOf_injective φ hφ x, hx5]
  · rw [Subgroup.card_map_of_injective hφ, hV]
  · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    rw [← map_mul, ← map_mul, mul_comm_of_isElemAbelian hel ha hb]
  · rintro _ ⟨v, hv, rfl⟩
    exact ⟨x * v * x⁻¹, (Subgroup.mem_normalizer_iff.1 hxN v).1 hv, by simp [map_mul, map_inv]⟩
  · rintro _ ⟨v, hv, rfl⟩
    refine ⟨x⁻¹ * v * x, ?_, by simp [map_mul, map_inv]⟩
    have := (Subgroup.mem_normalizer_iff.1 hxN' v).1 hv
    simpa using this

theorem exclA5BlockFor_alt : ExclA5BlockFor fun S _ => SQTKAltFam S := by
  refine ExclA5BlockFor.of_not_core fun S _ _ hS => ?_
  obtain ⟨n, h5, h8, ⟨e⟩⟩ := hS
  rcases Nat.lt_or_ge n 8 with h | h
  · exact not_core_alternatingGroup_small h5 (by omega) e
  · obtain rfl : n = 8 := by omega
    exact not_core_alternatingGroup_eight e

end CFSG.Quasithin.H13.CTK
