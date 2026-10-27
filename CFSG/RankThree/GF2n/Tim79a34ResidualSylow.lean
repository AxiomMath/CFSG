module

public import Mathlib.GroupTheory.Sylow

public section

namespace CFSG.RankThree.GF2n.Tim79a

theorem sup_eq_top_of_sylow {G : Type} [Group G] [Finite G] {G₀ : Subgroup G} [G₀.Normal]
    (h2 : IsPGroup 2 (G ⧸ G₀)) (T : Sylow 2 G) : G₀ ⊔ (T : Subgroup G) = ⊤ := by
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨m, hm⟩ := h2.exists_card_eq
  have hG0 : G₀.index = 2 ^ m := hm
  have hodd : ¬ 2 ∣ (T : Subgroup G).index := T.not_dvd_index
  have hdvdG0 : (G₀ ⊔ (T : Subgroup G)).index ∣ 2 ^ m := by
    rw [← hG0]
    exact Subgroup.index_dvd_of_le le_sup_left
  have hdvdT : (G₀ ⊔ (T : Subgroup G)).index ∣ (T : Subgroup G).index :=
    Subgroup.index_dvd_of_le le_sup_right
  have hcop : Nat.Coprime (G₀ ⊔ (T : Subgroup G)).index 2 :=
    ((Nat.Prime.coprime_iff_not_dvd Nat.prime_two).mpr fun h => hodd (h.trans hdvdT)).symm
  have hone : (G₀ ⊔ (T : Subgroup G)).index = 1 :=
    Nat.Coprime.eq_one_of_dvd (Nat.Coprime.pow_right m hcop) hdvdG0
  exact Subgroup.index_eq_one.mp hone

end CFSG.RankThree.GF2n.Tim79a
