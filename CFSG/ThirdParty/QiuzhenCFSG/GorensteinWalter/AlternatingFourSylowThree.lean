module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.AlternatingFourThreeSubgroupNormalizer
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

/-!
# Sylow three-subgroups in groups isomorphic to `A₄`

A finite group isomorphic to `A₄` has exactly four Sylow `3`-subgroups.
-/

namespace CFSG.GorensteinWalter

universe u

/-- A finite group isomorphic to `A₄` has four Sylow `3`-subgroups. -/
public theorem sylow_three_card_eq_four_of_mulEquiv_alternatingGroup_four
    {G : Type u} [Group G] [Finite G]
    (he : Nonempty (G ≃* alternatingGroup (Fin 4))) :
    Nat.card (Sylow 3 G) = 4 := by
  classical
  let : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 G := Classical.choice Sylow.nonempty
  let e : G ≃* alternatingGroup (Fin 4) := he.some
  have hGcard : Nat.card G = 12 := by
    calc
      Nat.card G = Nat.card (alternatingGroup (Fin 4)) :=
        Nat.card_congr e.toEquiv
      _ = 12 := alternatingGroup.card_of_card_eq_four (by simp)
  have hPcard : Nat.card P = 3 := by
    rw [P.card_eq_multiplicity, hGcard]
    have hfac : (Nat.factorization 12) 3 = 1 := by
      rw [show 12 = 3 * 4 by norm_num,
        Nat.factorization_mul_apply_of_coprime (by norm_num : Nat.Coprime 3 4),
        Nat.prime_three.factorization_self,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num : ¬ 3 ∣ 4)]
    rw [hfac]
    norm_num
  have hPnorm : Subgroup.normalizer (P : Set G) = (P : Subgroup G) :=
    normalizer_eq_self_of_card_eq_three_of_mulEquiv_alternatingGroup_four
      P hPcard he
  calc
    Nat.card (Sylow 3 G) =
        (Subgroup.normalizer (P : Set G)).index :=
      P.card_eq_index_normalizer
    _ = P.index := by rw [hPnorm]
    _ = 4 := by
      have hmul := P.card_mul_index
      rw [hPcard, hGcard] at hmul
      omega

end CFSG.GorensteinWalter
