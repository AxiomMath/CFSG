module

public import CFSG.Permutation.FiveTransitive.A9SmallActionIndexCore
public import CFSG.Permutation.FiveTransitive.NineDegreeOrderObstruction

public section

namespace CFSG

namespace FiveTransitive.A9SmallActionIndex

theorem one_or_nine
    {F : Type*} [Fintype F] [DecidableEq F] (hF : Nat.card F = 9)
    (H : Subgroup (alternatingGroup F)) (hsmall : H.index ≤ 14) :
    H.index = 1 ∨ H.index = 9 := by
  apply A9SmallActionIndexCore.one_or_nine_of_ne_fourteen hF H hsmall
  intro h14
  let _ : Nontrivial F := Finite.one_lt_card_iff_nontrivial.mp (by omega)
  have hA : Nat.card (alternatingGroup F) = 181440 := by
    rw [nat_card_alternatingGroup,hF]
    norm_num [Nat.factorial]
  have hm := H.card_mul_index
  rw [h14,hA] at hm
  have hH : Nat.card H = 12960 := by omega
  let K := H.map (alternatingGroup F).subtype
  have hK : Nat.card K = 12960 :=
    (Subgroup.card_map_of_injective (alternatingGroup F).subtype_injective).trans hH
  exact NineDegreeOrderObstruction.card_ne K hF hK

end FiveTransitive.A9SmallActionIndex

end CFSG
