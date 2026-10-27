module

public import CFSG.Quasithin.AppendixH.H9.H92.ConjTransport
public import CFSG.Quasithin.AppendixH.H9.H92.Rank6.ElemAb2InSymSix

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open

theorem le_Lg_of_five_le_rk (A : Subgroup (MulAut (PairN 5))) (hA : A ≤ Mg 5)
    (hab : IsElemAbelian2 A) (h5 : 5 ≤ rk ↥A) : A ≤ Lg 5 := by
  by_contra hnle
  obtain ⟨t, htA, htL⟩ := SetLike.not_le_iff_exists.mp hnle
  have ht2 : t ^ 2 = 1 := hab.2 t htA
  have ht1 : t ≠ 1 := fun h => htL (h ▸ (Lg 5).one_mem)
  have hord : orderOf t = 2 := orderOf_eq_prime ht2 ht1
  obtain ⟨θ, -⟩ := isSymNatural_of_outer_involution t (hA htA) htL hord
  have hAb : IsElemAb2 A := hab
  have hcardA : Nat.card ↥A = 2 ^ rk ↥A :=
    card_eq_two_pow_of_isPGroup
      (isPGroup_two_of_sq_eq_one fun v => Subtype.ext (hab.2 (v : MulAut (PairN 5)) v.2))
  have h32 : 32 ≤ Nat.card ↥A := by
    rw [hcardA]
    calc 32 = 2 ^ 5 := by norm_num
      _ ≤ 2 ^ rk ↥A := Nat.pow_le_pow_right (by norm_num) h5
  exact false_of_isElemAb2_of_symSix_centralizer hA (relIndex_Lg_Mg (by norm_num)) hAb h32 htA θ

end CFSG.ASVolI.ChH
