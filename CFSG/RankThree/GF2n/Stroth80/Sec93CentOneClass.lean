module

public import CFSG.LargeExtraspecial.AS35WOneSpor
public import CFSG.RankThree.GF2n.Stroth80.Sec93CentConj

public section

namespace CFSG.RankThree.GF2n.Stroth80

open CFSG CFSG.CGT.Timmesfeld75 CFSG.Open

theorem mem_of_mul_self_eq_one_of_oneClass {G : Type} [Group G] {T : Subgroup G} (hT : IsWC T)
    (hT1 : T ≠ ⊥) (hone : ∀ x y : G, orderOf x = 2 → orderOf y = 2 → IsConj x y) {x : G}
    (hx : x ∈ Subgroup.centralizer (T : Set G)) (hx2 : x * x = 1) : x ∈ T := by
  by_cases hx1 : x = 1
  · rw [hx1]
    exact T.one_mem
  obtain ⟨⟨t, htT⟩, ht1⟩ := Subgroup.ne_bot_iff_exists_ne_one.mp hT1
  have ht1' : t ≠ 1 := fun h' => ht1 (Subtype.ext h')
  have htt : t * t = 1 := elemAbelian_mul_self hT.1 htT
  have hxo : orderOf x = 2 := orderOf_eq_prime (by rw [pow_two]; exact hx2) hx1
  have hto : orderOf t = 2 := orderOf_eq_prime (by rw [pow_two]; exact htt) ht1'
  exact mem_of_isConj_of_mem_wc hT hx hx1 htT (hone x t hxo hto)

theorem mem_of_mul_self_eq_one_m22
    {S : Type} [Group S]
    (hS : CFSG.Blueprint.NativeSporadic.IsSporadic S .M22) {T : Subgroup S} (hT : IsWC T)
    (hT1 : T ≠ ⊥) {x : S} (hx : x ∈ Subgroup.centralizer (T : Set S)) (hx2 : x * x = 1) :
    x ∈ T :=
  mem_of_mul_self_eq_one_of_oneClass hT hT1 (CFSG.LargeExtraspecial.AS35W.oneClass_M22 hS) hx hx2

theorem mem_of_mul_self_eq_one_m23
    {S : Type} [Group S]
    (hS : CFSG.Blueprint.NativeSporadic.IsSporadic S .M23) {T : Subgroup S} (hT : IsWC T)
    (hT1 : T ≠ ⊥) {x : S} (hx : x ∈ Subgroup.centralizer (T : Set S)) (hx2 : x * x = 1) :
    x ∈ T :=
  mem_of_mul_self_eq_one_of_oneClass hT hT1 (CFSG.LargeExtraspecial.AS35W.oneClass_M23 hS) hx hx2

end CFSG.RankThree.GF2n.Stroth80
