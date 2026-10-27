module

public import CFSG.Quasithin.Vol2.KGFact12617L52Leaf.Defs
public import CFSG.Quasithin.Vol2.KGFact12617L52a

public section

namespace CFSG.Quasithin.H13.KG12617L52

open CFSG.Open

private theorem eq_one_of_pow_two_pow_eq_one {F : Type} [Field F] [Finite F] (hF : Nat.card F = 2)
    {x : ↥(StatedSL 5 F)} (hx : orderOf x = 5) :
    ∀ (k : ℕ) (t : ↥(StatedSL 5 F)), t ^ 2 ^ k = 1 → x * t = t * x → t = 1 := by
  intro k
  induction k with
  | zero =>
    intro t ht _
    simpa using ht
  | succ k ih =>
    intro t ht hc
    have hpow : (t ^ 2) ^ 2 ^ k = 1 := by
      rw [← pow_mul, ← pow_succ']
      exact ht
    have hsq : t ^ 2 = 1 :=
      ih (t ^ 2) hpow ((show Commute x t from hc).pow_right 2).eq
    exact eq_one_of_commute_orderOf_five hF hx hsq hc

theorem leafTwoElt_holds : LeafTwoElt := by
  intro F _ _ hF x t hx hk hc
  obtain ⟨k, hk⟩ := hk
  exact eq_one_of_pow_two_pow_eq_one hF hx k t hk hc

end CFSG.Quasithin.H13.KG12617L52
