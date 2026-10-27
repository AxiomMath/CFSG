module

public import Mathlib.GroupTheory.Subgroup.Simple
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG

namespace FiveTransitive.SimpleActionEven

private theorem hom_eq_one
    {G A : Type*} [Group G] [CommGroup A] [IsSimpleGroup G]
    (hcomm : ¬ IsMulCommutative G) (f : G →* A) (g : G) : f g = 1 := by
  rcases (inferInstance : f.ker.Normal).eq_bot_or_eq_top with h | h
  · have hi := (MonoidHom.ker_eq_bot_iff f).mp h
    exfalso
    apply hcomm
    apply isMulCommutative_iff.mpr
    intro x y
    apply hi
    simp only [map_mul, mul_comm]
  · have hg : g ∈ f.ker := by rw [h]; trivial
    exact hg

theorem sign_eq_one
    {G X : Type*} [Group G] [IsSimpleGroup G] [Fintype X] [DecidableEq X]
    [MulAction G X] (hcomm : ¬ IsMulCommutative G) (g : G) :
    Equiv.Perm.sign (MulAction.toPermHom G X g) = 1 :=
  hom_eq_one hcomm (Equiv.Perm.sign.comp (MulAction.toPermHom G X)) g

theorem four_dvd_support_of_even_involution
    {X : Type*} [Fintype X] [DecidableEq X] (g : Equiv.Perm X)
    (h2 : g ^ 2 = 1) (heven : g.sign = 1) : 4 ∣ g.support.card := by
  have hd := Equiv.Perm.two_dvd_card_support h2
  have hs := Equiv.Perm.sign_of_pow_two_eq_one h2
  rw [g.card_fixedPoints, g.sum_cycleType,
    Nat.sub_sub_self (Finset.card_le_univ g.support), heven] at hs
  have hp : Even (g.support.card / 2) :=
    (neg_one_pow_eq_one_iff_even (by decide : (-1 : ℤˣ) ≠ 1)).mp hs.symm
  obtain ⟨k, hk⟩ := hp
  refine ⟨k, ?_⟩
  have hc := Nat.div_mul_cancel hd
  omega

theorem fixed_card_mod_four
    {G X : Type*} [Group G] [IsSimpleGroup G] [Fintype X] [DecidableEq X]
    [MulAction G X] (hcomm : ¬ IsMulCommutative G) (g : G) (hg : orderOf g = 2) :
    (MulAction.fixedBy X g).ncard % 4 = Fintype.card X % 4 := by
  let p := MulAction.toPermHom G X g
  have hp2 : p ^ 2 = 1 := by
    rw [← map_pow, show g ^ 2 = 1 from hg ▸ pow_orderOf_eq_one g, map_one]
  have hd := four_dvd_support_of_even_involution p hp2 (sign_eq_one hcomm g)
  have hc := p.card_fixedPoints
  have hf : (MulAction.fixedBy X g).ncard = Fintype.card (Function.fixedPoints p) := by
    rw [← Nat.card_coe_set_eq, Nat.card_eq_fintype_card]
    rfl
  rw [hf, hc, p.sum_cycleType]
  have hle := Finset.card_le_univ p.support
  omega

end FiveTransitive.SimpleActionEven

end CFSG
