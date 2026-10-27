module

public import Mathlib.Algebra.Group.Subgroup.Ker
public import CFSG.Permutation.FiveTransitive.EqualSquareCommutation
public import Mathlib.GroupTheory.Perm.Sign
public import Mathlib.SetTheory.Cardinal.Finite

public section

namespace CFSG

namespace FiveTransitive.OddLiftCommutation

theorem commute
    {G F : Type*} [Group G] [Fintype F] [DecidableEq F]
    (f : G →* Equiv.Perm F) (Q A : Subgroup G) (hQ : Nat.card Q = 2)
    (hker : A ⊓ f.ker = Q) (a : Q) (ha : a ≠ 1)
    (heven : ∀ u : G, u ^ 2 = 1 → Equiv.Perm.sign (f u) = 1)
    (x u : A) (hx : x.val ^ 2 = a.val) (hu : u.val ^ 2 = 1)
    (hodd : Equiv.Perm.sign (f x.val) = -1)
    (hlocal : Commute (f x.val) (f u.val)) : Commute x.val u.val := by
  have hQker : Q ≤ f.ker := hker.ge.trans inf_le_right
  have hx2 : (f x.val) ^ 2 = 1 := by
    rw [← map_pow,hx]
    exact hQker a.property
  have hu2 : (f u.val) ^ 2 = 1 := by rw [← map_pow,hu,map_one]
  have hm : (x.val * u.val) ^ 2 ∈ Q := by
    apply hker.le
    refine ⟨A.pow_mem (A.mul_mem x.property u.property) 2,?_⟩
    change f ((x.val * u.val) ^ 2) = 1
    rw [map_pow,map_mul,hlocal.mul_pow,hx2,hu2,one_mul]
  have hne : (x.val * u.val) ^ 2 ≠ 1 := by
    intro h
    have hs := heven (x.val * u.val) h
    rw [map_mul,map_mul,hodd,heven u.val hu,mul_one] at hs
    contradiction
  obtain ⟨q,_,hq⟩ := (Nat.card_eq_two_iff' (1 : Q)).mp hQ
  have he : (x.val * u.val) ^ 2 = a.val := congrArg Subtype.val
    ((hq ⟨(x.val * u.val)^2,hm⟩ (fun h => hne (congrArg Subtype.val h))).trans
      (hq a ha).symm)
  exact EqualSquareCommutation.commute_of_involution x.val u.val hu (he.trans hx.symm)

end FiveTransitive.OddLiftCommutation

end CFSG
