module

public import Mathlib.SetTheory.Cardinal.NatCard
public import Mathlib.Algebra.Group.Subgroup.Ker

public section

namespace CFSG

namespace FiveTransitive.KernelImageUniqueFixed

theorem commute_of_ker_le
    {G H K : Type*} [Group G] [Group H] [Group K]
    (f : G →* H) (g : G →* K) (hker : f.ker ≤ g.ker)
    (a b : G) (hab : Commute (f a) (f b)) : Commute (g a) (g b) := by
  have hk : a * b * (b * a)⁻¹ ∈ f.ker := by
    change f (a * b * (b * a)⁻¹) = 1
    rw [map_mul, map_inv, map_mul, map_mul, hab.eq, mul_inv_cancel]
  have hg := MonoidHom.mem_ker.mp (hker hk)
  rw [map_mul, map_inv, map_mul, map_mul] at hg
  exact mul_inv_eq_one.mp hg

theorem fixes_unique
    {Y : Type*} [Finite Y] (a b : Equiv.Perm Y) (hab : Commute a b)
    (hcard : Nat.card (Function.fixedPoints a) ≤ 1) (y : Y) (hy : a y = y) : b y = y := by
  let _ : Subsingleton (Function.fixedPoints a) := Finite.card_le_one_iff_subsingleton.mp hcard
  have hby : a (b y) = b y := by
    calc
      a (b y) = b (a y) := Equiv.Perm.congr_fun hab.eq y
      _ = b y := congrArg b hy
  exact congrArg Subtype.val
    (Subsingleton.elim (⟨b y, hby⟩ : Function.fixedPoints a) ⟨y, hy⟩)

end FiveTransitive.KernelImageUniqueFixed

end CFSG
