module

public import CFSG.Permutation.FiveTransitive.SmallThreeOrbitAbelian

public section

namespace CFSG

namespace FiveTransitive.SmallThreeOrbitExponent

open MulAction

theorem cube_smul_eq
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hG : IsPGroup 3 G) (horbit : ∀ x : X, Nat.card (orbit G x) ≤ 3)
    (g : G) (x : X) : (g ^ 3) • x = x := by
  classical
  let C : SubMulAction G X :=
    { carrier := orbit G x
      smul_mem' := by
        intro q y hy
        obtain ⟨r,rfl⟩ := mem_orbit_iff.mp hy
        exact mem_orbit_iff.mpr ⟨q*r,mul_smul q r x⟩ }
  let rho := toPermHom G C
  have hd : Nat.card rho.range ∣ 3 :=
    SmallThreeOrbitAbelian.image_card_dvd_three hG (horbit x)
  have he : rho.rangeRestrict g ^ 3 = 1 :=
    orderOf_dvd_iff_pow_eq_one.mp ((orderOf_dvd_natCard _).trans hd)
  have hev := congrArg rho.range.subtype he
  simp only [map_pow,map_one] at hev
  change rho g ^ 3 = 1 at hev
  rw [← map_pow] at hev
  exact congrArg Subtype.val (DFunLike.congr_fun hev ⟨x,mem_orbit_self x⟩)

end FiveTransitive.SmallThreeOrbitExponent

end CFSG
