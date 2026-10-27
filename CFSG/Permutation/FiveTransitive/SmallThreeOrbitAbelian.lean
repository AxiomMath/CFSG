module

public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Finite.Perm
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG

namespace FiveTransitive.SmallThreeOrbitAbelian

open MulAction

theorem image_card_dvd_three
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hG : IsPGroup 3 G) (hX : Nat.card X ≤ 3) :
    Nat.card (toPermHom G X).range ∣ 3 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  let H := (toPermHom G X).range
  have hH : IsPGroup 3 H := hG.of_surjective _ (toPermHom G X).rangeRestrict_surjective
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hH
  have hd := Subgroup.card_subgroup_dvd_card H
  rw [Nat.card_perm] at hd
  have hle : Nat.card H ≤ 6 := by
    have h1 := Nat.le_of_dvd (Nat.factorial_pos _) hd
    have h2 := Nat.factorial_le hX
    norm_num [Nat.factorial] at h2
    omega
  have he1 : e ≤ 1 := by
    by_contra hn
    have hp := Nat.pow_le_pow_right (by norm_num : 0 < 3) (by omega : 2 ≤ e)
    rw [he] at hle
    norm_num at hp
    omega
  change Nat.card H ∣ 3
  rw [he]
  interval_cases e <;> norm_num

theorem isMulCommutative
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (hG : IsPGroup 3 G) (horbit : ∀ x : X, Nat.card (orbit G x) ≤ 3) :
    IsMulCommutative G := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  apply isMulCommutative_iff.mpr
  intro g h
  apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
  intro x
  let C : SubMulAction G X :=
    { carrier := orbit G x
      smul_mem' := by
        intro q y hy
        obtain ⟨r,rfl⟩ := mem_orbit_iff.mp hy
        exact mem_orbit_iff.mpr ⟨q*r, mul_smul q r x⟩ }
  let rho := toPermHom G C
  let H := rho.range
  have hd : Nat.card H ∣ 3 := image_card_dvd_three hG (horbit x)
  let _ : IsCyclic H := isCyclic_of_card_dvd_prime hd
  let _ : IsMulCommutative H := IsCyclic.isMulCommutative
  have he := mul_comm' (rho.rangeRestrict g) (rho.rangeRestrict h)
  have hev := congrArg Subtype.val he
  have hx := congrArg (fun f : Equiv.Perm C => (f ⟨x,mem_orbit_self x⟩).val) hev
  change g • (h • x) = h • (g • x) at hx
  simpa only [mul_smul] using hx

end FiveTransitive.SmallThreeOrbitAbelian

end CFSG
