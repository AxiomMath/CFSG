module

public import Mathlib.Data.Nat.Choose.Factorization
public import Mathlib.GroupTheory.PGroup
public import Mathlib.Data.Finite.Perm
public import Mathlib.Tactic.NormNum.Prime

public section

namespace CFSG

namespace FiveTransitive.Degree72LargePrimeOrbitImage

open MulAction

theorem image_card_dvd_prime
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (p : ℕ) (hp : p.Prime) (hG : IsPGroup p G) (hX : Nat.card X ≤ p) :
    Nat.card (toPermHom G X).range ∣ p := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
  let H := (toPermHom G X).range
  have hH : IsPGroup p H := hG.of_surjective _ (toPermHom G X).rangeRestrict_surjective
  obtain ⟨e,he⟩ := IsPGroup.iff_card.mp hH
  have hd := Subgroup.card_subgroup_dvd_card H
  rw [Nat.card_perm] at hd
  have hd' : Nat.card H ∣ p.factorial := hd.trans (Nat.factorial_dvd_factorial hX)
  have hfac : p.factorial.factorization p = 1 := by
    have hlog : Nat.log p p = 1 := by
      rw [Nat.log_eq_one_iff']
      exact ⟨le_rfl, by nlinarith [hp.two_le]⟩
    rw [Nat.factorization_factorial hp (b := 2) (by rw [hlog]; omega)]
    simpa using Nat.div_self hp.pos
  have hle := (Nat.factorization_le_iff_dvd Nat.card_pos.ne' p.factorial_ne_zero).mpr hd'
  have he1 : e ≤ 1 := by
    have h := hle p
    rw [he,Nat.factorization_pow_self hp,hfac] at h
    exact h
  change Nat.card H ∣ p
  rw [he]
  interval_cases e <;> simp

theorem isMulCommutative
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X] [FaithfulSMul G X]
    (p : ℕ) (hp : p.Prime) (hG : IsPGroup p G) (horbit : ∀ x : X, Nat.card (orbit G x) ≤ p) :
    IsMulCommutative G := by
  classical
  let _ : Fact p.Prime := ⟨hp⟩
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
  have hd : Nat.card H ∣ p := image_card_dvd_prime p hp hG (horbit x)
  let _ : IsCyclic H := isCyclic_of_card_dvd_prime hd
  let _ : IsMulCommutative H := IsCyclic.isMulCommutative
  have he := mul_comm' (rho.rangeRestrict g) (rho.rangeRestrict h)
  have hev := congrArg Subtype.val he
  have hx := congrArg (fun f : Equiv.Perm C => (f ⟨x,mem_orbit_self x⟩).val) hev
  change g • (h • x) = h • (g • x) at hx
  simpa only [mul_smul] using hx

end FiveTransitive.Degree72LargePrimeOrbitImage

end CFSG
