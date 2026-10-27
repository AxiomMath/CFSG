module

public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFamily

public section

namespace CFSG

namespace FiveTransitive.Degree67TwoSevenOrbit

open MulAction NormalizerOrbitFamily

theorem seven_fixes_family {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (Q : Subgroup G) (m : ℕ) (hsmall : Nat.card (Family (X := X) Q m) ≤ 6)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 7 = 1)
    (O : Family (X := X) Q m) :
    NormalizerOrbitHom.toPermHom (Y := X) Q g O.val = O.val := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let B := Family (X := X) Q m
  let a := NormalizerOrbitFamily.toPermHom (X := X) Q m g
  have ha7 : a ^ 7 = 1 := by rw [← map_pow,hg,map_one]
  have ha : a = 1 := by
    by_contra hn
    have ho : orderOf a = 7 := orderOf_eq_prime ha7 hn
    have hd : 7 ∣ (Nat.card B).factorial := by
      rw [← Nat.card_perm]
      exact ho ▸ orderOf_dvd_natCard a
    have hh := hd.trans (Nat.factorial_dvd_factorial hsmall)
    norm_num [Nat.factorial] at hh
  exact congrArg (fun p : Equiv.Perm B => (p O).val) ha

theorem exists_fixed_of_preserved {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (Q : Subgroup G) (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 7 = 1)
    (O : orbitRel.Quotient Q X) (hO : NormalizerOrbitHom.toPermHom (Y := X) Q g O = O)
    (hcop : ¬ 7 ∣ Nat.card O.orbit) : ∃ x : X, x ∈ O.orbit ∧ g.val • x = x := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let _ : Fintype O.orbit := Fintype.ofFinite _
  let f := NormalizerOrbitHom.toPermHom (Y := X) Q g
  have hstable (x : X) : g.val • x ∈ O.orbit ↔ x ∈ O.orbit := by
    simp only [orbitRel.Quotient.mem_orbit]
    change f (Quotient.mk'' x) = O ↔ Quotient.mk'' x = O
    exact ⟨fun he => f.injective (he.trans hO.symm),fun he => (congrArg f he).trans hO⟩
  let a : Equiv.Perm O.orbit := (toPerm g.val).subtypePerm hstable
  have hpow (n : ℕ) (x : O.orbit) : ((a ^ n) x).val = g.val ^ n • x.val := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      change g.val • ((a ^ n) x).val = _
      rw [ih,pow_succ',mul_smul]
  have ha7 : a ^ 7 = 1 := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rw [hpow,← Subgroup.coe_pow,hg,Subgroup.coe_one,one_smul]
    rfl
  obtain ⟨x,hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 7) (n := 1)
    (by simpa only [Nat.card_eq_fintype_card] using hcop) (by simpa only [pow_one] using ha7)
  exact ⟨x.val,x.property,congrArg Subtype.val hx⟩

end FiveTransitive.Degree67TwoSevenOrbit

end CFSG
