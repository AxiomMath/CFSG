module

public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFamily
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.Degree52TwoOrbitPreserved

open MulAction NormalizerOrbitFamily

theorem orbit_card_cases
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 52) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (O : orbitRel.Quotient Q X) :
    Nat.card O.orbit = 1 ∨ Nat.card O.orbit = 2 ∨ Nat.card O.orbit = 4 ∨
      Nat.card O.orbit = 8 ∨ Nat.card O.orbit = 16 ∨ Nat.card O.orbit = 32 := by
  refine Quotient.inductionOn O ?_
  intro x
  rw [orbitRel.Quotient.orbit_mk]
  obtain ⟨e,he⟩ := hQ.card_orbit x
  have hb := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
  have he6 : e ≤ 5 := by
    by_contra hn
    have hp : 64 ≤ 2 ^ e := Nat.pow_le_pow_right (by decide : 0 < 2) (by omega : 6 ≤ e)
    rw [he] at hb
    omega
  rw [he]
  interval_cases e <;> norm_num

theorem not_fixed_of_mem
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (Q : Subgroup G) (O : orbitRel.Quotient Q X) (hO : Nat.card O.orbit ≠ 1)
    (x : X) (hx : x ∈ O.orbit) : x ∉ fixedPoints Q X := by
  classical
  let _ : Fintype X := Fintype.ofFinite _
  intro hf
  have hc : Nat.card (orbit Q x) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact mem_fixedPoints_iff_card_orbit_eq_one.mp hf
  rw [← orbitRel.Quotient.orbit_mk,orbitRel.Quotient.mem_orbit.mp hx] at hc
  exact hO hc

theorem preserved_card_eq_sixteen
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 52) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (hunique : ∀ x y : X, x ∉ fixedPoints Q X → y ∉ fixedPoints Q X →
      g.val • x = x → g.val • y = y → x = y)
    (O : orbitRel.Quotient Q X) (hO : Nat.card O.orbit ≠ 1)
    (hpres : NormalizerOrbitHom.toPermHom (Y := X) Q g O = O) :
    Nat.card O.orbit = 16 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let _ : Fintype O.orbit := Fintype.ofFinite _
  let f := NormalizerOrbitHom.toPermHom (Y := X) Q g
  have hstable (x : X) : g.val • x ∈ O.orbit ↔ x ∈ O.orbit := by
    simp only [orbitRel.Quotient.mem_orbit]
    change f (Quotient.mk'' x) = O ↔ Quotient.mk'' x = O
    exact ⟨fun he => f.injective (he.trans hpres.symm),
      fun he => (congrArg f he).trans hpres⟩
  let a : Equiv.Perm O.orbit := (toPerm g.val).subtypePerm hstable
  have hpow (n : ℕ) (x : O.orbit) : ((a ^ n) x).val = g.val ^ n • x.val := by
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ',Equiv.Perm.mul_apply]
      change g.val • ((a ^ n) x).val = _
      rw [ih,pow_succ',mul_smul]
  have ha5 : a ^ 5 = 1 := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rw [hpow,← Subgroup.coe_pow,hg,Subgroup.coe_one,one_smul]
    rfl
  have hsub : Subsingleton (Function.fixedPoints a) := ⟨by
    intro x y
    apply Subtype.ext
    apply Subtype.ext
    exact hunique x.val.val y.val.val
      (not_fixed_of_mem Q O hO _ x.val.property)
      (not_fixed_of_mem Q O hO _ y.val.property)
      (congrArg Subtype.val x.property) (congrArg Subtype.val y.property)⟩
  have hle : Nat.card (Function.fixedPoints a) ≤ 1 :=
    Finite.card_le_one_iff_subsingleton.mpr hsub
  let b : Function.End O.orbit := a.toFun
  have hb : b ^ 5 = 1 := by
    funext x
    change (a ^ 5) x = x
    rw [ha5]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := b) (p := 5) (n := 1)
    (by simpa only [pow_one] using hb)
  change Fintype.card O.orbit % 5 = Fintype.card (Function.fixedPoints a) % 5 at hm
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card] at hm
  have hc := orbit_card_cases hX Q hQ O
  omega

theorem five_dvd_family_of_not_preserved
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (Q : Subgroup G) (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (m : ℕ) (hfree : ∀ O : Family (X := X) Q m,
      NormalizerOrbitHom.toPermHom (Y := X) Q g O.val ≠ O.val) :
    5 ∣ Nat.card (Family (X := X) Q m) := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let B := Family (X := X) Q m
  let _ : Fintype B := Fintype.ofFinite _
  let a := NormalizerOrbitFamily.toPermHom (X := X) Q m g
  have ha5 : a ^ 5 = 1 := by rw [← map_pow,hg,map_one]
  by_contra hn
  obtain ⟨O,hO⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 5) (n := 1)
    (by simpa only [Nat.card_eq_fintype_card] using hn) (by simpa only [pow_one] using ha5)
  exact hfree O (congrArg Subtype.val hO)

end FiveTransitive.Degree52TwoOrbitPreserved

end CFSG
