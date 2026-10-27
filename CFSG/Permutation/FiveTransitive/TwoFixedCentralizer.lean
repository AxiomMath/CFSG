module

public import CFSG.Permutation.FiveTransitive.RegularOrbitAutomorphism
public import Mathlib.Data.Rat.Floor
public import Mathlib.GroupTheory.PGroup

public section

namespace CFSG

namespace FiveTransitive.TwoFixedCentralizer

open MulAction

private theorem two_le_fixed_card
    (Q : Type*) [Group Q] [Finite Q] [Nontrivial Q]
    (hQ : IsPGroup 2 Q) (f : MulAut Q) (hf : Function.Involutive f) :
    2 ≤ Nat.card {q : Q // f q = q} := by
  let _ : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hf2 : f ^ 2 = 1 := by ext q; exact hf q
  have hp : IsPGroup 2 (Subgroup.zpowers f) := IsPGroup.of_card_dvd_pow (n := 1) (by
    rw [Nat.card_zpowers, pow_one]
    exact orderOf_dvd_of_pow_eq_one hf2)
  have hfixed : fixedPoints (Subgroup.zpowers f) Q = {q : Q | f q = q} := by
    ext q
    constructor
    · intro hq
      exact mem_fixedPoints.mp hq ⟨f, Subgroup.mem_zpowers f⟩
    · intro hq u
      have hle : Subgroup.zpowers f ≤ stabilizer (MulAut Q) q := Subgroup.zpowers_le.mpr hq
      exact hle u.property
  have hm := hp.card_modEq_card_fixedPoints Q
  rw [hfixed] at hm
  change Nat.card Q % 2 = Nat.card {q : Q // f q = q} % 2 at hm
  have hd : 2 ∣ Nat.card Q := hQ.card_eq_or_dvd.resolve_left (by
    have hh : 1 < Nat.card Q := Finite.one_lt_card
    omega)
  have hp0 : 0 < Nat.card {q : Q // f q = q} := Finite.card_pos_iff.mpr ⟨⟨1, map_one f⟩⟩
  have hz := Nat.mod_eq_zero_of_dvd hd
  omega

theorem fixed_card_two
    (Q Y : Type*) [Group Q] [Finite Q] [Nontrivial Q] [Finite Y] [MulAction Q Y]
    (hQ : IsPGroup 2 Q) (f : MulAut Q) (hf : Function.Involutive f)
    (a : Y → Y) (hcompat : ∀ q : Q, ∀ y : Y, a (q • y) = f q • a y)
    (hfree : ∀ q : Q, ∀ y : Y, q • y = y → q = 1)
    (htwo : Nat.card {y : Y // a y = y} = 2) :
    Nat.card {q : Q // f q = q} = 2 ∧
      ∀ x : Y, a x = x →
        Nat.card {y : Y // y ∈ orbit Q x ∧ a y = y} = 2 ∧
        ∀ y : Y, a y = y → y ∈ orbit Q x := by
  obtain ⟨x⟩ : Nonempty {y : Y // a y = y} := Finite.card_pos_iff.mp (by omega)
  have he := RegularOrbitAutomorphism.fixed_card_eq Q Y f.toMonoidHom a x.val x.property
    hcompat (fun q => hfree q x.val)
  change Nat.card {q : Q // f q = q} = Nat.card {y : Y // y ∈ orbit Q x.val ∧ a y = y} at he
  have hle : Nat.card {y : Y // y ∈ orbit Q x.val ∧ a y = y} ≤
      Nat.card {y : Y // a y = y} := Nat.card_le_card_of_injective
    (fun y => ⟨y.val, y.property.2⟩) (by intro y z h; exact Subtype.ext (congrArg (fun v : {y : Y // a y = y} => v.val) h))
  have hlo := two_le_fixed_card Q hQ f hf
  have hc : Nat.card {q : Q // f q = q} = 2 := by omega
  refine ⟨hc, ?_⟩
  intro z hz
  have hc' : Nat.card {y : Y // y ∈ orbit Q z ∧ a y = y} = 2 :=
    (RegularOrbitAutomorphism.fixed_card_eq Q Y f.toMonoidHom a z hz
      hcompat (fun q => hfree q z)).symm.trans hc
  refine ⟨hc', ?_⟩
  have hs : {y : Y | y ∈ orbit Q z ∧ a y = y} = {y : Y | a y = y} := by
    apply Set.eq_of_subset_of_ncard_le (fun y hy => hy.2)
    rw [←Nat.card_coe_set_eq, ←Nat.card_coe_set_eq]
    change Nat.card {y : Y // a y = y} ≤ Nat.card {y : Y // y ∈ orbit Q z ∧ a y = y}
    rw [htwo, hc']
  intro y hy
  have hh : y ∈ {y : Y | y ∈ orbit Q z ∧ a y = y} := by rw [hs]; exact hy
  exact hh.1

end FiveTransitive.TwoFixedCentralizer

end CFSG
