module

public import CFSG.Permutation.FiveTransitive.NormalizerLargeOrbit
public import Mathlib.Data.Nat.Totient
public import Mathlib.GroupTheory.Perm.Cycle.Type

public section

namespace CFSG

namespace FiveTransitive.NormalizerOrbitFamily

open MulAction
open scoped BigOperators

@[expose] abbrev Family {G X : Type*} [Group G] [MulAction G X] (Q : Subgroup G) (m : ℕ) :=
  {O : orbitRel.Quotient Q X // Nat.card O.orbit = m}

@[expose] def toPermHom {G X : Type*} [Group G] [MulAction G X] (Q : Subgroup G) (m : ℕ) :
    Subgroup.normalizer (Q : Set G) →* Equiv.Perm (Family (X := X) Q m) where
  toFun g := (NormalizerOrbitHom.toPermHom (Y := X) Q g).subtypePerm (by
    intro O
    rw [NormalizerLargeOrbit.card_orbit_eq])
  map_one' := by
    apply Equiv.ext
    intro O
    apply Subtype.ext
    change NormalizerOrbitHom.toPermHom (Y := X) Q 1 O.val = O.val
    rw [map_one]
    rfl
  map_mul' g h := by
    apply Equiv.ext
    intro O
    apply Subtype.ext
    change NormalizerOrbitHom.toPermHom (Y := X) Q (g*h) O.val =
      NormalizerOrbitHom.toPermHom (Y := X) Q g
        (NormalizerOrbitHom.toPermHom (Y := X) Q h O.val)
    rw [map_mul]
    rfl

theorem card_mul_le {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (Q : Subgroup G) (m : ℕ) : Nat.card (Family (X := X) Q m) * m ≤ Nat.card X := by
  classical
  let B := Family (X := X) Q m
  let e (b : B) : Fin m ↪ b.val.orbit :=
    (Fin.castLEEmb b.property.ge).trans (Finite.equivFin b.val.orbit).symm.toEmbedding
  let f : B × Fin m → X := fun p => (e p.1 p.2).val
  have hf : Function.Injective f := by
    intro a b hab
    have ha : (Quotient.mk'' (f a) : orbitRel.Quotient Q X) = a.1.val :=
      orbitRel.Quotient.mem_orbit.mp (e a.1 a.2).property
    have hb : (Quotient.mk'' (f b) : orbitRel.Quotient Q X) = b.1.val :=
      orbitRel.Quotient.mem_orbit.mp (e b.1 b.2).property
    have he : a.1 = b.1 := Subtype.ext (ha.symm.trans ((congrArg Quotient.mk'' hab).trans hb))
    rcases a with ⟨a,i⟩
    rcases b with ⟨b,j⟩
    dsimp only at he
    subst b
    have hij : i = j := (e a).injective (Subtype.ext hab)
    subst j
    rfl
  simpa only [Nat.card_prod,Nat.card_fin] using Nat.card_le_card_of_injective f hf

theorem fixed_family_card {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (Q : Subgroup G) : Nat.card (Family (X := X) Q 1) = Nat.card (fixedPoints Q X) := by
  classical
  let _ : Fintype X := Fintype.ofFinite _
  let f : fixedPoints Q X → Family (X := X) Q 1 := fun x => ⟨Quotient.mk'' x.val,by
    rw [orbitRel.Quotient.orbit_mk,Nat.card_eq_fintype_card]
    exact mem_fixedPoints_iff_card_orbit_eq_one.mp x.property⟩
  have hf : Function.Bijective f := by
    constructor
    · intro x y h
      have he : (Quotient.mk'' x.val : orbitRel.Quotient Q X) = Quotient.mk'' y.val :=
        congrArg Subtype.val h
      obtain ⟨q,hq⟩ := mem_orbit_iff.mp (Quotient.exact he)
      exact Subtype.ext (((y.property q).symm.trans hq).symm)
    · intro O
      obtain ⟨x,hx⟩ := O.val.nonempty_orbit
      have he : (Quotient.mk'' x : orbitRel.Quotient Q X) = O.val :=
        orbitRel.Quotient.mem_orbit.mp hx
      have hfixed : x ∈ fixedPoints Q X := by
        apply mem_fixedPoints_iff_card_orbit_eq_one.mpr
        rw [← Nat.card_eq_fintype_card,← orbitRel.Quotient.orbit_mk,he,O.property]
      exact ⟨⟨x,hfixed⟩,Subtype.ext he⟩
  exact Nat.card_congr (Equiv.ofBijective f hf).symm

theorem card_eq_one_two_four {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (Q : Subgroup G)
    (hsize : ∀ O : orbitRel.Quotient Q X,
      Nat.card O.orbit = 1 ∨ Nat.card O.orbit = 2 ∨ Nat.card O.orbit = 4) :
    Nat.card X = Nat.card (fixedPoints Q X) +
      2 * Nat.card (Family (X := X) Q 2) + 4 * Nat.card (Family (X := X) Q 4) := by
  classical
  let _ : Fintype X := Fintype.ofFinite _
  let _ : Fintype (orbitRel.Quotient Q X) := Fintype.ofFinite _
  have he : Nat.card X = ∑ O : orbitRel.Quotient Q X, Nat.card O.orbit := by
    rw [Nat.card_congr (selfEquivSigmaOrbits Q X)]
    simp only [Nat.card_eq_fintype_card,Fintype.card_sigma]
    congr 1
    funext O
    rw [orbitRel.Quotient.orbit_eq_orbit_out O Quotient.out_eq']
  have hcount (m : ℕ) : Nat.card (Family (X := X) Q m) =
      ∑ O : orbitRel.Quotient Q X, if Nat.card O.orbit = m then 1 else 0 := by
    simp only [Family,Nat.card_eq_fintype_card,Fintype.card_subtype,
      Finset.card_eq_sum_ones,Finset.sum_filter]
  have hterm (O : orbitRel.Quotient Q X) : Nat.card O.orbit =
      (if Nat.card O.orbit = 1 then 1 else 0) +
      2 * (if Nat.card O.orbit = 2 then 1 else 0) +
      4 * (if Nat.card O.orbit = 4 then 1 else 0) := by
    rcases hsize O with h | h | h <;> rw [h] <;> norm_num
  rw [he]
  calc
    ∑ O : orbitRel.Quotient Q X, Nat.card O.orbit =
        ∑ O : orbitRel.Quotient Q X,
          ((if Nat.card O.orbit = 1 then 1 else 0) +
          2 * (if Nat.card O.orbit = 2 then 1 else 0) +
          4 * (if Nat.card O.orbit = 4 then 1 else 0)) :=
      Finset.sum_congr rfl (fun O _ => hterm O)
    _ = _ := by
      rw [Finset.sum_add_distrib,Finset.sum_add_distrib,← Finset.mul_sum,← Finset.mul_sum,
        ← hcount 1,← hcount 2,← hcount 4,fixed_family_card]

theorem exists_fixed_of_preserved {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (Q : Subgroup G) (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (O : orbitRel.Quotient Q X) (hO : NormalizerOrbitHom.toPermHom (Y := X) Q g O = O)
    (hcop : ¬ 5 ∣ Nat.card O.orbit) : ∃ x : X, x ∈ O.orbit ∧ g.val • x = x := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
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
  have ha5 : a ^ 5 = 1 := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rw [hpow,← Subgroup.coe_pow,hg,Subgroup.coe_one,one_smul]
    rfl
  obtain ⟨x,hx⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 5) (n := 1)
    (by simpa only [Nat.card_eq_fintype_card] using hcop) (by simpa only [pow_one] using ha5)
  exact ⟨x.val,x.property,congrArg Subtype.val hx⟩

theorem five_dvd_card_family {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (Q : Subgroup G) (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (hfree : ∀ x : X, x ∉ fixedPoints Q X → g.val • x ≠ x)
    (m : ℕ) (hm : m ≠ 1) (hcop : ¬ 5 ∣ m) :
    5 ∣ Nat.card (Family (X := X) Q m) := by
  classical
  let _ : Fintype X := Fintype.ofFinite _
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let B := Family (X := X) Q m
  let _ : Fintype B := Fintype.ofFinite _
  let a := toPermHom (X := X) Q m g
  have ha5 : a ^ 5 = 1 := by rw [← map_pow,hg,map_one]
  by_contra hn
  obtain ⟨O,hO⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 5) (n := 1)
    (by simpa only [Nat.card_eq_fintype_card] using hn) (by simpa only [pow_one] using ha5)
  have hpres : NormalizerOrbitHom.toPermHom (Y := X) Q g O.val = O.val :=
    congrArg Subtype.val hO
  obtain ⟨x,hx,hgx⟩ := exists_fixed_of_preserved Q g hg O.val hpres (by rwa [O.property])
  apply hfree x ?_ hgx
  intro hxf
  have hc : Nat.card (orbit Q x) = 1 := by
    rw [Nat.card_eq_fintype_card]
    exact mem_fixedPoints_iff_card_orbit_eq_one.mp hxf
  have he := orbitRel.Quotient.mem_orbit.mp hx
  rw [← orbitRel.Quotient.orbit_mk,he,O.property] at hc
  exact hm hc

end FiveTransitive.NormalizerOrbitFamily

end CFSG
