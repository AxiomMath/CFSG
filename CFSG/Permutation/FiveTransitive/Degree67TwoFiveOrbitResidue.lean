module

public import CFSG.Permutation.FiveTransitive.Degree52TwoOrbitPreserved

public section

namespace CFSG

namespace FiveTransitive.Degree67TwoFiveOrbitResidue

open MulAction NormalizerOrbitFamily

theorem preserved_mod_le
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (p : ℕ) [Fact p.Prime] (Q : Subgroup G)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ p = 1)
    (O : orbitRel.Quotient Q X)
    (hpres : NormalizerOrbitHom.toPermHom (Y := X) Q g O = O) :
    Nat.card O.orbit % p ≤ Nat.card {x : O.orbit // g.val • x.val = x.val} := by
  classical
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
  have hap : a ^ p = 1 := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rw [hpow,← Subgroup.coe_pow,hg,Subgroup.coe_one,one_smul]
    rfl
  let b : Function.End O.orbit := a.toFun
  have hb : b ^ p = 1 := by
    funext x
    change (a ^ p) x = x
    rw [hap]
    rfl
  have hm := Equiv.Perm.card_fixedPoints_modEq (f := b) (p := p) (n := 1)
    (by simpa only [pow_one] using hb)
  change Fintype.card O.orbit % p = Fintype.card (Function.fixedPoints a) % p at hm
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card] at hm
  let e : Function.fixedPoints a ≃ {x : O.orbit // g.val • x.val = x.val} :=
    { toFun := fun x => ⟨x.val,congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨x.val,Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e] at hm
  rw [hm]
  exact Nat.mod_le _ _

theorem family_residue_bound
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (p : ℕ) [Fact p.Prime] (Q : Subgroup G)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ p = 1)
    (b : ℕ) (houtside : Nat.card {x : X // x ∉ fixedPoints Q X ∧ g.val • x = x} ≤ b)
    (m : ℕ) (hm : m ≠ 1) :
    (m % p) * (Nat.card (Family (X := X) Q m) % p) ≤ b := by
  classical
  let B := Family (X := X) Q m
  let sigma := NormalizerOrbitFamily.toPermHom (X := X) Q m
  let Z := Function.fixedPoints (sigma g)
  let E := {x : X // x ∉ fixedPoints Q X ∧ g.val • x = x}
  have hlocal (O : Z) : m % p ≤ Nat.card {x : O.val.val.orbit // g.val • x.val = x.val} := by
    have hh := preserved_mod_le p Q g hg O.val.val (congrArg Subtype.val O.property)
    rwa [O.val.property] at hh
  let e (O : Z) : Fin (m % p) ↪ {x : O.val.val.orbit // g.val • x.val = x.val} :=
    (Fin.castLEEmb (hlocal O)).trans (Finite.equivFin _).symm.toEmbedding
  let f : Z × Fin (m % p) → E := fun t => ⟨(e t.1 t.2).val.val,
    Degree52TwoOrbitPreserved.not_fixed_of_mem Q t.1.val.val
      (by rw [t.1.val.property]; exact hm) _ (e t.1 t.2).val.property,
    (e t.1 t.2).property⟩
  have hf : Function.Injective f := by
    intro a b hab
    have hpoint := congrArg Subtype.val hab
    have ha : (Quotient.mk'' (f a).val : orbitRel.Quotient Q X) = a.1.val.val :=
      orbitRel.Quotient.mem_orbit.mp (e a.1 a.2).val.property
    have hb : (Quotient.mk'' (f b).val : orbitRel.Quotient Q X) = b.1.val.val :=
      orbitRel.Quotient.mem_orbit.mp (e b.1 b.2).val.property
    have he : a.1 = b.1 := Subtype.ext (Subtype.ext
      (ha.symm.trans ((congrArg Quotient.mk'' hpoint).trans hb)))
    rcases a with ⟨a,i⟩
    rcases b with ⟨b,j⟩
    dsimp only at he
    subst b
    have hij : i = j := (e a).injective (Subtype.ext (Subtype.ext hpoint))
    subst j
    rfl
  have hprod : Nat.card Z * (m % p) ≤ b := by
    have hh := Nat.card_le_card_of_injective f hf
    rw [Nat.card_prod,Nat.card_fin] at hh
    exact hh.trans houtside
  let _ : Fintype B := Fintype.ofFinite _
  let a : Function.End B := (sigma g).toFun
  have ha : a ^ p = 1 := by
    funext x
    change ((sigma g) ^ p) x = x
    rw [← map_pow,hg,map_one]
    rfl
  have hmod := Equiv.Perm.card_fixedPoints_modEq (f := a) (p := p) (n := 1)
    (by simpa only [pow_one] using ha)
  change Fintype.card B % p = Fintype.card Z % p at hmod
  rw [← Nat.card_eq_fintype_card,← Nat.card_eq_fintype_card] at hmod
  have hZ : Nat.card B % p ≤ Nat.card Z := by rw [hmod]; exact Nat.mod_le _ _
  change (m % p) * (Nat.card B % p) ≤ b
  exact (Nat.mul_le_mul_left (m % p) hZ).trans (by simpa only [Nat.mul_comm] using hprod)

end FiveTransitive.Degree67TwoFiveOrbitResidue

end CFSG
