module

public import CFSG.Permutation.FiveTransitive.CentralizingOrbitExponent
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitConjugacy

public section

namespace CFSG

namespace FiveTransitive.Degree54FiveOrbitCountCore

open MulAction NormalizerFixedComplement

private theorem free_complement
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (Q : Subgroup G) (hQ : Nat.card Q = 5) :
    ∀ (q : Q) (x : X), x ∉ fixedPoints Q X → q • x = x → q = 1 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  intro q x hx hqx
  by_contra hq
  have hpow : q ^ 5 = 1 := by rw [← hQ]; exact pow_card_eq_one'
  have ho : orderOf q = 5 := orderOf_eq_prime hpow hq
  have hz : Subgroup.zpowers q = ⊤ := (Subgroup.zpowers q).eq_top_of_card_eq
    (by rw [Nat.card_zpowers,ho,hQ])
  have hs : Subgroup.zpowers q ≤ stabilizer Q x := Subgroup.zpowers_le.mpr hqx
  apply hx
  intro a
  exact hs (hz.symm ▸ Subgroup.mem_top a)

theorem orbit_card_nine
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hQ : Nat.card Q = 5) (hX : Nat.card X = 54)
    (hF : Nat.card (fixedPoints Q X) = 9) :
    Nat.card (orbitRel.Quotient (Inside Q) (Domain (X := X) Q)) = 9 := by
  have hfree := free_inside (X := X) Q (free_complement (X := X) Q hQ)
  have hc := FreeComplementOrbitCount.card_eq_mul_orbits hfree
  have hinside : Nat.card (Inside Q) = Nat.card Q :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv
  rw [card_domain (X := X) Q,← Nat.card_coe_set_eq,hF,hX,hinside,hQ] at hc
  omega

private theorem fixed_iff_orbit_fixed
    {G X : Type*} [Group G] [Finite G] [MulAction G X]
    (Q : Subgroup G) (hQ : Nat.card Q = 5)
    (g : Normalizer Q) (hc : ∀ q : Q, Commute g.val q.val) (hg : g ^ 2 = 1)
    (y : Domain (X := X) Q) :
    g • y = y ↔ NormalizerOrbitConjugacy.orbitHom (X := X) Q g
      (Quotient.mk'' y) = Quotient.mk'' y := by
  constructor
  · intro h
    change (Quotient.mk'' (g • y) : orbitRel.Quotient (Inside Q) (Domain (X := X) Q)) = Quotient.mk'' y
    rw [h]
  · intro h
    have hQpow : ∀ q : Q, q ^ 5 = 1 := by intro q; rw [← hQ]; exact pow_card_eq_one'
    apply Subtype.ext
    apply CentralizingOrbitExponent.smul_eq_of_square_eq_one Q hQpow g.val hc
      (congrArg Subtype.val hg) y.val
    change (Quotient.mk'' (g • y) : orbitRel.Quotient (Inside Q) (Domain (X := X) Q)) = Quotient.mk'' y at h
    have ho : g • y ∈ orbit (Inside Q) y := Quotient.exact h
    obtain ⟨q,hq⟩ := mem_orbit_iff.mp ho
    exact ⟨⟨q.val.val,q.property⟩,(congrArg Subtype.val hq).symm⟩

theorem exterior_fixed_card
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hQ : Nat.card Q = 5)
    (g : Normalizer Q) (hc : ∀ q : Q, Commute g.val q.val) (hg : g ^ 2 = 1) :
    (fixedBy X g.val \ fixedPoints Q X).ncard =
      5 * Nat.card (Function.fixedPoints (NormalizerOrbitConjugacy.orbitHom (X := X) Q g)) := by
  let Y := Domain (X := X) Q
  let f := NormalizerOrbitConjugacy.orbitHom (X := X) Q g
  let e : fixedBy Y g ≃ {y : Y // f (Quotient.mk'' y) = Quotient.mk'' y} :=
    Equiv.subtypeEquivRight (fun y => fixed_iff_orbit_fixed Q hQ g hc hg y)
  have hcount := FreeActionTransporterCount.card_orbit_preimage
    (free_inside (X := X) Q (free_complement (X := X) Q hQ)) (fun O => f O = O)
  have hinside : Nat.card (Inside Q) = 5 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe Q.le_normalizer).toEquiv).trans hQ
  rw [hinside] at hcount
  rw [← NormalizerFixedComplement.fixed_card Q g,Nat.card_congr e]
  exact hcount

end FiveTransitive.Degree54FiveOrbitCountCore

end CFSG
