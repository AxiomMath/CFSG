module

public import CFSG.Permutation.FiveTransitive.Degree58LargePrimeFiveCentralizer

public section

namespace CFSG

namespace FiveTransitive.Degree67LargePrimeFiveCentralizer

open MulAction

private theorem fixes_outside
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (hX : Nat.card X = 67) (p : ℕ) (hp : p.Prime) (hp13 : 13 ≤ p)
    (hpfive : Nat.Coprime p 5) (Q : Subgroup G) (hQ : IsPGroup p Q)
    (hlower : 15 ≤ Nat.card (fixedPoints Q X))
    (g : Subgroup.normalizer (Q : Set G)) (hg : orderOf g = 5)
    (hc : g.val ∈ Subgroup.centralizer (Q : Set G))
    (x : X) (hx : x ∉ fixedPoints Q X) : g.val • x = x := by
  classical
  let _ : Fintype X := Fintype.ofFinite _
  let _ : Fact p.Prime := ⟨hp⟩
  obtain ⟨e,he⟩ := hQ.card_orbit x
  have hm : Nat.card (orbit Q x) ≠ 1 := by
    intro hm
    exact hx (mem_fixedPoints_iff_card_orbit_eq_one.mpr (by rwa [← Nat.card_eq_fintype_card]))
  have he0 : 0 < e := by
    by_contra hn
    apply hm
    rw [he,show e=0 by omega,pow_zero]
  have hlo : p ≤ Nat.card (orbit Q x) := by
    rw [he]
    simpa only [pow_one] using Nat.pow_le_pow_right hp.pos he0
  have hb := NormalizerExteriorOrbitFamily.card_mul_add_fixed_le (X := X) Q _ hm
  rw [hX] at hb
  have hsmall : Nat.card (NormalizerOrbitFamily.Family (X := X) Q (Nat.card (orbit Q x))) ≤ 4 := by
    nlinarith
  have hpres := NormalizerExteriorOrbitFamilyFive.five_fixes_family (X := X) Q _ hsmall g
    (hg ▸ pow_orderOf_eq_one g) ⟨Quotient.mk'' x,by rw [orbitRel.Quotient.orbit_mk]⟩
  have horbit : g.val • x ∈ orbit Q x := Quotient.exact (show
      (Quotient.mk'' (g.val • x) : orbitRel.Quotient Q X) = Quotient.mk'' x from hpres)
  apply CoprimeCentralizerOrbit.fixed_of_mem_orbit Q g.val hc ?_ x horbit
  intro r
  obtain ⟨k,hk⟩ := IsPGroup.iff_orderOf.mp hQ r
  rw [hk,show orderOf g.val = 5 by simpa only [Subgroup.orderOf_coe] using hg]
  exact Nat.Coprime.pow_left k hpfive

theorem excluded
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 67)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (p : ℕ) (hp : p.Prime) (hcases : p = 13 ∨ p = 17 ∨ p = 19 ∨ p = 23)
    (Q : Subgroup P) (hQ : IsPGroup p Q)
    (hQcard : Nat.card Q ≤ if p = 19 then 19 else p ^ 2)
    (hlower : 15 ≤ Nat.card (fixedPoints Q X))
    (hfixed : Nat.card (fixedPoints Q X) ≤ 33)
    (g : Subgroup.normalizer (Q : Set P)) (hg : orderOf g = 5) : False := by
  have hc := Degree58LargePrimeFiveCentralizer.centralizes p hp hcases Q hQ hQcard g (hg ▸ pow_orderOf_eq_one g)
  have hsub : (fixedPoints Q X)ᶜ ⊆ Function.fixedPoints g.val.val := by
    intro x hx
    exact fixes_outside (by rwa [Nat.card_eq_fintype_card]) p hp (by rcases hcases with rfl | rfl | rfl | rfl <;> omega)
      (by rcases hcases with rfl | rfl | rfl | rfl <;> decide) Q hQ hlower g hg hc x hx
  have hle := Set.ncard_le_ncard hsub
  rw [Set.ncard_compl,← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,
    Nat.card_eq_fintype_card (α := X),hcard] at hle
  have hne : g.val.val ≠ 1 := by
    intro hh
    have hgone : g = 1 := Subtype.ext (Subtype.ext hh)
    rw [hgone,orderOf_one] at hg
    omega
  have hb := HighDegreeManningSupport.degree_le_two_mul_support P (by omega) h5 hnotAlt
    g.val.property hne
  rw [hcard] at hb
  rw [Nat.card_eq_fintype_card (α := Function.fixedPoints g.val.val),Equiv.Perm.card_fixedPoints,g.val.val.sum_cycleType,hcard] at hle
  omega

end FiveTransitive.Degree67LargePrimeFiveCentralizer

end CFSG
