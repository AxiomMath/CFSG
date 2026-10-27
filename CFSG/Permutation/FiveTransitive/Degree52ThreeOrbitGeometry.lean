module

public import CFSG.Permutation.FiveTransitive.ThreeGroupOrbitSevenFixed
public import CFSG.Permutation.FiveTransitive.Degree52ThreeLargeOrbit
public import CFSG.Permutation.FiveTransitive.OrbitFixedComplementBound
public import CFSG.Permutation.FiveTransitive.AbelianOrbitEvaluation

public section

namespace CFSG

namespace FiveTransitive.Degree52ThreeOrbitGeometry

open MulAction

theorem orbit_card_three_of_fixed_difference
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hX : Nat.card X = 52) (Q : Subgroup G) (hQ : IsPGroup 3 Q)
    (hQfixed : Nat.card (fixedPoints Q X) = 7)
    (g : Subgroup.normalizer (Q : Set G)) (hg : orderOf g = 7)
    (hcount : Nat.card (fixedBy X g.val) =
      Nat.card {x : fixedPoints Q X // g.val • x.val = x.val} + 3)
    (x : X) (hx : x ∉ fixedPoints Q X) : Nat.card (orbit Q x) = 3 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hg7 : g ^ 7 = 1 := by simpa only [hg] using pow_orderOf_eq_one g
  have hb := OrbitFixedComplementBound.card_le (G := Q) x
  rw [hX,hQfixed] at hb
  have hsmall : Nat.card (orbit Q x) < 81 := by omega
  have hlt : Nat.card (orbit Q x) < 9 := by
    by_contra hn
    have hlarge : 9 ≤ Nat.card (orbit Q x) := by omega
    have hp := Degree52ThreeLargeOrbit.fixes_large_orbit Q (by omega : Nat.card X ≤ 52)
      g hg7 (Quotient.mk'' x) (by simpa only [orbitRel.Quotient.orbit_mk] using hlarge)
    have hpreserve : g.val • x ∈ orbit Q x := Quotient.exact (show
        (Quotient.mk'' (g.val • x) : orbitRel.Quotient Q X) = Quotient.mk'' x from hp)
    have hsub : orbit Q x ⊆ fixedBy X g.val := by
      intro y hy
      exact ThreeGroupOrbitSevenFixed.fixes_preserved_orbit Q hQ g.val g.property
        (congrArg Subtype.val hg7) x hsmall hpreserve y hy
    let E : Set X := fixedPoints Q X ∩ fixedBy X g.val
    let e : E ≃ {y : fixedPoints Q X // g.val • y.val = y.val} :=
      { toFun := fun y => ⟨⟨y.val,y.property.1⟩,y.property.2⟩
        invFun := fun y => ⟨y.val.val,⟨y.val.property,y.property⟩⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hdis : Disjoint E (orbit Q x) :=
      (AbelianOrbitEvaluation.orbit_disjoint_fixedPoints x hx).mono_left (fun _ h => h.1)
    have hunion : E ∪ orbit Q x ⊆ fixedBy X g.val := by
      intro y hy
      rcases hy with hy | hy
      · exact hy.2
      · exact hsub hy
    have hh := Set.ncard_le_ncard hunion
    rw [Set.ncard_union_eq hdis,← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,
      ← Nat.card_coe_set_eq,Nat.card_congr e,hcount] at hh
    omega
  obtain ⟨e,he⟩ := hQ.card_orbit x
  have he1 : e ≤ 1 := by
    by_contra hn
    have hp : 9 ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num : 0 < 3) (by omega : 2 ≤ e)
    rw [← he] at hp
    omega
  let _ : Fintype (orbit Q x) := Fintype.ofFinite _
  have hepos : 0 < e := by
    by_contra hn
    have he0 : e = 0 := by omega
    exact hx (mem_fixedPoints_iff_card_orbit_eq_one.mpr (by
      rw [← Nat.card_eq_fintype_card,he,he0,pow_zero]))
  rw [he,show e = 1 by omega,pow_one]

end FiveTransitive.Degree52ThreeOrbitGeometry

end CFSG
