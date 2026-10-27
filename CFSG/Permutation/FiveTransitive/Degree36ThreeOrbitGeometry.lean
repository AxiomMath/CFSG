module

public import CFSG.Permutation.FiveTransitive.ThreeGroupOrbitFiveFixed
public import CFSG.Permutation.FiveTransitive.NormalizerLargeOrbit
public import CFSG.Permutation.FiveTransitive.Degree36OrderFiveFixed

public section

namespace CFSG

namespace FiveTransitive.Degree36ThreeOrbitGeometry

open MulAction

private theorem orbit_card_three_of_fixed_bound
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hX : Nat.card X = 36) (Q : Subgroup G) (hQ : IsPGroup 3 Q)
    (hQfixed : Nat.card (fixedPoints Q X) = 6)
    (g : Subgroup.normalizer (Q : Set G)) (hg : orderOf g = 5)
    (hfixed : 5 ≤ Nat.card (fixedBy X g) → Nat.card (fixedBy X g) = 6)
    (x : X) (hx : x ∉ fixedPoints Q X) : Nat.card (orbit Q x) = 3 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hg5 : g ^ 5 = 1 := by simpa only [hg] using pow_orderOf_eq_one g
  have hb := OrbitFixedComplementBound.card_le (G := Q) x
  rw [hX,hQfixed] at hb
  have hsmall : Nat.card (orbit Q x) < 81 := by omega
  have hlt : Nat.card (orbit Q x) < 9 := by
    by_contra hn
    have hlarge : 9 ≤ Nat.card (orbit Q x) := by omega
    have hp := NormalizerLargeOrbit.fixes_large_orbit Q (by omega : Nat.card X ≤ 36)
      g hg5 (Quotient.mk'' x) (by simpa only [orbitRel.Quotient.orbit_mk] using hlarge)
    have hpreserve : g.val • x ∈ orbit Q x := Quotient.exact (show
        (Quotient.mk'' (g.val • x) : orbitRel.Quotient Q X) = Quotient.mk'' x from hp)
    have hsub : orbit Q x ⊆ fixedBy X g := by
      intro y hy
      exact ThreeGroupOrbitFiveFixed.fixes_preserved_orbit Q hQ g.val g.property
        (congrArg Subtype.val hg5) x hsmall hpreserve y hy
    have hh := Set.ncard_le_ncard hsub
    rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq] at hh
    have hsix := hfixed (by omega)
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
  have heq : e = 1 := by omega
  rw [he,heq,pow_one]

theorem orbit_card_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (Q : Subgroup P) (hQ : IsPGroup 3 Q)
    (hQfixed : Nat.card (fixedPoints Q X) = 6)
    (g : Subgroup.normalizer (Q : Set P)) (hg : orderOf g = 5)
    (x : X) (hx : x ∉ fixedPoints Q X) : Nat.card (orbit Q x) = 3 := by
  apply orbit_card_three_of_fixed_bound
    (by rw [Nat.card_eq_fintype_card,hcard]) Q hQ hQfixed g hg ?_ x hx
  intro hfixed
  have horder : orderOf g.val = 5 := by simpa only [Subgroup.orderOf_coe] using hg
  exact Degree36OrderFiveFixed.fixed_card_eq_six P hcard h5 hnotAlt g.val horder hfixed

end FiveTransitive.Degree36ThreeOrbitGeometry

end CFSG
