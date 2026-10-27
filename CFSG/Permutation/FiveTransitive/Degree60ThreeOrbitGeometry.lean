module

public import CFSG.Permutation.FiveTransitive.ThreeGroupOrbitElevenFixed
public import CFSG.Permutation.FiveTransitive.Degree60ThreeLargeOrbit
public import CFSG.Permutation.FiveTransitive.AbelianOrbitEvaluation

public section

namespace CFSG

namespace FiveTransitive.Degree60ThreeOrbitGeometry

open MulAction

private theorem large_orbit_fixed
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hX : Nat.card X = 60) (Q : Subgroup G) (hQ : IsPGroup 3 Q)
    (g : Subgroup.normalizer (Q : Set G)) (hg : orderOf g = 11)
    (x : X) (hx : 9 ≤ Nat.card (orbit Q x)) : orbit Q x ⊆ fixedBy X g := by
  have hgpow : g ^ 11 = 1 := hg ▸ pow_orderOf_eq_one g
  have hp := Degree60ThreeLargeOrbit.fixes_large_orbit Q (by omega : Nat.card X ≤ 60)
    g hgpow (Quotient.mk'' x) (by simpa only [orbitRel.Quotient.orbit_mk] using hx)
  have hpreserve : g.val • x ∈ orbit Q x := Quotient.exact (show
      (Quotient.mk'' (g.val • x) : orbitRel.Quotient Q X) = Quotient.mk'' x from hp)
  have hsmall : Nat.card (orbit Q x) < 81 := by
    have h := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
    omega
  intro y hy
  exact ThreeGroupOrbitElevenFixed.fixes_preserved_orbit Q hQ g.val g.property
    (congrArg Subtype.val hgpow) x hsmall hpreserve y hy

theorem orbit_card_cases
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hX : Nat.card X = 60) (Q : Subgroup G) (hQ : IsPGroup 3 Q)
    (g : Subgroup.normalizer (Q : Set G)) (hg : orderOf g = 11)
    (hfixed : Nat.card (fixedBy X g) = 16)
    (x : X) (hx : x ∉ fixedPoints Q X) :
    Nat.card (orbit Q x) = 3 ∨ Nat.card (orbit Q x) = 9 := by
  classical
  let _ : Fact (Nat.Prime 3) := ⟨by decide⟩
  have hlt : Nat.card (orbit Q x) < 27 := by
    by_contra hn
    have hsub := large_orbit_fixed hX Q hQ g hg x (by omega)
    have h := Set.ncard_le_ncard hsub
    rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq] at h
    omega
  obtain ⟨e,he⟩ := hQ.card_orbit x
  have he2 : e ≤ 2 := by
    by_contra hn
    have hp : 27 ≤ 3 ^ e := Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 3 ≤ e)
    omega
  let _ : Fintype (orbit Q x) := Fintype.ofFinite _
  have hpos : 0 < e := by
    by_contra hn
    have he0 : e = 0 := by omega
    apply hx
    apply mem_fixedPoints_iff_card_orbit_eq_one.mpr
    rw [← Nat.card_eq_fintype_card,he,he0,pow_zero]
  have hc : e = 1 ∨ e = 2 := by omega
  rcases hc with h | h <;> rw [he,h] <;> norm_num

theorem orbit_card_le_three_outside_nine
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (hX : Nat.card X = 60) (Q : Subgroup G) (hQ : IsPGroup 3 Q)
    (g : Subgroup.normalizer (Q : Set G)) (hg : orderOf g = 11)
    (hfixed : Nat.card (fixedBy X g) = 16)
    (x : X) (hx : Nat.card (orbit Q x) = 9)
    (y : X) (hy : y ∉ orbit Q x) : Nat.card (orbit Q y) ≤ 3 := by
  classical
  by_cases hyF : y ∈ fixedPoints Q X
  · let _ : Fintype (orbit Q y) := Fintype.ofFinite _
    have h := mem_fixedPoints_iff_card_orbit_eq_one.mp hyF
    rw [← Nat.card_eq_fintype_card] at h
    omega
  rcases orbit_card_cases hX Q hQ g hg hfixed y hyF with h3 | h9
  · omega
  have hd := AbelianOrbitEvaluation.orbit_disjoint_of_notMem x y hy
  have hsub : orbit Q x ∪ orbit Q y ⊆ fixedBy X g := Set.union_subset
    (large_orbit_fixed hX Q hQ g hg x (by omega))
    (large_orbit_fixed hX Q hQ g hg y (by omega))
  have h := Set.ncard_le_ncard hsub
  rw [Set.ncard_union_eq hd,← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,
    ← Nat.card_coe_set_eq,hx,h9,hfixed] at h
  omega

end FiveTransitive.Degree60ThreeOrbitGeometry

end CFSG
