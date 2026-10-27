module

public import CFSG.Permutation.FiveTransitive.ThreeGroupOrbitFiveFixed
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFamily

public section

namespace CFSG

namespace FiveTransitive.Degree69ThreeOrbitGeometry

open MulAction NormalizerOrbitFamily
open scoped BigOperators

private theorem orbit_card_cases
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 69) (Q : Subgroup G) (hQ : IsPGroup 3 Q)
    (O : orbitRel.Quotient Q X) : Nat.card O.orbit = 1 ∨
      Nat.card O.orbit = 3 ∨ Nat.card O.orbit = 9 ∨ Nat.card O.orbit = 27 := by
  refine Quotient.inductionOn O ?_
  intro x
  rw [orbitRel.Quotient.orbit_mk]
  obtain ⟨e,he⟩ := hQ.card_orbit x
  have hb := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
  have he3 : e ≤ 3 := by
    by_contra hn
    have hp : 81 ≤ 3 ^ e := Nat.pow_le_pow_right (by decide : 0 < 3) (by omega : 4 ≤ e)
    rw [he] at hb
    omega
  rw [he]
  interval_cases e <;> norm_num

theorem preserved_card_le_four
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 69) (Q : Subgroup G) (hQ : IsPGroup 3 Q)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (hfixed : Nat.card (fixedBy X g.val) = 4)
    (O : orbitRel.Quotient Q X)
    (hpres : NormalizerOrbitHom.toPermHom (Y := X) Q g O = O) :
    Nat.card O.orbit ≤ 4 := by
  obtain ⟨x,hx⟩ := O.nonempty_orbit
  have he : (Quotient.mk'' x : orbitRel.Quotient Q X) = O := orbitRel.Quotient.mem_orbit.mp hx
  have hO : O.orbit = orbit Q x := by rw [← he,orbitRel.Quotient.orbit_mk]
  have hsmall : Nat.card (orbit Q x) < 81 := by
    have hh := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
    omega
  have hgx : g.val • x ∈ orbit Q x := by
    apply Quotient.exact (s := orbitRel Q X)
    change NormalizerOrbitHom.toPermHom (Y := X) Q g (Quotient.mk'' x) = Quotient.mk'' x
    rwa [he]
  have hsub : O.orbit ⊆ fixedBy X g.val := by
    intro y hy
    exact ThreeGroupOrbitFiveFixed.fixes_preserved_orbit Q hQ g.val g.property
      (congrArg Subtype.val hg) x hsmall hgx y (hO ▸ hy)
  have hb := Set.ncard_le_ncard hsub
  rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,hfixed] at hb
  exact hb

private theorem five_dvd_family
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 69) (Q : Subgroup G) (hQ : IsPGroup 3 Q)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (hfixed : Nat.card (fixedBy X g.val) = 4)
    (m : ℕ) (hm : 4 < m) : 5 ∣ Nat.card (Family (X := X) Q m) := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let B := Family (X := X) Q m
  let _ : Fintype B := Fintype.ofFinite _
  let a := NormalizerOrbitFamily.toPermHom (X := X) Q m g
  have ha5 : a ^ 5 = 1 := by rw [← map_pow,hg,map_one]
  by_contra hn
  obtain ⟨O,hO⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 5) (n := 1)
    (by simpa only [Nat.card_eq_fintype_card] using hn) (by simpa only [pow_one] using ha5)
  have hb := preserved_card_le_four hX Q hQ g hg hfixed O.val (congrArg Subtype.val hO)
  rw [O.property] at hb
  omega

private theorem card_eq_orbit_sum
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 69) (Q : Subgroup G) (hQ : IsPGroup 3 Q) :
    Nat.card X = Nat.card (fixedPoints Q X) +
      3 * Nat.card (Family (X := X) Q 3) + 9 * Nat.card (Family (X := X) Q 9) +
      27 * Nat.card (Family (X := X) Q 27) := by
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
      3 * (if Nat.card O.orbit = 3 then 1 else 0) +
      9 * (if Nat.card O.orbit = 9 then 1 else 0) +
      27 * (if Nat.card O.orbit = 27 then 1 else 0) := by
    rcases orbit_card_cases hX Q hQ O with h | h | h | h <;> rw [h] <;> norm_num
  rw [he]
  calc
    ∑ O : orbitRel.Quotient Q X, Nat.card O.orbit =
        ∑ O : orbitRel.Quotient Q X,
          ((if Nat.card O.orbit = 1 then 1 else 0) +
          3 * (if Nat.card O.orbit = 3 then 1 else 0) +
          9 * (if Nat.card O.orbit = 9 then 1 else 0) +
          27 * (if Nat.card O.orbit = 27 then 1 else 0)) :=
      Finset.sum_congr rfl (fun O _ => hterm O)
    _ = _ := by
      simp only [Finset.sum_add_distrib,← Finset.mul_sum,← hcount,fixed_family_card]

theorem orbit_geometry
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (hX : Nat.card X = 69) (Q : Subgroup G) (hQ : IsPGroup 3 Q)
    (hcommon : Nat.card (fixedPoints Q X) = 6)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (hfixed : Nat.card (fixedBy X g.val) = 4) :
    (∀ O : orbitRel.Quotient Q X, Nat.card O.orbit = 1 ∨
      Nat.card O.orbit = 3 ∨ Nat.card O.orbit = 9) ∧
    ((Nat.card (Family (X := X) Q 3) = 21 ∧ Nat.card (Family (X := X) Q 9) = 0) ∨
     (Nat.card (Family (X := X) Q 3) = 6 ∧ Nat.card (Family (X := X) Q 9) = 5)) := by
  have h9 := five_dvd_family hX.le Q hQ g hg hfixed 9 (by decide)
  have h27 := five_dvd_family hX.le Q hQ g hg hfixed 27 (by decide)
  have hm := card_eq_orbit_sum hX.le Q hQ
  rw [hX,hcommon] at hm
  have h27zero : Nat.card (Family (X := X) Q 27) = 0 := by omega
  refine ⟨?_,by omega⟩
  intro O
  have hnot27 : Nat.card O.orbit ≠ 27 := by
    intro he
    have hp : 0 < Nat.card (Family (X := X) Q 27) := Finite.card_pos_iff.mpr ⟨⟨O,he⟩⟩
    omega
  have hc := orbit_card_cases hX.le Q hQ O
  omega

end FiveTransitive.Degree69ThreeOrbitGeometry

end CFSG
