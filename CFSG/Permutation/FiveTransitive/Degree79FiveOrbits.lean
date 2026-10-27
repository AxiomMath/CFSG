module

public import CFSG.Permutation.FiveTransitive.Degree58FiveOrbitSevenFixed
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFamily

public section

namespace CFSG

namespace FiveTransitive.Degree79FiveOrbits
open MulAction NormalizerOrbitFamily
open scoped BigOperators

private theorem orbit_card_cases
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 79) (Q : Subgroup G) (hQ : IsPGroup 5 Q)
    (O : orbitRel.Quotient Q X) : Nat.card O.orbit = 1 ∨
      Nat.card O.orbit = 5 ∨ Nat.card O.orbit = 25 := by
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  refine Quotient.inductionOn O ?_
  intro x
  rw [orbitRel.Quotient.orbit_mk]
  obtain ⟨e,he⟩ := hQ.card_orbit x
  have hb := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
  have he2 : e ≤ 2 := by
    by_contra hn
    have hp : 125 ≤ 5 ^ e := Nat.pow_le_pow_right (by decide : 0 < 5) (by omega : 3 ≤ e)
    rw [he] at hb
    omega
  rw [he]
  interval_cases e <;> norm_num

private theorem twenty_five_family_eq_zero
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 79) (Q : Subgroup G) (hQ : IsPGroup 5 Q)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 7 = 1)
    (hfixed : Nat.card (fixedBy X g.val) ≤ 9) :
    Nat.card (Family (X := X) Q 25) = 0 := by
  classical
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  let B := Family (X := X) Q 25
  let _ : Fintype B := Fintype.ofFinite _
  have hB := NormalizerOrbitFamily.card_mul_le (X := X) Q 25
  change Nat.card B * 25 ≤ Nat.card X at hB
  have hBle : Nat.card B ≤ 3 := by omega
  by_contra hn
  change Nat.card B ≠ 0 at hn
  have hBpos : 0 < Nat.card B := by omega
  let a : Equiv.Perm B := NormalizerOrbitFamily.toPermHom (X := X) Q 25 g
  have ha7 : a ^ 7 = 1 := by rw [← map_pow,hg,map_one]
  have hnot : ¬ 7 ∣ Nat.card B := by omega
  obtain ⟨O,hO⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 7) (n := 1)
    (by simpa only [Nat.card_eq_fintype_card] using hnot) (by simpa only [pow_one] using ha7)
  have hpres : NormalizerOrbitHom.toPermHom (Y := X) Q g O.val = O.val :=
    congrArg Subtype.val hO
  obtain ⟨x,hx⟩ := O.val.nonempty_orbit
  have he : (Quotient.mk'' x : orbitRel.Quotient Q X) = O.val :=
    orbitRel.Quotient.mem_orbit.mp hx
  have hOrb : O.val.orbit = orbit Q x := by rw [← he,orbitRel.Quotient.orbit_mk]
  have hsmall : Nat.card (orbit Q x) < 125 := by
    have hh := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
    omega
  have hgx : g.val • x ∈ orbit Q x := by
    apply Quotient.exact (s := orbitRel Q X)
    change NormalizerOrbitHom.toPermHom (Y := X) Q g (Quotient.mk'' x) = Quotient.mk'' x
    rwa [he]
  have hsub : O.val.orbit ⊆ fixedBy X g.val := by
    intro y hy
    exact Degree58FiveOrbitSevenFixed.fixes_preserved_orbit Q hQ g.val g.property
      (congrArg Subtype.val hg) x hsmall hgx y (hOrb ▸ hy)
  have hb := Set.ncard_le_ncard hsub
  rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,O.property] at hb
  omega

theorem exterior_orbit_card_five
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 79) (Q : Subgroup G) (hQ : IsPGroup 5 Q)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 7 = 1)
    (hfixed : Nat.card (fixedBy X g.val) ≤ 9)
    (x : X) (hx : x ∉ fixedPoints Q X) : Nat.card (orbit Q x) = 5 := by
  classical
  let _ : Fintype X := Fintype.ofFinite _
  have hn25 := twenty_five_family_eq_zero hX Q hQ g hg hfixed
  have hn1 : Nat.card (orbit Q x) ≠ 1 := by
    intro he
    apply hx
    exact mem_fixedPoints_iff_card_orbit_eq_one.mpr (by rwa [← Nat.card_eq_fintype_card])
  have hc := orbit_card_cases hX Q hQ (Quotient.mk'' x)
  rw [orbitRel.Quotient.orbit_mk] at hc
  rcases hc with hc | hc | hc
  · exact (hn1 hc).elim
  · exact hc
  · have hp : 0 < Nat.card (Family (X := X) Q 25) :=
      Finite.card_pos_iff.mpr ⟨⟨Quotient.mk'' x,by rwa [orbitRel.Quotient.orbit_mk]⟩⟩
    omega

private theorem card_eq_fixed_add_five_mul_family
    {G X : Type*} [Group G] [MulAction G X] [Finite X] (Q : Subgroup G)
    (hsize : ∀ O : orbitRel.Quotient Q X, Nat.card O.orbit = 1 ∨ Nat.card O.orbit = 5) :
    Nat.card X = Nat.card (fixedPoints Q X) + 5 * Nat.card (Family (X := X) Q 5) := by
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
      (if Nat.card O.orbit = 1 then 1 else 0) + 5 * (if Nat.card O.orbit = 5 then 1 else 0) := by
    rcases hsize O with h | h <;> rw [h] <;> norm_num
  rw [he]
  calc
    ∑ O : orbitRel.Quotient Q X, Nat.card O.orbit =
        ∑ O : orbitRel.Quotient Q X,
          ((if Nat.card O.orbit = 1 then 1 else 0) + 5 * (if Nat.card O.orbit = 5 then 1 else 0)) :=
      Finset.sum_congr rfl (fun O _ => hterm O)
    _ = _ := by simp only [Finset.sum_add_distrib,← Finset.mul_sum,← hcount,fixed_family_card]

theorem five_family_card
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (hX : Nat.card X = 79) (Q : Subgroup G) (hQ : IsPGroup 5 Q)
    (hF : Nat.card (fixedPoints Q X) = 9)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 7 = 1)
    (hfixed : Nat.card (fixedBy X g.val) ≤ 9) :
    Nat.card (Family (X := X) Q 5) = 14 := by
  classical
  let _ : Fintype X := Fintype.ofFinite _
  have hsize (O : orbitRel.Quotient Q X) : Nat.card O.orbit = 1 ∨ Nat.card O.orbit = 5 := by
    refine Quotient.inductionOn O ?_
    intro x
    rw [orbitRel.Quotient.orbit_mk]
    by_cases hx : x ∈ fixedPoints Q X
    · left
      rw [Nat.card_eq_fintype_card]
      exact mem_fixedPoints_iff_card_orbit_eq_one.mp hx
    · exact Or.inr (exterior_orbit_card_five hX.le Q hQ g hg hfixed x hx)
  have hm := card_eq_fixed_add_five_mul_family Q hsize
  rw [hX,hF] at hm
  omega

end FiveTransitive.Degree79FiveOrbits

end CFSG
