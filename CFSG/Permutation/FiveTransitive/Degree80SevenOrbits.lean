module

public import CFSG.Permutation.FiveTransitive.Degree80SevenFiveLift
public import CFSG.Permutation.FiveTransitive.NormalizerOrbitFamily
public import CFSG.Permutation.FiveTransitive.Degree54SevenOrbitFiveFixed

public section

namespace CFSG

namespace FiveTransitive.Degree80SevenOrbits
open MulAction SylowFixedActionCore NormalizerOrbitFamily
open scoped BigOperators

private theorem orbit_card_cases
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 80) (Q : Subgroup G) (hQ : IsPGroup 7 Q)
    (O : orbitRel.Quotient Q X) : Nat.card O.orbit = 1 ∨
      Nat.card O.orbit = 7 ∨ Nat.card O.orbit = 49 := by
  let _ : Fact (Nat.Prime 7) := ⟨by decide⟩
  refine Quotient.inductionOn O ?_
  intro x
  rw [orbitRel.Quotient.orbit_mk]
  obtain ⟨e,he⟩ := hQ.card_orbit x
  have hb := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
  have he2 : e ≤ 2 := by
    by_contra hn
    have hp : 343 ≤ 7 ^ e := Nat.pow_le_pow_right (by decide : 0 < 7) (by omega : 3 ≤ e)
    rw [he] at hb
    omega
  rw [he]
  interval_cases e <;> norm_num

private theorem forty_nine_family_eq_zero
    {G X : Type*} [Group G] [Finite G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 80) (Q : Subgroup G) (hQ : IsPGroup 7 Q)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (hfixed : Nat.card (fixedBy X g.val) ≤ 40) :
    Nat.card (Family (X := X) Q 49) = 0 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let B := Family (X := X) Q 49
  let _ : Fintype B := Fintype.ofFinite _
  have hB := NormalizerOrbitFamily.card_mul_le (X := X) Q 49
  change Nat.card B * 49 ≤ Nat.card X at hB
  have hBle : Nat.card B ≤ 1 := by omega
  by_contra hn
  change Nat.card B ≠ 0 at hn
  have hBone : Nat.card B = 1 := by omega
  let a : Equiv.Perm B := NormalizerOrbitFamily.toPermHom (X := X) Q 49 g
  have ha5 : a ^ 5 = 1 := by rw [← map_pow,hg,map_one]
  have hnot : ¬ 5 ∣ Nat.card B := by rw [hBone]; decide
  obtain ⟨O,hO⟩ := Equiv.Perm.exists_fixed_point_of_prime (p := 5) (n := 1)
    (by simpa only [Nat.card_eq_fintype_card] using hnot) (by simpa only [pow_one] using ha5)
  have hpres : NormalizerOrbitHom.toPermHom (Y := X) Q g O.val = O.val :=
    congrArg Subtype.val hO
  obtain ⟨x,hx⟩ := O.val.nonempty_orbit
  have he : (Quotient.mk'' x : orbitRel.Quotient Q X) = O.val :=
    orbitRel.Quotient.mem_orbit.mp hx
  have hOrb : O.val.orbit = orbit Q x := by rw [← he,orbitRel.Quotient.orbit_mk]
  have hsmall : Nat.card (orbit Q x) < 343 := by
    have hh := Nat.card_le_card_of_injective (fun y : orbit Q x => y.val) Subtype.val_injective
    omega
  have hgx : g.val • x ∈ orbit Q x := by
    apply Quotient.exact (s := orbitRel Q X)
    change NormalizerOrbitHom.toPermHom (Y := X) Q g (Quotient.mk'' x) = Quotient.mk'' x
    rwa [he]
  have hsub : O.val.orbit ⊆ fixedBy X g.val := by
    intro y hy
    exact Degree54SevenOrbitFiveFixed.fixes_preserved_orbit Q hQ g.val g.property
      (congrArg Subtype.val hg) x hsmall hgx y (hOrb ▸ hy)
  have hb := Set.ncard_le_ncard hsub
  rw [← Nat.card_coe_set_eq,← Nat.card_coe_set_eq,O.property] at hb
  omega

theorem exterior_orbit_card_seven
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 80)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 7 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1)
    (x : X) (hx : x ∉ fixedPoints (sylowImage X P s S) X) :
    Nat.card (orbit (sylowImage X P s S) x) = 7 := by
  classical
  let Q := sylowImage X P s S
  have hQ : IsPGroup 7 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  obtain ⟨g,hg,hfix⟩ := Degree80SevenFiveLift.exists_normalizer_five
    P hcard h5 hnotAlt s hs S hS
  have hX : Nat.card X ≤ 80 := by rw [Nat.card_eq_fintype_card,hcard]
  have hn49 := forty_nine_family_eq_zero hX Q hQ g
    (hg ▸ pow_orderOf_eq_one g) hfix
  have hn1 : Nat.card (orbit Q x) ≠ 1 := by
    intro he
    apply hx
    exact mem_fixedPoints_iff_card_orbit_eq_one.mpr (by rwa [← Nat.card_eq_fintype_card])
  have hc := orbit_card_cases hX Q hQ (Quotient.mk'' x)
  rw [orbitRel.Quotient.orbit_mk] at hc
  rcases hc with hc | hc | hc
  · exact (hn1 hc).elim
  · exact hc
  · have hp : 0 < Nat.card (Family (X := X) Q 49) :=
      Finite.card_pos_iff.mpr ⟨⟨Quotient.mk'' x,by rwa [orbitRel.Quotient.orbit_mk]⟩⟩
    omega

theorem card_eq_fixed_add_seven_mul_family
    {G X : Type*} [Group G] [MulAction G X] [Finite X] (Q : Subgroup G)
    (hsize : ∀ O : orbitRel.Quotient Q X, Nat.card O.orbit = 1 ∨ Nat.card O.orbit = 7) :
    Nat.card X = Nat.card (fixedPoints Q X) + 7 * Nat.card (Family (X := X) Q 7) := by
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
      (if Nat.card O.orbit = 1 then 1 else 0) + 7 * (if Nat.card O.orbit = 7 then 1 else 0) := by
    rcases hsize O with h | h <;> rw [h] <;> norm_num
  rw [he]
  calc
    ∑ O : orbitRel.Quotient Q X, Nat.card O.orbit =
        ∑ O : orbitRel.Quotient Q X,
          ((if Nat.card O.orbit = 1 then 1 else 0) + 7 * (if Nat.card O.orbit = 7 then 1 else 0)) :=
      Finset.sum_congr rfl (fun O _ => hterm O)
    _ = _ := by simp only [Finset.sum_add_distrib,← Finset.mul_sum,← hcount,fixed_family_card]

end FiveTransitive.Degree80SevenOrbits

end CFSG
