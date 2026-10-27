module

public import CFSG.Permutation.FiveTransitive.Degree54ThreeFixed
public import CFSG.Permutation.FiveTransitive.Degree54ThreeOrbitGeometry
public import CFSG.Permutation.FiveTransitive.Degree54ThreeSixImage
public import CFSG.Permutation.FiveTransitive.Degree54FiveFree

public section

namespace CFSG

namespace FiveTransitive.Degree54ThreeStructure

open MulAction SylowFixedActionCore NormalizerOrbitFamily

theorem exists_five_fixed_four
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    ∃ g : sylowNormalizer X P s S, orderOf g = 5 ∧ Nat.card (fixedBy X g.val) = 4 := by
  classical
  let _ : Fact (Nat.Prime 5) := ⟨by decide⟩
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let rho := MulAction.toPermHom N F
  obtain ⟨hF,him⟩ := Degree54ThreeFixed.fixed_card_and_image P hcard h5 hnotAlt s hs S hS
  have hd : 5 ∣ Nat.card rho.range := by
    rw [him,Subgroup.card_top,Nat.card_perm,hF]
    norm_num [Nat.factorial]
  obtain ⟨g,hg⟩ := exists_prime_orderOf_dvd_card' (G := N) 5
    (hd.trans (Subgroup.card_range_dvd rho))
  exact ⟨g,hg,Degree54FiveFree.fixed_card_eq_four P hcard h5 hnotAlt g.val
    ((Subgroup.orderOf_coe g).trans hg)⟩

private theorem nine_family_ne_five
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    Nat.card (Family (X := X) (sylowImage X P s S) 9) ≠ 5 := by
  classical
  intro hE
  let Q := sylowImage X P s S
  let N := sylowNormalizer X P s S
  let F := sylowFixedPoints X P s S
  let _ : Fintype F := Fintype.ofFinite F
  let E := Family (X := X) Q 9
  let rho := MulAction.toPermHom N F
  let sigma := NormalizerOrbitFamily.toPermHom (X := X) Q 9
  obtain ⟨hF,him⟩ := Degree54ThreeFixed.fixed_card_and_image P hcard h5 hnotAlt s hs S hS
  obtain ⟨g,hg,hker⟩ := Degree54ThreeSixImage.exists_five_in_kernel hF hE rho sigma him
  have hQ : IsPGroup 3 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hfixed : Nat.card (fixedBy X g.val) = 4 :=
    Degree54FiveFree.fixed_card_eq_four P hcard h5 hnotAlt g.val ((Subgroup.orderOf_coe g).trans hg)
  have hEcard : Nat.card E = 5 := hE
  have hne : Nonempty E := Finite.card_pos_iff.mp (by rw [hEcard]; decide)
  obtain ⟨O⟩ := hne
  have hpres : NormalizerOrbitHom.toPermHom (Y := X) Q g O.val = O.val := by
    have he := congrArg (fun f : Equiv.Perm E => f O) hker
    exact congrArg Subtype.val he
  have hb := Degree54ThreeOrbitGeometry.preserved_card_le_four
    (by rw [Nat.card_eq_fintype_card,hcard]) Q hQ g (hg ▸ pow_orderOf_eq_one g) hfixed O.val hpres
  rw [O.property] at hb
  omega

theorem exterior_orbit_card_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 54)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5) (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1) :
    ∀ x : X, x ∉ fixedPoints (sylowImage X P s S) X →
      Nat.card (orbit (sylowImage X P s S) x) = 3 := by
  classical
  let Q := sylowImage X P s S
  have hQ : IsPGroup 3 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hX : Nat.card X = 54 := by rwa [Nat.card_eq_fintype_card]
  have hcommon : Nat.card (fixedPoints Q X) = 6 := by
    rw [← FixedNormalizerAction.fixed_eq Q]
    exact Degree54ThreeFixed.fixed_card_eq_six P hcard h5 hnotAlt s hs S hS
  obtain ⟨g,hg,hfixed⟩ := exists_five_fixed_four P hcard h5 hnotAlt s hs S hS
  obtain ⟨hcases,hgeom⟩ := Degree54ThreeOrbitGeometry.orbit_geometry hX Q hQ hcommon g
    (hg ▸ pow_orderOf_eq_one g) hfixed
  have h9zero : Nat.card (Family (X := X) Q 9) = 0 := by
    have hn := nine_family_ne_five P hcard h5 hnotAlt s hs S hS
    change Nat.card (Family (X := X) Q 9) ≠ 5 at hn
    omega
  intro x hx
  change Nat.card (orbit Q x) = 3
  have hcasesx := hcases (Quotient.mk'' x)
  rw [orbitRel.Quotient.orbit_mk] at hcasesx
  have hn1 : Nat.card (orbit Q x) ≠ 1 := by
    intro he
    apply hx
    exact mem_fixedPoints_iff_card_orbit_eq_one.mpr (by rwa [← Nat.card_eq_fintype_card])
  have hn9 : Nat.card (orbit Q x) ≠ 9 := by
    intro he
    have hp : 0 < Nat.card (Family (X := X) Q 9) :=
      Finite.card_pos_iff.mpr ⟨⟨Quotient.mk'' x,by rwa [orbitRel.Quotient.orbit_mk]⟩⟩
    omega
  omega

end FiveTransitive.Degree54ThreeStructure

end CFSG
