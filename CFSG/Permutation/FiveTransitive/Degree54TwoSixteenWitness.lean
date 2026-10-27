module

public import CFSG.Permutation.FiveTransitive.Degree54TwoOrbitRestriction
public import CFSG.Permutation.FiveTransitive.Degree52TwoOrbitPreserved
public import CFSG.Permutation.FiveTransitive.Degree52TwoOrderImage

public section

namespace CFSG

namespace FiveTransitive.Degree54TwoSixteenWitness

open MulAction
open scoped BigOperators

theorem exists_sixteen
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 54) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (hfixed : Nat.card {x : X // x ∉ fixedPoints Q X ∧ g.val • x = x} = 3) :
    ∃ x : X, x ∉ fixedPoints Q X ∧ g.val • x = x ∧
      Nat.card (orbit Q x) = 16 ∧
      Nat.card {y : orbit Q x // g.val • y.val = y.val} = 1 := by
  classical
  let _ : Fintype X := Fintype.ofFinite _
  let _ : Fintype (orbitRel.Quotient Q X) := Fintype.ofFinite _
  let B := {x : X // x ∉ fixedPoints Q X ∧ g.val • x = x}
  let f : B → orbitRel.Quotient Q X := fun x => Quotient.mk'' x.val
  have hsum : Nat.card B = ∑ O : orbitRel.Quotient Q X, Nat.card {x : B // f x = O} := by
    rw [← Nat.card_congr (Equiv.sigmaFiberEquiv f),Nat.card_sigma]
  by_contra hn
  have heven (O : orbitRel.Quotient Q X) : 2 ∣ Nat.card {x : B // f x = O} := by
    by_cases hzero : Nat.card {x : B // f x = O} = 0
    · rw [hzero]
      exact dvd_zero 2
    have hpos : 0 < Nat.card {x : B // f x = O} := Nat.pos_of_ne_zero hzero
    obtain ⟨z⟩ : Nonempty {x : B // f x = O} := (Nat.card_pos_iff.mp hpos).1
    let x := z.val.val
    have hx : x ∉ fixedPoints Q X := z.val.property.1
    have hgx : g.val • x = x := z.val.property.2
    have hO : Nat.card (orbit Q x) ≠ 1 := by
      intro he
      apply hx
      apply mem_fixedPoints_iff_card_orbit_eq_one.mpr
      rwa [← Nat.card_eq_fintype_card]
    have hpres : NormalizerOrbitHom.toPermHom (Y := X) Q g (Quotient.mk'' x) =
        Quotient.mk'' x := by
      change Quotient.mk'' (g.val • x) = Quotient.mk'' x
      rw [hgx]
    have hnot (y : orbit Q x) : y.val ∉ fixedPoints Q X := by
      apply Degree52TwoOrbitPreserved.not_fixed_of_mem Q (Quotient.mk'' x)
      · rwa [orbitRel.Quotient.orbit_mk]
      · simpa only [orbitRel.Quotient.orbit_mk] using y.property
    let E : {w : B // f w = O} ≃ {y : orbit Q x // g.val • y.val = y.val} :=
      { toFun := fun w => ⟨⟨w.val.val,Quotient.exact (w.property.trans z.property.symm)⟩,
          w.val.property.2⟩
        invFun := fun y => ⟨⟨y.val.val,hnot y.val,y.property⟩,
          (Quotient.sound y.val.property).trans z.property⟩
        left_inv := fun _ => rfl
        right_inv := fun _ => rfl }
    have hlocal : Nat.card {y : orbit Q x // g.val • y.val = y.val} ≤ 3 := by
      rw [← hfixed,← Nat.card_congr E]
      exact Nat.card_le_card_of_injective Subtype.val Subtype.val_injective
    have hc := Degree54TwoOrbitRestriction.fixed_card_cases hX Q hQ g hg x hO hpres hlocal
    have h16 : ¬ (Nat.card (orbit Q x) = 16 ∧
        Nat.card {y : orbit Q x // g.val • y.val = y.val} = 1) := by
      intro hh
      exact hn ⟨x,hx,hgx,hh⟩
    have hc2 : Nat.card {y : orbit Q x // g.val • y.val = y.val} = 2 := by
      rcases hc with h | h | h
      · exact h.2
      · exact (h16 h).elim
      · exact h.2
    rw [Nat.card_congr E,hc2]
  have hd : 2 ∣ Nat.card B := by
    rw [hsum]
    exact Finset.dvd_sum (fun O _ => heven O)
  change 2 ∣ Nat.card {x : X // x ∉ fixedPoints Q X ∧ g.val • x = x} at hd
  rw [hfixed] at hd
  norm_num at hd

theorem exists_regular_sixteen
    {G X : Type*} [Group G] [MulAction G X] [Finite X]
    (hX : Nat.card X ≤ 54) (Q : Subgroup G) (hQ : IsPGroup 2 Q)
    (g : Subgroup.normalizer (Q : Set G)) (hg : g ^ 5 = 1)
    (hfixed : Nat.card {x : X // x ∉ fixedPoints Q X ∧ g.val • x = x} = 3) :
    ∃ x : X, g.val • x = x ∧ Nat.card (orbit Q x) = 16 ∧
      Nat.card (toPermHom Q (orbit Q x)).range = 16 := by
  obtain ⟨x,_,hx,hO,hlocal⟩ := exists_sixteen hX Q hQ g hg hfixed
  have hsub : Subsingleton {y : orbit Q x // g.val • y.val = y.val} :=
    Finite.card_le_one_iff_subsingleton.mp hlocal.le
  have hunique (y : X) (hy : y ∈ orbit Q x) (hgy : g.val • y = y) : y = x := by
    have he : (⟨⟨y,hy⟩,hgy⟩ : {y : orbit Q x // g.val • y.val = y.val}) =
        ⟨⟨x,mem_orbit_self x⟩,hx⟩ := hsub.elim _ _
    exact congrArg (fun z => z.val.val) he
  exact ⟨x,hx,hO,Degree52TwoOrderImage.image_card_sixteen Q hQ g hg x hO hx hunique⟩

end FiveTransitive.Degree54TwoSixteenWitness

end CFSG
