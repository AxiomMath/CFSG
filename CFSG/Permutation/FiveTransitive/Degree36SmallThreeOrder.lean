module

public import CFSG.Permutation.FiveTransitive.Degree36CentralizingFiveFree
public import CFSG.Permutation.FiveTransitive.Degree36SylowThreeStructure

public section

namespace CFSG

namespace FiveTransitive.Degree36SmallThreeOrder

open MulAction SylowFixedActionCore

theorem card_eq_three
    {X : Type} [Fintype X] [DecidableEq X]
    (P : Subgroup (Equiv.Perm X)) (hcard : Fintype.card X = 36)
    (h5 : IsMultiplyPretransitive P X 5) (hnotAlt : ¬ alternatingGroup X ≤ P)
    (s : Set X) (hs : s.ncard = 5)
    (S : Sylow 3 (fixingSubgroup P s)) (hS : Nat.card S ≠ 1)
    (hScard : Nat.card S ≤ 27) : Nat.card S = 3 := by
  classical
  let Q := sylowImage X P s S
  let F := sylowFixedPoints X P s S
  have hQ : IsPGroup 3 Q := S.isPGroup'.map (fixingSubgroup P s).subtype
  have hQcard : Nat.card Q = Nat.card S := Nat.card_congr
    ((S : Subgroup (fixingSubgroup P s)).equivMapOfInjective
      (fixingSubgroup P s).subtype Subtype.val_injective).toEquiv.symm
  have hF := (Degree36SmallPrimeEntrance.three_entrance P hcard h5 hnotAlt s hs S hS).1
  have hfixeq : (F : Set X) = fixedPoints Q X := FixedNormalizerAction.fixed_eq Q
  have hQfixed : Nat.card (fixedPoints Q X) = 6 := by rw [← hfixeq]; exact hF
  obtain ⟨g,hg,_,hglocal⟩ :=
    Degree36SylowThreeFiveLift.exists_five_fixed_one P hcard h5 hnotAlt s hs S hS
  let e : Function.fixedPoints (toPermHom (sylowNormalizer X P s S) F g) ≃
      {x : fixedPoints Q X // g.val • x.val = x.val} :=
    { toFun := fun x => ⟨⟨x.val.val,hfixeq ▸ x.val.property⟩,congrArg Subtype.val x.property⟩
      invFun := fun x => ⟨⟨x.val.val,hfixeq.symm ▸ x.val.property⟩,Subtype.ext x.property⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  have hlocal : Nat.card {x : fixedPoints Q X // g.val • x.val = x.val} = 1 := by
    rw [← Nat.card_congr e]
    exact hglocal
  obtain ⟨hcomm,hgfix⟩ := Degree36CentralizingFiveFree.centralizes_and_fixed_one
    P hcard h5 hnotAlt Q hQ (by omega) g hg hlocal
  have horder : orderOf g.val = 5 := by simpa only [Subgroup.orderOf_coe] using hg
  have hfree := Degree36CentralizingFiveFree.free_outside P hcard h5 hnotAlt
    Q hQ hQfixed g.val horder hgfix hcomm
  have hout : ∃ x : X, x ∉ fixedPoints Q X := by
    by_contra hn
    have he : fixedPoints Q X = Set.univ := Set.eq_univ_iff_forall.mpr (by simpa using hn)
    rw [he,Nat.card_coe_set_eq,Set.ncard_univ,Nat.card_eq_fintype_card,hcard] at hQfixed
    omega
  obtain ⟨x,hx⟩ := hout
  have hstab : stabilizer Q x = ⊥ := by
    apply bot_unique
    intro r hr
    exact Subgroup.mem_bot.mpr (hfree r x hx hr)
  have ho := Degree36SylowThreeStructure.orbit_card_three P hcard h5 hnotAlt s hs S hS x hx
  have hm := MinimalOrbitStabilizer.nat_card_orbit_mul_stabilizer Q X x
  rw [ho,hstab,Subgroup.card_bot,mul_one,hQcard] at hm
  exact hm.symm

end FiveTransitive.Degree36SmallThreeOrder

end CFSG
