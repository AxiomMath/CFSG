module

public import CFSG.Permutation.FiveTransitive.PointStabilizerFixedSign
public import CFSG.Permutation.FiveTransitive.SylowFixedSixImageExclusion
public import CFSG.Permutation.FiveTransitive.PointStabilizerSylow

public section

namespace CFSG

namespace FiveTransitive.SylowFixedSevenExclusion

open MulAction SubMulAction GenericSylowFixedAction PointStabilizerSylow

theorem not_seven_of_even_fixed
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (h5 : IsMultiplyPretransitive G X 5) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s)) (hS : (S : Subgroup (fixingSubgroup G s)) ≠ ⊥)
    (hseven : Nat.card (sylowFixedPoints G X s S) = 7)
    (heven : EvenSixTupleLocal.EvenFixed G X (sylowImage G X s S)) : False := by
  classical
  let Q := sylowImage G X s S
  let F := fixedPoints Q X
  have hF : Nat.card F = 7 := by
    rwa [SylowFixedSixImageExclusion.internal_fixed_eq] at hseven
  have hnot : ¬ F ⊆ s := by
    intro hf
    have hle := Set.ncard_le_ncard hf
    rw [← Nat.card_coe_set_eq, hF, hs] at hle
    omega
  obtain ⟨x,hxF,hxs⟩ := Set.not_subset.mp hnot
  have hx : ∀ q : S, q • x = x := by
    intro q
    exact hxF ⟨q.val.val, ⟨q.val,q.property,rfl⟩⟩
  let H := stabilizer G x
  let Y := ofStabilizer G x
  let _ : Fintype Y := Fintype.ofFinite Y
  let _ : FaithfulSMul H Y := ⟨by
    intro a b hab
    apply Subtype.ext
    apply FaithfulSMul.eq_of_smul_eq_smul (α := X)
    intro y
    by_cases he : y = x
    · rw [he, a.property, b.property]
    · exact congrArg Subtype.val (hab ⟨y,he⟩)⟩
  let t := restrictedBase G X s x
  let T := restrictedSylow G X s x hxs S hx
  let R := sylowImage H Y t T
  have hmap : R.map H.subtype = Q := restrictedSylow_image G X s x hxs S hx
  have ht : t.ncard = 4 := (restrictedBase_card G X s x hxs).trans hs
  have hT : (T : Subgroup (fixingSubgroup H t)) ≠ ⊥ := by
    intro he
    have hQ : Q = ⊥ := by
      rw [← hmap]
      change (((T : Subgroup (fixingSubgroup H t)).map (fixingSubgroup H t).subtype).map H.subtype) = ⊥
      rw [he, Subgroup.map_bot, Subgroup.map_bot]
    apply hS
    exact (Subgroup.map_eq_bot_iff_of_injective (S : Subgroup (fixingSubgroup G s)) (fixingSubgroup G s).subtype_injective).mp hQ
  have hYfix : Nat.card (fixedPoints R Y) = 6 := by
    have hc := PointStabilizerFixedSet.fixed_card G X x R
    rw [hmap, hF] at hc
    exact hc
  have hYeven : EvenSixTupleLocal.EvenFixed H Y R := by
    have hev : EvenSixTupleLocal.EvenFixed G X (R.map H.subtype) := by rwa [hmap]
    intro g hg
    exact (PointStabilizerFixedSign.sign_fixedPerm G X x R g hg).trans
      (hev g.val (PointStabilizerFixedSet.mem_normalizer_map G X x R g hg))
  have hX : 5 ≤ Nat.card X := by
    have hl := Nat.card_le_card_of_injective (f := fun y : F => y.val) Subtype.val_injective
    rw [hF] at hl
    omega
  let _ : IsMultiplyPretransitive G X 5 := h5
  let _ : IsPretransitive G X := is_one_pretransitive_iff.mp
    (isMultiplyPretransitive_of_le (G := G) (α := X) (n := 5) (by omega : 1 ≤ 5) hX)
  have hH4 : IsMultiplyPretransitive H Y 4 :=
    (ofStabilizer.isMultiplyPretransitive (G := G) (α := X) (a := x)).mp h5
  exact SylowFixedSixImageExclusion.not_even_fixed_six_set H Y hH4 t ht T hT hYfix hYeven

end FiveTransitive.SylowFixedSevenExclusion

end CFSG
