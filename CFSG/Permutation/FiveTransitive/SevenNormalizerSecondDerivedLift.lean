module

public import CFSG.Permutation.FiveTransitive.DerivedTwoLift
public import CFSG.Permutation.FiveTransitive.SevenSwapCentralizerSecondCommutator
public import CFSG.Permutation.FiveTransitive.FixedNormalizerCyclicPreimageSylow
public import CFSG.Permutation.FiveTransitive.FixedNormalizerLocalCard

public section

namespace CFSG

open scoped Classical

namespace FiveTransitive.SevenNormalizerSecondDerivedLift

open MulAction FixedNormalizerAction

theorem exists_two_lift
    {G X : Type*} [Group G] [Finite G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (hseven : Nat.card (Fixed (X := X) Q) = 7)
    (S : Sylow 2 (fixingSubgroup G (fixedPoints Q X)))
    (hS : (S : Subgroup (fixingSubgroup G (fixedPoints Q X))).map
      (fixingSubgroup G (fixedPoints Q X)).subtype = Q)
    (A : Subgroup G) (hA : IsPGroup 2 A) (hQA : Q ≤ A)
    (x : Normalizer Q) (hxA : (x : G) ∈ A)
    (himage : Image (X := X) Q = ⊤)
    (hlocal : (fixedBy X x.val ∩ fixedPoints Q X).ncard = 5) :
    let R := (Inside Q ⊔ Subgroup.zpowers x : Subgroup (Normalizer Q))
    let D := commutator (Subgroup.normalizer (R : Set (Normalizer Q)))
    ∃ y : D,
      y ∈ commutator D ∧
      IsPGroup 2 (Subgroup.zpowers y) ∧
      orderOf (toPermHom (Normalizer Q) (Fixed (X := X) Q) y.val.val) = 2 ∧
      Nat.card (Function.fixedPoints
        (toPermHom (Normalizer Q) (Fixed (X := X) Q) y.val.val)) = 3 := by
  classical
  let _ : Fintype (Fixed (X := X) Q) := Fintype.ofFinite _
  let f := toPermHom (Normalizer Q) (Fixed (X := X) Q)
  have hxswap := FixedNormalizerLocalCard.isSwap Q hseven x hlocal
  have hmap := FixedNormalizerCyclicPreimageSylow.normalizer_generated_map_eq_centralizer
    Q S hS A hA hQA x hxA himage hxswap.orderOf
  let R := (Inside Q ⊔ Subgroup.zpowers x : Subgroup (Normalizer Q))
  let N := Subgroup.normalizer (R : Set (Normalizer Q))
  let C := Subgroup.centralizer ({f x} : Set (Equiv.Perm (Fixed (X := X) Q)))
  let fC : N →* C :=
    { toFun := fun n => ⟨f n.val, hmap.le ⟨n.val, n.property, rfl⟩⟩
      map_one' := Subtype.ext (map_one f)
      map_mul' a b := Subtype.ext (map_mul f a.val b.val) }
  have hfC : Function.Surjective fC := by
    intro d
    obtain ⟨n, hn, hnd⟩ := hmap.ge d.property
    exact ⟨⟨n, hn⟩, Subtype.ext hnd⟩
  obtain ⟨d, hd, hd2, hd3, _⟩ :=
    SevenSwapCentralizerSecondCommutator.exists_double_swap hseven (f x) hxswap
  have hd2' : orderOf d = 2 :=
    (orderOf_injective (C.subtype.comp (commutator C).subtype)
      (fun a b h => Subtype.ext (Subtype.ext h)) d).symm.trans hd2
  have hderived : (commutator N).map fC = commutator C := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hfC]
    rfl
  let fD : commutator N →* commutator C :=
    { toFun := fun n => ⟨fC n.val, hderived.le ⟨n.val, n.property, rfl⟩⟩
      map_one' := Subtype.ext (map_one fC)
      map_mul' a b := Subtype.ext (map_mul fC a.val b.val) }
  have hfD : Function.Surjective fD := by
    intro d
    obtain ⟨n, hn, hnd⟩ := hderived.ge d.property
    exact ⟨⟨n, hn⟩, Subtype.ext hnd⟩
  have hsecond : (commutator (commutator N)).map fD = commutator (commutator C) := by
    rw [map_commutator_eq, MonoidHom.range_eq_top.mpr hfD]
    rfl
  obtain ⟨y, hy, hfy, htwo⟩ := DerivedTwoLift.exists_two_element fD d
    (by rw [hsecond]; exact hd) hd2'
  have hyf : f y.val.val = d.val.val := congrArg (fun z : commutator C => z.val.val) hfy
  refine ⟨y, hy, htwo, ?_, ?_⟩
  · change orderOf (f y.val.val) = 2
    rw [hyf]
    exact hd2
  · change Nat.card (Function.fixedPoints (f y.val.val)) = 3
    rw [hyf]
    exact hd3

end FiveTransitive.SevenNormalizerSecondDerivedLift

end CFSG
