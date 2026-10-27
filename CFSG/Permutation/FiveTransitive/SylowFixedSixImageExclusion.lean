module

public import CFSG.Permutation.FiveTransitive.GenericSylowFixedAction
public import CFSG.Permutation.FiveTransitive.OyamaFixedSixExclusion

public section

namespace CFSG

namespace FiveTransitive.SylowFixedSixImageExclusion

open MulAction GenericSylowFixedAction FixedSetNormalizerPerm OyamaMinimalOrbitDescent

theorem internal_fixed_eq
    (G X : Type) [Group G] [MulAction G X] (s : Set X)
    (S : Sylow 2 (fixingSubgroup G s)) :
    sylowFixedPoints G X s S = fixedPoints (sylowImage G X s S) X := by
  ext x
  constructor
  · intro hx p
    exact hx ⟨⟨p.val, (sylowImage G X s S).le_normalizer p.property⟩, p.property⟩
  · intro hx p
    exact hx ⟨p.val.val, p.property⟩

private theorem evenFixed_of_internal_card
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X]
    (s : Set X) (S : Sylow 2 (fixingSubgroup G s))
    (hfix : Nat.card (sylowFixedPoints G X s S) = 6)
    (himage : Nat.card (MulAction.toPermHom (sylowNormalizer G X s S)
      (sylowFixedPoints G X s S)).range = 360) :
    EvenSixTupleLocal.EvenFixed G X (sylowImage G X s S) := by
  classical
  let F := sylowFixedPoints G X s S
  let A := sylowNormalizer G X s S
  let Q := sylowImage G X s S
  let L := (MulAction.toPermHom A F).range
  let _ : Fintype F := Fintype.ofFinite F
  let _ : DecidableEq F := Classical.decEq F
  have hpermcard : Nat.card (Equiv.Perm F) = 720 := by
    rw [Nat.card_perm, hfix]
    norm_num
  have hL : L = alternatingGroup F := by
    apply Equiv.Perm.eq_alternatingGroup_of_index_eq_two
    have hi := L.index_mul_card
    change Nat.card L = 360 at himage
    rw [himage, hpermcard] at hi
    omega
  let _ : Fintype (fixedPoints Q X) := Fintype.ofFinite _
  let _ : DecidableEq (fixedPoints Q X) := Classical.decEq _
  let e : fixedPoints Q X ≃ F := (Set.equivOfEq (internal_fixed_eq G X s S)).symm
  intro n hn
  have hp : e.permCongr (fixedPerm G X Q n hn) =
      MulAction.toPermHom A F ⟨n, hn⟩ := by
    apply Equiv.ext
    intro x
    apply Subtype.ext
    rfl
  have hm : MulAction.toPermHom A F ⟨n, hn⟩ ∈ alternatingGroup F := by
    rw [← hL]
    exact ⟨⟨n, hn⟩, rfl⟩
  rw [← Equiv.Perm.sign_permCongr e, hp]
  exact Equiv.Perm.mem_alternatingGroup.mp hm

theorem not_even_fixed_six_set
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s)) (hS : (S : Subgroup (fixingSubgroup G s)) ≠ ⊥)
    (hfix : Nat.card (fixedPoints (sylowImage G X s S) X) = 6)
    (heven : EvenSixTupleLocal.EvenFixed G X (sylowImage G X s S)) : False := by
  classical
  have hcard : Nat.card s = 4 := by rwa [Nat.card_coe_set_eq]
  let E : s ≃ Fin 4 := Finite.equivFinOfCardEq hcard
  let a : Fin 4 ↪ X := E.symm.toEmbedding.trans (Function.Embedding.subtype _)
  have hra : Set.range a = s := by
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact (E.symm i).property
    · intro hx
      exact ⟨E ⟨x, hx⟩, congrArg Subtype.val (E.symm_apply_apply ⟨x, hx⟩)⟩
  have hK : fixingSubgroup G s = stabilizer G a := by
    rw [← hra, EvenSixTupleLocal.fixing_range]
  have he (H : Subgroup G) (hH : H = stabilizer G a)
      (T : Sylow 2 H) (hT : (T : Subgroup H) ≠ ⊥)
      (hc : Nat.card (fixedPoints ((T : Subgroup H).map H.subtype) X) = 6)
      (hv : EvenSixTupleLocal.EvenFixed G X ((T : Subgroup H).map H.subtype)) :
      False := by
    subst H
    exact OyamaFixedSixExclusion.not_even_fixed_six h4 a T hT hc hv
  exact he (fixingSubgroup G s) hK S hS hfix heven

theorem not_six_of_internal_card
    (G X : Type) [Group G] [Finite G] [Fintype X] [MulAction G X] [FaithfulSMul G X]
    (h4 : IsMultiplyPretransitive G X 4) (s : Set X) (hs : s.ncard = 4)
    (S : Sylow 2 (fixingSubgroup G s)) (hS : (S : Subgroup (fixingSubgroup G s)) ≠ ⊥)
    (hfix : Nat.card (sylowFixedPoints G X s S) = 6)
    (himage : Nat.card (MulAction.toPermHom (sylowNormalizer G X s S)
      (sylowFixedPoints G X s S)).range = 360) : False := by
  apply not_even_fixed_six_set G X h4 s hs S hS
  · rwa [← internal_fixed_eq G X s S]
  · exact evenFixed_of_internal_card G X s S hfix himage

end FiveTransitive.SylowFixedSixImageExclusion

end CFSG
