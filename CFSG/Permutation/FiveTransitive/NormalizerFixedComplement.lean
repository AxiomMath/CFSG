module

public import CFSG.Permutation.FiveTransitive.FreeComplementOrbitCount
public import CFSG.Permutation.FiveTransitive.FixedSetNormalizerPerm

public section

namespace CFSG

namespace FiveTransitive.NormalizerFixedComplement

open MulAction

@[expose] abbrev Normalizer {G : Type*} [Group G] (Q : Subgroup G) :=
  Subgroup.normalizer (Q : Set G)

@[expose] abbrev Inside {G : Type*} [Group G] (Q : Subgroup G) := Q.subgroupOf (Normalizer Q)

@[expose] def Domain {G X : Type*} [Group G] [MulAction G X] (Q : Subgroup G) :
    SubMulAction (Normalizer Q) X :=
  FreeComplementOrbitCount.complement (Normalizer Q) (fixedPoints Q X) (by
    intro n x hx
    exact FixedSetNormalizerPerm.smul_mem_fixedPoints G X Q n n.property hx)

theorem card_domain {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G) : Nat.card (Domain (X := X) Q) =
      Nat.card X - (fixedPoints Q X).ncard :=
  FreeComplementOrbitCount.card_complement (Normalizer Q) (fixedPoints Q X) _

theorem free_inside {G X : Type*} [Group G] [MulAction G X]
    (Q : Subgroup G)
    (hfree : ∀ (q : Q) (x : X), x ∉ fixedPoints Q X → q • x = x → q = 1) :
    ∀ (q : Inside Q) (x : Domain (X := X) Q), q • x = x → q = 1 := by
  intro q x hqx
  let qQ : Q := ⟨q.val.val, q.property⟩
  have h : qQ • x.val = x.val := congrArg Subtype.val hqx
  have he := hfree qQ x.val x.property h
  apply Subtype.ext
  apply Subtype.ext
  exact congrArg (fun q : Q => (q : G)) he

theorem fixed_card {G X : Type*} [Group G] [Finite X] [MulAction G X]
    (Q : Subgroup G) (n : Normalizer Q) :
    Nat.card (fixedBy (Domain (X := X) Q) n) =
      (fixedBy X (n : G) \ fixedPoints Q X).ncard := by
  let e : fixedBy (Domain (X := X) Q) n ≃
      ↥(fixedBy X (n : G) \ fixedPoints Q X) :=
    { toFun := fun x => ⟨x.val.val, congrArg Subtype.val x.property, x.val.property⟩
      invFun := fun x => ⟨⟨x.val, x.property.2⟩, Subtype.ext x.property.1⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  rw [Nat.card_congr e, Nat.card_coe_set_eq]

end FiveTransitive.NormalizerFixedComplement

end CFSG
