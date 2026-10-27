module

public import Mathlib.GroupTheory.Sylow
public import CFSG.Permutation.FiveTransitive.AmbientConjugateFixedSet
public import Mathlib.GroupTheory.GroupAction.Embedding

public section

namespace CFSG

namespace FiveTransitive.FixedNormalizerAction

open MulAction

@[expose] abbrev Normalizer {G:Type*} [Group G] (Q:Subgroup G) := Subgroup.normalizer (Q:Set G)
@[expose] abbrev Inside {G:Type*} [Group G] (Q:Subgroup G) := Q.subgroupOf (Normalizer Q)
@[expose] abbrev Fixed {G X:Type*} [Group G] [MulAction G X] (Q:Subgroup G) := fixedPoints (Inside Q) X
@[expose] abbrev Image {G X:Type*} [Group G] [MulAction G X] (Q:Subgroup G) :=
  (toPermHom (Normalizer Q) (Fixed (X:=X) Q)).range

theorem fixed_eq {G X:Type*} [Group G] [MulAction G X] (Q:Subgroup G) :
    (Fixed (X:=X) Q : Set X)=fixedPoints Q X :=
  AmbientConjugateFixedSet.fixedPoints_subgroupOf Q (Normalizer Q) Q.le_normalizer

@[expose] def ambientEmbedding {G X:Type*} [Group G] [MulAction G X] {Q:Subgroup G}
    {k:ℕ} (b:Fin k ↪ Fixed (X:=X) Q) : Fin k ↪ X :=
  b.trans (Function.Embedding.subtype _)

private def localFixerEquiv {G X:Type*} [Group G] [MulAction G X] (Q:Subgroup G)
    {k:ℕ} (b:Fin k ↪ Fixed (X:=X) Q) :
    stabilizer (Normalizer Q) b ≃* ↥(Normalizer Q ⊓ stabilizer G (ambientEmbedding b)) where
  toFun r := ⟨r.val.val,⟨r.val.property,by
    apply Function.Embedding.ext
    intro i
    have h := DFunLike.congr_fun r.property i
    exact congrArg Subtype.val h⟩⟩
  invFun r := ⟨⟨r.val,r.property.1⟩,by
    apply Function.Embedding.ext
    intro i
    apply Subtype.ext
    exact DFunLike.congr_fun r.property.2 i⟩
  left_inv _ := rfl
  right_inv _ := rfl
  map_mul' _ _ := rfl

theorem sylow_localFixer_image
    {G X:Type*} [Group G] [Finite G] [MulAction G X] {p:ℕ} [Fact p.Prime]
    (Q:Subgroup G) {k:ℕ} (b:Fin k ↪ Fixed (X:=X) Q)
    (R:Sylow p (stabilizer (Normalizer Q) b)) :
    ∃ S:Sylow p ↥(Normalizer Q ⊓ stabilizer G (ambientEmbedding b)),
      (S:Subgroup ↥(Normalizer Q ⊓ stabilizer G (ambientEmbedding b))).map
        (Normalizer Q ⊓ stabilizer G (ambientEmbedding b)).subtype =
      ((R:Subgroup (stabilizer (Normalizer Q) b)).map (stabilizer (Normalizer Q) b).subtype).map
        (Normalizer Q).subtype := by
  let E := localFixerEquiv Q b
  let S := Sylow.mapSurjective (f:=E.toMonoidHom) E.surjective R
  refine ⟨S,?_⟩
  change ((R:Subgroup (stabilizer (Normalizer Q) b)).map E.toMonoidHom).map
      (Normalizer Q ⊓ stabilizer G (ambientEmbedding b)).subtype = _
  rw [Subgroup.map_map,Subgroup.map_map]
  congr 1

end FiveTransitive.FixedNormalizerAction

end CFSG
