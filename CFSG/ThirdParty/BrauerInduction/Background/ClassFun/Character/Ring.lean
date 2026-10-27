module

public import CFSG.ThirdParty.BrauerInduction.Background.ClassFun.Character.Basic

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# The character ring

This file packages virtual characters as a subring of the ring of class
functions.

* `ClassFun.characterSet k G` is the set of characters of finite-dimensional
  representations of `G`;
* `ClassFun.characterSpan k G` is their integral span;
* `ClassFun.CharacterRing k G` is the corresponding subring of
  `ClassFun k G`, with multiplication induced by tensor product;
* `ClassFun.CharacterRing.character` regards a representation character as an
  element of the character ring.

This is an image-level character ring inside `ClassFun k G`. It is deliberately
not defined as a Grothendieck group or as the full Green ring of
representations.
-/

universe u

namespace CFSG.ClassFun

section Span

variable {k G : Type u} [Field k] [Group G]

/--
Characters of finite-dimensional representations of `G`.
-/
@[expose] def characterSet
    (k : Type u) [Field k]
    (G : Type u) [Group G] :
    Set (ClassFun k G) :=
  {χ |
    ∃ V : FDRep k G,
      χ = ClassFun.character V}

/--
The integral span of characters of finite-dimensional representations.
-/
@[expose] def characterSpan
    (k : Type u) [Field k]
    (G : Type u) [Group G] :
    Submodule ℤ (ClassFun k G) :=
  Submodule.span ℤ (characterSet k G)

namespace characterSpan

lemma character_mem
    (V : FDRep k G) :
    ClassFun.character V ∈ characterSpan k G :=
  Submodule.subset_span ⟨V, rfl⟩

lemma one_mem :
    (1 : ClassFun k G) ∈ characterSpan k G := by
  rw [← ClassFun.char_trivial (k := k) (G := G)]
  exact character_mem (FDRep.trivial k G)

lemma character_mul_mem
    (V : FDRep k G)
    {f : ClassFun k G}
    (hf : f ∈ characterSpan k G) :
    ClassFun.character V * f ∈ characterSpan k G := by
  refine Submodule.span_induction
    (p := fun f _ =>
      ClassFun.character V * f ∈ characterSpan k G)
    ?gen ?zero ?add ?smul hf
  · rintro _ ⟨W, rfl⟩
    rw [← ClassFun.char_tensor]
    exact character_mem (FDRep.tensor V W)
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  · intro n x _ hx
    rw [mul_smul_comm]
    exact Submodule.smul_mem _ n hx

lemma mul_mem
    {f g : ClassFun k G}
    (hf : f ∈ characterSpan k G)
    (hg : g ∈ characterSpan k G) :
    f * g ∈ characterSpan k G := by
  refine Submodule.span_induction
    (p := fun f _ => f * g ∈ characterSpan k G)
    ?gen ?zero ?add ?smul hf
  · rintro _ ⟨V, rfl⟩
    exact character_mul_mem V hg
  · simp
  · intro x y _ _ hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  · intro n x _ hx
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ n hx

end characterSpan

/--
The character ring of `G` over `k`.

This is the subring of `ClassFun k G` consisting of integral linear
combinations of characters of finite-dimensional representations. It is an
image-level character ring, not a Grothendieck or Green ring construction.
-/
@[expose] def CharacterRing
    (k : Type u) [Field k]
    (G : Type u) [Group G] :
    Subring (ClassFun k G) where
  carrier := characterSpan k G
  zero_mem' := Submodule.zero_mem _
  one_mem' := characterSpan.one_mem
  add_mem' := fun hf hg => Submodule.add_mem _ hf hg
  mul_mem' := characterSpan.mul_mem
  neg_mem' := fun hf => Submodule.neg_mem _ hf

namespace CharacterRing

@[simp]
lemma mem_iff
    {f : ClassFun k G} :
    f ∈ CharacterRing k G ↔ f ∈ characterSpan k G :=
  Iff.rfl

/-- A representation character regarded as an element of the character ring. -/
@[expose] noncomputable def character
    (V : FDRep k G) :
    CharacterRing k G :=
  ⟨ClassFun.character V, characterSpan.character_mem V⟩

@[simp]
lemma coe_character
    (V : FDRep k G) :
    (character V : ClassFun k G) = ClassFun.character V :=
  rfl

@[simp]
lemma character_trivial :
    character (FDRep.trivial k G) = 1 := by
  apply Subtype.ext
  exact ClassFun.char_trivial k G

@[simp]
lemma character_tensor
    (V W : FDRep k G) :
    character (FDRep.tensor V W) = character V * character W := by
  apply Subtype.ext
  exact ClassFun.char_tensor V W

end CharacterRing

end Span

end CFSG.ClassFun
