module

public import CFSG.ThirdParty.BrauerInduction.Background.ClassFun.Character.Ring
public import CFSG.ThirdParty.BrauerInduction.Background.FDRep.Character.Induced
public import CFSG.ThirdParty.BrauerInduction.Elementary.BrauerElementary

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# Induced-character spans and ideals

This file develops a generic API for integral spans of characters induced from
subgroups satisfying a predicate `P`.

* `InducedCharacterGen P` is the set of induced-character generators;
* `InducedCharacterSpan P` is their `ℤ`-span in `ClassFun k G`;
* `InducedCharacterIdeal P` packages the same span as an ideal of
  `ClassFun.CharacterRing k G`.

The generic span is contained in the character span, is stable under
multiplication by virtual characters, and is preserved by subgroup induction
when the subgroup predicate is preserved under the relevant embeddings.

The final section specializes this construction to Brauer-elementary
subgroups, defining `BrauerSpanChar` and `BrauerIdeal`. The subsequent
linear-character reduction is developed separately in
`BrauerInduction.LinearSpan`.
-/

universe u

open BigOperators CategoryTheory

namespace CFSG.BrauerInduction

variable {k : Type u} [Field k] {G : Type u} [Group G] [Finite G]


/--
Characters induced from representations of subgroups satisfying `P`.
-/
@[expose] def InducedCharacterGen
    {k G : Type u} [Field k] [Group G] [Finite G]
    (P : Subgroup G → Prop) :
    Set (ClassFun k G) :=
  {φ |
    ∃ (H : Subgroup G) (_ : P H)
      (V : FDRep k H),
      φ = ClassFun.ind H (ClassFun.character V)}

/--
The integral span of characters induced from representations of subgroups
satisfying `P`.
-/
@[expose] def InducedCharacterSpan
    {k : Type u} [Field k]
    {G : Type u} [Group G] [Finite G]
    (P : Subgroup G → Prop) :
    Submodule ℤ (ClassFun k G) :=
  Submodule.span ℤ (InducedCharacterGen P)

namespace InducedCharacterSpan

lemma inducedCharacter_mem
    {P : Subgroup G → Prop}
    (H : Subgroup G)
    (hH : P H)
    (V : FDRep k H) :
    ClassFun.ind H (ClassFun.character V) ∈ InducedCharacterSpan P :=
  Submodule.subset_span ⟨H, hH, V, rfl⟩

lemma mono
    {P Q : Subgroup G → Prop}
    (hPQ : ∀ H, P H → Q H) :
    InducedCharacterSpan (k := k) P ≤ InducedCharacterSpan Q := by
  rw [InducedCharacterSpan, Submodule.span_le]
  rintro _ ⟨H, hH, V, rfl⟩
  exact Submodule.subset_span ⟨H, hPQ H hH, V, rfl⟩

/--
Every induced-character span is contained in the character span.
-/
lemma le_characterSpan
    (P : Subgroup G → Prop) :
    InducedCharacterSpan (k := k) P ≤ ClassFun.characterSpan k G := by
  rw [InducedCharacterSpan, Submodule.span_le]
  rintro _ ⟨H, _, V, rfl⟩
  rw [ClassFun.ind_ofChar]
  exact ClassFun.characterSpan.character_mem (FDRep.ind H V)

/--
Multiplication on the left by the character of a representation preserves an
induced-character span.
-/
lemma character_mul_mem
    (P : Subgroup G → Prop)
    (V : FDRep k G)
    {φ : ClassFun k G}
    (hφ : φ ∈ InducedCharacterSpan P) :
    ClassFun.character V * φ ∈ InducedCharacterSpan P := by
  refine Submodule.span_induction
    (p := fun θ _ =>
      ClassFun.character V * θ ∈ InducedCharacterSpan P)
    ?gen ?zero ?add ?smul hφ
  · rintro θ ⟨H, hH, W, rfl⟩
    rw [ClassFun.projection_formula
      H (ClassFun.character V) (ClassFun.character W)]
    rw [ClassFun.res_ofChar (H := H) V]
    rw [← ClassFun.char_tensor]
    exact inducedCharacter_mem
      H hH (FDRep.tensor (FDRep.res V H) W)
  · simp
  · intro x y _ _ hx hy
    rw [mul_add]
    exact Submodule.add_mem _ hx hy
  · intro n x _ hx
    have hcomm :
        ClassFun.character V * (n • x) =
          n • (ClassFun.character V * x) := by
      ext g
      simp only [ClassFun.mul_apply, ClassFun.zsmul_apply]
      rw [mul_smul_comm n]
    rw [hcomm]
    exact Submodule.smul_mem _ n hx

/--
Multiplication on the left by an element of the character span preserves an
induced-character span.
-/
lemma characterSpan_mul_mem
    (P : Subgroup G → Prop)
    {φ ψ : ClassFun k G}
    (hφ : φ ∈ ClassFun.characterSpan k G)
    (hψ : ψ ∈ InducedCharacterSpan P) :
    φ * ψ ∈ InducedCharacterSpan P := by
  change
    φ ∈ Submodule.span ℤ (ClassFun.characterSet k G)
    at hφ
  refine Submodule.span_induction
    (p := fun θ _ => θ * ψ ∈ InducedCharacterSpan P)
    ?gen ?zero ?add ?smul hφ
  · rintro _ ⟨V, rfl⟩
    exact character_mul_mem P V hψ
  · simp
  · intro x y _ _ hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  · intro n x _ hx
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ n hx

/--
An induced-character span is closed under pointwise multiplication.
-/
lemma mul_mem
    (P : Subgroup G → Prop)
    {φ ψ : ClassFun k G}
    (hφ : φ ∈ InducedCharacterSpan P)
    (hψ : ψ ∈ InducedCharacterSpan P) :
    φ * ψ ∈ InducedCharacterSpan P :=
  characterSpan_mul_mem P (le_characterSpan P hφ) hψ

/--
Induction from a subgroup maps one induced-character span into another,
provided the subgroup predicate is preserved when subgroups are mapped into
the ambient group.
-/
lemma induction_mem
    {H : Subgroup G}
    {P : Subgroup H → Prop}
    {Q : Subgroup G → Prop}
    (hmap : ∀ K : Subgroup H, P K → Q (K.map H.subtype))
    {ψ : ClassFun k H}
    (hψ : ψ ∈ InducedCharacterSpan P) :
    ClassFun.ind H ψ ∈ InducedCharacterSpan Q := by
  refine Submodule.span_induction
    (p := fun f _ =>
      ClassFun.ind H f ∈ InducedCharacterSpan Q)
    ?gen ?zero ?add ?smul hψ

  · rintro f ⟨K, hK, W, rfl⟩
    let K_G : Subgroup G := K.map H.subtype
    let eK : K ≃* K_G :=
      K.equivMapOfInjective H.subtype Subtype.coe_injective
    let W_G : FDRep k K_G := FDRep.transport eK W
    have h_transport_char :
        ClassFun.character W_G =
          (ClassFun.equivOfMulEquiv eK).symm
            (ClassFun.character W) := by
      ext x
      rfl
    rw [ClassFun.ind_trans (K := H) (H := K) (ClassFun.character W)]
    rw [← h_transport_char]
    exact inducedCharacter_mem (P := Q) K_G (hmap K hK) W_G
  · rw [ClassFun.ind_zero]
    exact Submodule.zero_mem _
  · intro x y _ _ hx hy
    rw [ClassFun.ind_add]
    exact Submodule.add_mem _ hx hy
  · intro n x _ hx
    rw [ClassFun.ind_zsmul]
    exact Submodule.smul_mem _ n hx

end InducedCharacterSpan

section InducedCharacterIdeal

/--
The ideal of the character ring generated by characters induced from
representations of subgroups satisfying `P`.
-/
@[expose] def InducedCharacterIdeal
    (P : Subgroup G → Prop) :
    Ideal (ClassFun.CharacterRing k G) where
  carrier :=
    {φ | (φ : ClassFun k G) ∈ InducedCharacterSpan P}
  zero_mem' := by
    change (0 : ClassFun k G) ∈ InducedCharacterSpan P
    exact Submodule.zero_mem _
  add_mem' := by
    intro φ ψ hφ hψ
    change
      (φ : ClassFun k G) + (ψ : ClassFun k G) ∈ InducedCharacterSpan P
    exact Submodule.add_mem _ hφ hψ
  smul_mem' := by
    intro φ ψ hψ
    change
      (φ : ClassFun k G) * (ψ : ClassFun k G) ∈ InducedCharacterSpan P
    exact InducedCharacterSpan.characterSpan_mul_mem P φ.property hψ

namespace InducedCharacterIdeal

@[simp]
lemma mem_iff
    (P : Subgroup G → Prop)
    (φ : ClassFun.CharacterRing k G) :
    φ ∈ InducedCharacterIdeal P ↔
      (φ : ClassFun k G) ∈ InducedCharacterSpan P :=
  Iff.rfl

/--
An implication between subgroup predicates induces an inclusion between the
corresponding induced-character ideals.
-/
lemma mono
    {P Q : Subgroup G → Prop}
    (hPQ : ∀ H, P H → Q H) :
    InducedCharacterIdeal P ≤ InducedCharacterIdeal (k := k) Q := by
  intro φ hφ
  exact InducedCharacterSpan.mono hPQ hφ

end InducedCharacterIdeal

end InducedCharacterIdeal

section BrauerSpanChar

/--
The `ℤ`-span of characters induced from representations of Brauer-elementary
subgroups.
-/
@[expose] def BrauerSpanChar :
    Submodule ℤ (ClassFun k G) :=
  InducedCharacterSpan (fun H => IsBrauerElementary H)

/--
The ideal of the character ring consisting of integral combinations of
characters induced from representations of Brauer-elementary subgroups.
-/
@[expose] def BrauerIdeal :
    Ideal (ClassFun.CharacterRing k G) :=
  InducedCharacterIdeal (fun H => IsBrauerElementary H)

namespace BrauerIdeal

@[simp]
lemma mem_iff
    (φ : ClassFun.CharacterRing k G) :
    φ ∈ BrauerIdeal ↔ (φ : ClassFun k G) ∈ BrauerSpanChar :=
  Iff.rfl

end BrauerIdeal

namespace BrauerSpanChar

/--
The Brauer character span is contained in the character span.
-/
lemma le_characterSpan :
    BrauerSpanChar ≤ ClassFun.characterSpan k G :=
  InducedCharacterSpan.le_characterSpan
    (fun H => IsBrauerElementary H)

/--
Multiplication on the left by an arbitrary virtual character preserves
membership in `BrauerSpanChar`.
-/
lemma characterSpan_mul_mem
    {φ ψ : ClassFun k G}
    (hφ : φ ∈ ClassFun.characterSpan k G)
    (hψ : ψ ∈ BrauerSpanChar) :
    φ * ψ ∈ BrauerSpanChar :=
  InducedCharacterSpan.characterSpan_mul_mem
    (fun H => IsBrauerElementary H) hφ hψ

/--
Multiplication on the left by the character of a representation preserves
membership in `BrauerSpanChar`.
-/
lemma character_mul_mem
    (V : FDRep k G)
    {φ : ClassFun k G}
    (hφ : φ ∈ BrauerSpanChar) :
    ClassFun.character V * φ ∈ BrauerSpanChar :=
  characterSpan_mul_mem
    (ClassFun.characterSpan.character_mem V) hφ

/--
The Brauer-character span is closed under pointwise multiplication.
-/

lemma mul_mem
    {φ ψ : ClassFun k G}
    (hφ : φ ∈ BrauerSpanChar)
    (hψ : ψ ∈ BrauerSpanChar) :
    φ * ψ ∈ BrauerSpanChar :=
  characterSpan_mul_mem (le_characterSpan hφ) hψ

/--
Induction from a subgroup preserves membership in `BrauerSpanChar`.
-/
lemma induction_mem
    {H : Subgroup G}
    {ψ : ClassFun k H}
    (hψ :
      ψ ∈ BrauerSpanChar (G := H)) :
    ClassFun.ind H ψ ∈ BrauerSpanChar := by
  apply InducedCharacterSpan.induction_mem
    (P := fun K : Subgroup H => IsBrauerElementary K)
    (Q := fun K : Subgroup G => IsBrauerElementary K)
    ?_ hψ
  intro K hK
  exact IsBrauerElementary.ofMulEquiv
    hK (K.equivMapOfInjective H.subtype Subtype.coe_injective)

/--
Every character of a Brauer-elementary group belongs to its Brauer character
span.
-/
theorem character_mem_of_isBrauerElementary
    (hG : IsBrauerElementary G)
    (V : FDRep k G) :
    ClassFun.character V ∈ BrauerSpanChar := by
  have htop : IsBrauerElementary (⊤ : Subgroup G) :=
      IsBrauerElementary.ofMulEquiv hG Subgroup.topEquiv.symm
  have hgen :
      ClassFun.ind ⊤
        (ClassFun.character (FDRep.res V ⊤)) ∈ BrauerSpanChar := by
    apply Submodule.subset_span
    exact ⟨⊤, htop, FDRep.res V (⊤ : Subgroup G), rfl⟩
  let e : FDRep.ind ⊤ (FDRep.res V ⊤) ≅ V :=
    FDRep.indTopIsoOfTop (FDRep.res V ⊤) ≪≫ FDRep.ofTop_res_top_iso V
  have hchar :
      ClassFun.ind (⊤ : Subgroup G)
          (ClassFun.character (FDRep.res V ⊤))
        =
      ClassFun.character V := by
    rw [ClassFun.ind_ofChar]
    exact ClassFun.char_eq_of_iso e
  rw [hchar] at hgen
  exact hgen

end BrauerSpanChar

end BrauerSpanChar

end CFSG.BrauerInduction
