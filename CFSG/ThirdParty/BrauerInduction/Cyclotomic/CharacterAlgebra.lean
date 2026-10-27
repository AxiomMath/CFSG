module

public import CFSG.ThirdParty.BrauerInduction.Cyclotomic.CharacterSystem

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG

/-!
# The cyclotomic character algebra

This file packages the global cyclotomic character span `R_Lambda.top k G` as
a subalgebra of the ring of class functions over the cyclotomic coefficient
ring `Lambda k G`.
-/

universe u

namespace CFSG.ClassFun

variable {k : Type u} [Field k]
variable {G : Type u} [Group G] [Finite G]

namespace R_Lambda

/--
Characters of finite-dimensional representations belong to the global
cyclotomic character span.
-/
lemma top_char_mem
    (V : FDRep k G) :
    ClassFun.character V ∈ R_Lambda.top k G :=
  Submodule.subset_span ⟨V, rfl⟩

/--
The constant character `1` belongs to the global cyclotomic character span.
-/
lemma top_one_mem :
    (1 : ClassFun k G) ∈ R_Lambda.top k G := by
  rw [← ClassFun.char_trivial k G]
  exact top_char_mem (FDRep.trivial k G)

/--
The global cyclotomic character span is closed under pointwise
multiplication.
-/
lemma top_mul_mem
    {f g : ClassFun k G}
    (hf : f ∈ R_Lambda.top k G)
    (hg : g ∈ R_Lambda.top k G) :
    f * g ∈ R_Lambda.top k G := by
  refine Submodule.span_induction
    (p := fun f _ => f * g ∈ R_Lambda.top k G)
    ?gen_f ?zero_f ?add_f ?smul_f hf
  · rintro _ ⟨V, rfl⟩
    refine Submodule.span_induction
      (p := fun g _ =>
        ClassFun.character V * g ∈ R_Lambda.top k G)
      ?gen_g ?zero_g ?add_g ?smul_g hg
    · rintro _ ⟨W, rfl⟩
      rw [← ClassFun.char_tensor]
      exact top_char_mem (FDRep.tensor V W)
    · simp
    · intro x y _ _ hx hy
      rw [mul_add]
      exact Submodule.add_mem _ hx hy
    · intro a x _ hx
      rw [mul_smul_comm]
      exact Submodule.smul_mem _ a hx
  · simp
  · intro x y _ _ hx hy
    rw [add_mul]
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ a hx

/--
Induction from a subgroup sends `R_Λ(H)` into the global cyclotomic character
algebra.
-/
lemma ind_mem_top
    (H : Subgroup G)
    {q : ClassFun k H}
    (hq : q ∈ R_Lambda k G H) :
    ClassFun.ind H q ∈ R_Lambda.top k G := by
  refine Submodule.span_induction
    (p := fun q _ => ClassFun.ind H q ∈ R_Lambda.top k G)
    ?gen ?zero ?add ?smul hq
  · rintro _ ⟨V, rfl⟩
    rw [← ClassFun.char_ind]
    exact top_char_mem (FDRep.ind H V)
  · simp
  · intro x y _ _ hx hy
    rw [ClassFun.ind_add]
    exact Submodule.add_mem _ hx hy
  · intro a x _ hx
    change
      ClassFun.ind H (((a : Lambda k G) : k) • x) ∈
        R_Lambda.top k G
    rw [ClassFun.ind_smul]
    exact Submodule.smul_mem _ a hx

end R_Lambda

/--
The cyclotomic character algebra of `G` over `k`.

Its underlying `Lambda k G`-submodule is the global cyclotomic character span
`R_Lambda.top k G`.
-/
@[expose] def CyclotomicCharacterAlgebra :
    Subalgebra (Lambda k G) (ClassFun k G) :=
  (R_Lambda.top k G).toSubalgebra
    R_Lambda.top_one_mem
    (fun _ _ hf hg => R_Lambda.top_mul_mem hf hg)

namespace CyclotomicCharacterAlgebra

@[simp]
lemma mem_iff
    {f : ClassFun k G} :
    f ∈ CyclotomicCharacterAlgebra (k := k) (G := G) ↔
      f ∈ R_Lambda.top k G :=
  Iff.rfl

/--
A representation character regarded as an element of the cyclotomic character
algebra.
-/
@[expose] noncomputable def character
    (V : FDRep k G) :
    CyclotomicCharacterAlgebra (k := k) (G := G) :=
  ⟨ClassFun.character V, R_Lambda.top_char_mem V⟩

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

end CyclotomicCharacterAlgebra

end CFSG.ClassFun
