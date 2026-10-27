module

public import CFSG.ThirdParty.BrauerInduction.Bernstein.PElementaryConstruction
public import CFSG.ThirdParty.BrauerInduction.Cyclotomic.IntegralCharacterRing

public section

set_option autoImplicit true
set_option maxSynthPendingDepth 3

namespace CFSG
end CFSG
open CFSG


/-!
# Bernstein's prime-local ideal

This file defines the prime-local Bernstein span used in Steps 3--5 of the
proof.

For a fixed prime `p`, the basic generators are induced class functions

`Ind_E^G q`

where `E ≤ G` is `p`-elementary and `q ∈ Q(E)`.  We package these generators
as `JGen` and define their integral span `J p`.

The file also proves the structural properties needed later:

* generators restrict to global elements of the character system `Q`;
* `J p` absorbs multiplication by global `Q`-functions;
-/

universe u

namespace CFSG.BrauerInduction.Bernstein

variable {k G : Type u} [Field k] [Group G] [Finite G]

section IntegralIdeal

variable (p : ℕ)

/-!
## The integral span `J_p`

This section defines the common generator set `JGen` and the integral span
`J p`.  It proves the elementary closure lemmas for `J`, the projection-formula
ideal property `mul_mem_J`, and the Step 8 membership result `f_a_mem_J`.
-/

/-- The common generator set for both `J_p` and `Jloc_p`. -/
@[expose] def JGen : Set (ClassFun k G) :=
  { f : ClassFun k G |
      ∃ (E : Subgroup G) (_ : IsPElementary p E)
        (q : ClassFun k E),
        q ∈ ClassFun.Q_sys k G E ∧
        f = ClassFun.ind (k := k) E q }

/-- Bernstein's integral prime-local span `J_p`. -/
@[expose] def J : Submodule ℤ (ClassFun k G) := Submodule.span ℤ (JGen p)

/-- A generator of `J_p`: induction from a `p`-elementary subgroup. -/
lemma ind_mem_J
    (E : Subgroup G) (hE : IsPElementary p E)
    {q : ClassFun k E}
    (hq : q ∈ ClassFun.Q_sys k G E) :
    ClassFun.ind (k := k) E q ∈ J p := by
  exact Submodule.subset_span ⟨E, hE, q, hq, rfl⟩

/-- The zero function belongs to `J_p`. -/
lemma zero_mem_J :
    (0 : ClassFun k G) ∈ J p :=
  Submodule.zero_mem _

/-- `J_p` is closed under addition. -/
lemma add_mem_J
    {f g : ClassFun k G} (hf : f ∈ J p) (hg : g ∈ J p) :
    f + g ∈ J p :=
  Submodule.add_mem _ hf hg

/-- `J_p` is closed under integral scalar multiplication. -/
lemma zsmul_mem_J
    (n : ℤ) {f : ClassFun k G} (hf : f ∈ J p) :
    n • f ∈ J p :=
  Submodule.smul_mem _ n hf

/--
A generator restricts to a global element of the character system `Q`.
-/
lemma JGen_mem_Q_sys
    {y : ClassFun k G}
    (hy : y ∈ JGen p) :
    ClassFun.res (⊤ : Subgroup G) y
      ∈ ClassFun.Q_sys k G (⊤ : Subgroup G) := by
  rcases hy with ⟨E, hE, q, hq_Q, rfl⟩
  exact ClassFun.Q_sys.ind_mem (H := E) hq_Q

/-- The integral span `J_p` absorbs multiplication by global `Q`-functions. -/
lemma mul_mem_J [Fact p.Prime]
    (f g : ClassFun k G)
    (hf : f ∈ J p)
    (hg : ClassFun.res (⊤ : Subgroup G) g ∈ ClassFun.Q_sys (k := k) (G := G) ⊤) :
    f * g ∈ J p := by
  refine Submodule.span_induction (p := fun f _ => f * g ∈ J p) ?_ ?_ ?_ ?_ hf
  · rintro _ ⟨E, hE, q, ⟨hq_Lambda, hq_Z⟩, rfl⟩
    obtain ⟨hg_Lambda, hg_Z⟩ := hg
    rw [mul_comm, ClassFun.projection_formula]
    apply Submodule.subset_span (R := ℤ)
    use E, hE, (ClassFun.res E g * q)
    constructor
    · constructor
      · apply ClassFun.R_Lambda.mul_mem
        · exact ClassFun.R_Lambda.res_top_to_subgroup hg_Lambda
        · exact hq_Lambda
      · apply ClassFun.C_Z.mul_mem
        · apply ClassFun.C_Z.res
          intro x
          exact hg_Z ⟨x, Subgroup.mem_top x⟩
        · exact hq_Z
    · rfl
  · simp only [zero_mul, zero_mem]
  · intro x y _ _ hx_mem hy_mem
    rw [add_mul]
    exact Submodule.add_mem _ hx_mem hy_mem
  · intro n x _ hx_mem
    rw [smul_mul_assoc]
    exact Submodule.smul_mem _ n hx_mem

section IdealPackaging

variable [Fact p.Prime]

/--
Bernstein's fixed-prime ideal in the ring of integer-valued cyclotomic
characters.

Its underlying membership condition is membership in the integral span `J p`.
-/
@[expose] def JIdeal :
    Ideal (ClassFun.IntegralCyclotomicCharacterRing (k := k) (G := G)) where
  carrier :=
    {f | (f : ClassFun k G) ∈ J p}
  zero_mem' := by
    change (0 : ClassFun k G) ∈ J p
    exact Submodule.zero_mem _
  add_mem' := by
    intro f g hf hg
    change
      (f : ClassFun k G) + (g : ClassFun k G) ∈ J p
    exact Submodule.add_mem _ hf hg
  smul_mem' := by
    intro q f hf
    change
      (q : ClassFun k G) * (f : ClassFun k G) ∈ J p
    simpa only [mul_comm] using
      mul_mem_J p
        (f : ClassFun k G)
        (q : ClassFun k G)
        hf
        (ClassFun.IntegralCyclotomicCharacterRing.res_top_mem_Q_sys q)

namespace JIdeal

@[simp]
lemma mem_iff
    (f : ClassFun.IntegralCyclotomicCharacterRing (k := k) (G := G)) :
    f ∈ JIdeal p ↔ (f : ClassFun k G) ∈ J p :=
  Iff.rfl

/--
Induction of a `Q(E)`-function from a `p`-elementary subgroup gives an element
of Bernstein's fixed-prime ideal.
-/
lemma ind_mem
    (E : Subgroup G)
    (hE : IsPElementary p E)
    {q : ClassFun k E}
    (hq : q ∈ ClassFun.Q_sys k G E) :
    ClassFun.IntegralCyclotomicCharacterRing.ind E hq ∈ JIdeal p :=
      ind_mem_J p E hE hq

end JIdeal
end IdealPackaging

open BrauerInduction.PElementary in
/-- Bernstein Step 8: the induced function `f_a` belongs to `J_p`. -/
lemma f_a_mem_J
    [Fact p.Prime] [CharZero k] [IsAlgClosed k]
    (a : G) (ha : IsPRegular p a) :
    f (k := k) p a ∈ J p :=
      ind_mem_J p
        (E_subgroup p a) (E_isPElementary p ha) (phi_mem_Q p a ha)

end IntegralIdeal


end CFSG.BrauerInduction.Bernstein
