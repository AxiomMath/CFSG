module

public import CFSG.LocalAnalysis.WeakClosure81.NineDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open CFSG.CGT.Timmesfeld75 Subgroup
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def nineDelta (V S : Subgroup G) : Set (Subgroup G) :=
  {B | IsGConj V B ∧ B ≤ S}

@[expose] def nineW (V S : Subgroup G) : Subgroup G :=
  ⨆ B ∈ nineDelta V S, B

@[expose] def nineDeltaStab (V S : Subgroup G) : Subgroup G where
  carrier := {g | ∀ B : Subgroup G, B ∈ nineDelta V S ↔ conjSubgroup B g ∈ nineDelta V S}
  one_mem' := by
    intro B
    rw [conjSubgroup_one]
  mul_mem' := by
    intro a b ha hb B
    rw [ha B, hb (conjSubgroup B a), conjSubgroup_conjSubgroup]
  inv_mem' := by
    intro a ha B
    have h := ha (conjSubgroup B a⁻¹)
    rw [conjSubgroup_conjSubgroup, inv_mul_cancel, conjSubgroup_one] at h
    exact h.symm

theorem mem_nineDeltaStab {V S : Subgroup G} {g : G} :
    g ∈ nineDeltaStab V S ↔
      ∀ B : Subgroup G, B ∈ nineDelta V S ↔ conjSubgroup B g ∈ nineDelta V S :=
  Iff.rfl

structure Nine3Core (V T A K S X : Subgroup G) (p : ℕ) : Prop where
  h9 : Hyp9 V T
  conj : IsGConj V A
  leT : A ≤ T
  syl : IsSylowIn 2 (T ⊓ centralizer (A : Set G))
    (normalizer (V : Set G) ⊓ centralizer (A : Set G))
  ne : A ≠ V
  leS : S ≤ T
  tau : E1.tauOf (normalizer (V : Set G)) T A ≤ S
  hyp : Nine2Hyp V K S X p
  card : Nat.card X = p

namespace Nine3Core

variable {V T A K S X : Subgroup G} {p : ℕ}

theorem hyp7 (h : Nine3Core V T A K S X p) : Hyp7 V := h.h9.hyp7

theorem rk_gt (h : Nine3Core V T A K S X p) : 2 < rk ↥V := h.h9.rk_gt

end Nine3Core

end CFSG.LocalAnalysis.WeakClosure81
