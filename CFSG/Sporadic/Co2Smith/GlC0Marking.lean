module

public import CFSG.Sporadic.Co2Smith.GlC0Fix

public section

namespace CFSG.Sporadic.Co2Smith

open Subgroup

attribute [local irreducible] Matrix.instHMulOfFintypeOfMulOfAddCommMonoid

section Norm

variable
  {G : Type*} [Group G] {z : G}

@[expose] def zH (z : G) : centralizer ({z} : Set G) := ⟨z, mem_centralizer_singleton_iff.2 rfl⟩

@[expose] noncomputable def z0C0 : C0c := ⟨z0, x16K_eq ▸ x16K_mem_C0c⟩

end Norm

section Main

variable
  {G : Type*} [Group G] {z : G}

@[expose] def FixFusion (φ : centralizer ({z} : Set G) ≃* Cz) : Prop :=
  ∀ d d' : Cz, d * d = 1 → d ≠ 1 → d' * d' = 1 → d' ≠ 1 →
    IsConj (φ.symm d : G) (φ.symm d' : G) → fixK (d : K) = fixK (d' : K)

end Main

end CFSG.Sporadic.Co2Smith
