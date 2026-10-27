module

public import CFSG.Quasithin.Vol2.Ch12Sec8NonabG112Def

public section

namespace CFSG.Quasithin

open CFSG.Open

namespace G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

abbrev GLV (V : Type) [AddCommGroup V] [Module (ZMod 2) V] : Type := V ≃ₗ[ZMod 2] V

@[expose] def Invariant (K : Subgroup (GLV V)) (U : Submodule (ZMod 2) V) : Prop :=
  ∀ k ∈ K, ∀ u ∈ U, k u ∈ U

@[expose] def fixedSpace (K : Subgroup (GLV V)) : Submodule (ZMod 2) V where
  carrier := {v | ∀ k ∈ K, k v = v}
  add_mem' := fun {a b} ha hb k hk => by rw [map_add, ha k hk, hb k hk]
  zero_mem' := fun k _ => map_zero k
  smul_mem' := fun c v hv k hk => by rw [map_smul, hv k hk]

@[expose] def commSpace (K : Subgroup (GLV V)) (U : Submodule (ZMod 2) V) :
    Submodule (ZMod 2) V :=
  Submodule.span (ZMod 2) {w | ∃ k ∈ K, ∃ u ∈ U, w = k u - u}

@[expose] def conjSub (g : GLV V) (U : Submodule (ZMod 2) V) : Submodule (ZMod 2) V :=
  U.map (g : V →ₗ[ZMod 2] V)

@[expose] def centralizerOn (K : Subgroup (GLV V)) (U : Submodule (ZMod 2) V) :
    Subgroup (GLV V) where
  carrier := {k | k ∈ K ∧ ∀ u ∈ U, k u = u}
  mul_mem' := fun {a b} ha hb => ⟨K.mul_mem ha.1 hb.1, fun u hu => by
    show a (b u) = u
    rw [hb.2 u hu, ha.2 u hu]⟩
  one_mem' := ⟨K.one_mem, fun u _ => rfl⟩
  inv_mem' := fun {a} ha => ⟨K.inv_mem ha.1, fun u hu => by
    show a.symm u = u
    rw [LinearEquiv.symm_apply_eq]
    exact (ha.2 u hu).symm⟩

@[expose] def stabilizerOf (K : Subgroup (GLV V)) (U : Submodule (ZMod 2) V) :
    Subgroup (GLV V) where
  carrier := {k | k ∈ K ∧ conjSub k U = U}
  mul_mem' := fun {a b} ha hb => ⟨K.mul_mem ha.1 hb.1, by
    have h1 : Submodule.map (b : V →ₗ[ZMod 2] V) U = U := hb.2
    have h2 : Submodule.map (a : V →ₗ[ZMod 2] V) U = U := ha.2
    show Submodule.map ((a * b : GLV V) : V →ₗ[ZMod 2] V) U = U
    calc Submodule.map ((a * b : GLV V) : V →ₗ[ZMod 2] V) U
        = Submodule.map (a : V →ₗ[ZMod 2] V) (Submodule.map (b : V →ₗ[ZMod 2] V) U) := by
          rw [← Submodule.map_comp]
          rfl
      _ = U := by rw [h1, h2]⟩
  one_mem' := ⟨K.one_mem, by
    show Submodule.map ((1 : GLV V) : V →ₗ[ZMod 2] V) U = U
    exact Submodule.map_id U⟩
  inv_mem' := fun {a} ha => ⟨K.inv_mem ha.1, by
    have h2 : Submodule.map (a : V →ₗ[ZMod 2] V) U = U := ha.2
    have hid : ((a⁻¹ : GLV V) : V →ₗ[ZMod 2] V) ∘ₗ (a : V →ₗ[ZMod 2] V) = LinearMap.id := by
      ext v
      simp
    show Submodule.map ((a⁻¹ : GLV V) : V →ₗ[ZMod 2] V) U = U
    calc Submodule.map ((a⁻¹ : GLV V) : V →ₗ[ZMod 2] V) U
        = Submodule.map ((a⁻¹ : GLV V) : V →ₗ[ZMod 2] V)
            (Submodule.map (a : V →ₗ[ZMod 2] V) U) := by rw [h2]
      _ = Submodule.map (((a⁻¹ : GLV V) : V →ₗ[ZMod 2] V) ∘ₗ (a : V →ₗ[ZMod 2] V)) U := by
          rw [← Submodule.map_comp]
      _ = U := by rw [hid, Submodule.map_id]⟩

@[expose] def IrrSec (K : Subgroup (GLV V)) (C L : Submodule (ZMod 2) V) : Prop :=
  C < L ∧ ∀ J : Submodule (ZMod 2) V, Invariant K J → C ≤ J → J ≤ L → J = C ∨ J = L

@[expose] def IsIrr (K : Subgroup (GLV V)) (U : Submodule (ZMod 2) V) : Prop :=
  Invariant K U ∧ IrrSec K ⊥ U

@[expose] def IrrPlus (K : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : Prop :=
  Invariant K I ∧ commSpace K I = I ∧ IrrSec K (fixedSpace K ⊓ I) I

@[expose] def HIso (K : Subgroup (GLV V)) (I J : Submodule (ZMod 2) V) : Prop :=
  ∃ φ : I ≃ₗ[ZMod 2] J, ∀ k ∈ K, ∀ i j : I, k (i : V) = (j : V) →
    k ((φ i : J) : V) = ((φ j : J) : V)

@[expose] def Homogeneous (K : Subgroup (GLV V)) : Prop :=
  ∀ I J : Submodule (ZMod 2) V, IrrPlus K I → IrrPlus K J → HIso K I J

@[expose] def FaithfulOn (K : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : Prop :=
  centralizerOn K I = ⊥

@[expose] def SelfDual (K : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : Prop :=
  ∃ f : LinearMap.BilinForm (ZMod 2) I, f.Nondegenerate ∧
    ∀ k ∈ K, ∀ i j i' j' : I, k (i : V) = (i' : V) → k (j : V) = (j' : V) → f i' j' = f i j

@[expose] def AutAll (K : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : Prop :=
  ∀ g : I ≃ₗ[ZMod 2] I, ∃ k ∈ K, ∀ i : I, k (i : V) = ((g i : I) : V)

@[expose] def Isotropic (B : LinearMap.BilinForm (ZMod 2) V) (U : Submodule (ZMod 2) V) : Prop :=
  ∀ u ∈ U, ∀ u' ∈ U, B u u' = 0

@[expose] def NondegOn (B : LinearMap.BilinForm (ZMod 2) V) (U : Submodule (ZMod 2) V) : Prop :=
  ∀ u ∈ U, (∀ w ∈ U, B u w = 0) → u = 0

@[expose] def perp (B : LinearMap.BilinForm (ZMod 2) V) (v : V) : Submodule (ZMod 2) V :=
  LinearMap.ker (B v)

@[expose] def InducesTransvection (x : GLV V) (U : Submodule (ZMod 2) V) (c : V) : Prop :=
  (∀ u ∈ U, x u - u ∈ Submodule.span (ZMod 2) {c}) ∧ ∃ u ∈ U, x u ≠ u

@[expose] def FullTransvections (Y : Subgroup (GLV V)) (U : Submodule (ZMod 2) V) (c : V)
    (hc : c ∈ U) : Prop :=
  (∀ y ∈ Y, ∃ f : U →ₗ[ZMod 2] ZMod 2, f ⟨c, hc⟩ = 0 ∧ ∀ u : U, y (u : V) = (u : V) + f u • c) ∧
    ∀ f : U →ₗ[ZMod 2] ZMod 2, f ⟨c, hc⟩ = 0 →
      ∃ y ∈ Y, ∀ u : U, y (u : V) = (u : V) + f u • c

@[expose] def normalClosure (Γ L : Subgroup (GLV V)) : Subgroup (GLV V) :=
  Subgroup.closure {x | ∃ γ ∈ Γ, ∃ l ∈ L, x = γ * l * γ⁻¹}

@[expose] noncomputable def numConjugates (Γ L : Subgroup (GLV V)) : ℕ :=
  Set.ncard {M : Subgroup (GLV V) | ∃ γ ∈ Γ, M = L.map (MulAut.conj γ).toMonoidHom}

@[expose] def IsA5Module (L : Subgroup (GLV V)) (I : Submodule (ZMod 2) V) : Prop :=
  ∃ (φ : ↥L ≃* ↥(alternatingGroup (Fin 5))) (ψ : ↥I ≃ₗ[ZMod 2] ↥(permCore 5)),
    ∀ (γ : ↥L) (v w : ↥I), (w : V) = (γ : GLV V) (v : V) →
      (ψ w : Fin 5 → ZMod 2) =
        permAct ((φ γ : ↥(alternatingGroup (Fin 5))) : Equiv.Perm (Fin 5)) (ψ v)

end G11

end CFSG.Quasithin
