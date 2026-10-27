module

public import CFSG.Open.LocalVocabulary

public section

namespace CFSG.SignalizerFunctorTheorem.Quadratic

@[expose] def IsElemAb (p : ℕ) {G : Type*} [Group G] (E : Subgroup G) : Prop :=
  CFSG.Open.IsElemAbelian p E

@[expose] def IsSyl (p : ℕ) {G : Type*} [Group G] (T U : Subgroup G) : Prop :=
  ∃ P : Sylow p U, (P : Subgroup U).map U.subtype = T

abbrev LGL (p : ℕ) (V : Type*) [AddCommGroup V] [Module (ZMod p) V] := V ≃ₗ[ZMod p] V

instance {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V] [Finite V] :
    Finite (LGL p V) :=
  Finite.of_injective (fun f : LGL p V => (f : V → V)) fun _ _ h => LinearEquiv.ext (congrFun h)

variable {p : ℕ} {V : Type*} [AddCommGroup V] [Module (ZMod p) V]

@[expose] def fixSub (A : Subgroup (LGL p V)) : Submodule (ZMod p) V where
  carrier := {v | ∀ a ∈ A, a v = v}
  add_mem' := fun {x y} hx hy a ha => by rw [map_add, hx a ha, hy a ha]
  zero_mem' := fun a _ => map_zero a
  smul_mem' := fun c x hx a ha => by rw [map_smul, hx a ha]

@[expose] def commSub (A : Subgroup (LGL p V)) : Submodule (ZMod p) V :=
  Submodule.span (ZMod p) {w | ∃ a ∈ A, ∃ v : V, w = a v - v}

@[expose] def QOne (A : Subgroup (LGL p V)) : Prop :=
  ∀ B : Subgroup (LGL p V), B ≤ A →
    Nat.card B * Nat.card (fixSub B) ≤ Nat.card A * Nat.card (fixSub A)

@[expose] def IsAV (H A : Subgroup (LGL p V)) : Prop :=
  A ≤ H ∧ IsElemAb p A ∧ QOne A

@[expose] def IsAVMin (H A : Subgroup (LGL p V)) : Prop :=
  IsAV H A ∧ commSub A ≠ ⊥ ∧
    ∀ B : Subgroup (LGL p V), IsAV H B → commSub B ≠ ⊥ → B ≤ A → B = A

@[expose] def blk (H A : Subgroup (LGL p V)) : Subgroup (LGL p V) :=
  ⨆ h ∈ H, A.map (MulAut.conj h).toMonoidHom

@[expose] def cj (g : LGL p V) (A : Subgroup (LGL p V)) : Subgroup (LGL p V) :=
  A.map (MulAut.conj g).toMonoidHom

structure IsBlock (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (E : Subgroup (LGL p V)) : Prop where
  card_comm : Nat.card (commSub E) = p ^ 2
  faithful : ∀ g ∈ E, (∀ w ∈ commSub E, g w = w) → g = 1
  card : Nat.card E = p * (p ^ 2 - 1)
  gen : ∃ A ≤ E, Nat.card A = p ∧ ⨆ e ∈ E, cj e A = E

structure IsBlockSystem (p : ℕ) {V : Type*} [AddCommGroup V] [Module (ZMod p) V]
    (𝓔 : Set (Subgroup (LGL p V))) : Prop where
  isBlock : ∀ E ∈ 𝓔, IsBlock p E
  commute : ∀ E ∈ 𝓔, ∀ E' ∈ 𝓔, E ≠ E' → ∀ g ∈ E, ∀ g' ∈ E', g * g' = g' * g
  trivial_on : ∀ E ∈ 𝓔, ∀ E' ∈ 𝓔, E ≠ E' → ∀ g ∈ E, ∀ w ∈ commSub E', g w = w
  indep : iSupIndep (fun E : 𝓔 => commSub (E : Subgroup (LGL p V)))

structure Hyp (H : Subgroup (LGL p V)) : Prop where
  solvable : Group.IsSolvable H
  noP : ∀ N : Subgroup (LGL p V), N ≤ H → (N.subgroupOf H).Normal → IsPGroup p N → N = ⊥

@[expose] def blocks (H : Subgroup (LGL p V)) : Set (Subgroup (LGL p V)) :=
  {E | ∃ A, IsAVMin H A ∧ E = blk H A}

@[expose] def Qp (p : ℕ) {G : Type*} [Group G] (H : Subgroup G) : Subgroup G :=
  ⨆ (N : Subgroup G) (_ : N ≤ H ∧ (N.subgroupOf H).Normal ∧ Nat.Coprime p (Nat.card N)), N

@[expose] def rp (p : ℕ) : ℕ := if p = 2 then 3 else 2

@[expose] def kerOn (H : Subgroup (LGL p V)) (W : Submodule (ZMod p) V) : Subgroup (LGL p V) where
  carrier := {g | g ∈ H ∧ ∀ w ∈ W, g w = w}
  one_mem' := ⟨H.one_mem, fun _ _ => rfl⟩
  mul_mem' := fun {a b} ha hb =>
    ⟨H.mul_mem ha.1 hb.1, fun w hw => by
      change a (b w) = w
      rw [hb.2 w hw, ha.2 w hw]⟩
  inv_mem' := fun {a} ha =>
    ⟨H.inv_mem ha.1, fun w hw => by
      conv_lhs => rw [← ha.2 w hw]
      exact a.symm_apply_apply w⟩

end CFSG.SignalizerFunctorTheorem.Quadratic

