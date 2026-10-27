module

public import CFSG.LocalAnalysis.QuasithinUnique.PushingUp.Blocks

public section

namespace CFSG.Quasithin.C116Two

open CFSG.QuasithinUnique CFSG.Open

variable {G : Type} [Group G]

instance evenWeight_addCommGroup (m : ℕ) : AddCommGroup (evenWeight m) :=
  AddSubgroup.toAddCommGroup _

structure ModData (L : Subgroup G) (V : Type) [CommGroup V] where
  ρ : ↥L →* MulAut V
  β : ↥(blockU L) →* V
  surj : Function.Surjective β
  ker : β.ker = (blockZ L).subgroupOf (blockU L)
  equiv : ∀ (ℓ : ↥L) (u v : ↥(blockU L)), (v : G) = ℓ * u * ℓ⁻¹ → β v = ρ ℓ (β u)
  faithful : ∀ ℓ : ↥L, ρ ℓ = 1 → (ℓ : G) ∈ blockQ L

@[expose] def NatCountMod (V : Type) [CommGroup V] (Lh : Subgroup (MulAut V)) : Prop :=
  ∀ B : Subgroup (MulAut V), IsElemAbelian 2 B → (∀ b ∈ B, ∀ l ∈ Lh, b * l * b⁻¹ ∈ Lh) →
    Nat.card B * Nat.card {x : V // ∀ b ∈ B, b x = x} ≤ Nat.card V

@[expose] def permActEquiv (m : ℕ) (σ : Equiv.Perm (Fin m)) : evenWeight m ≃+ evenWeight m where
  toFun x := ⟨fun i => (x : Fin m → ZMod 2) (σ⁻¹ i), by
    have hx : ∑ i, (x : Fin m → ZMod 2) i = 0 := x.2
    show ∑ i, (x : Fin m → ZMod 2) (σ⁻¹ i) = 0
    rw [Equiv.sum_comp σ⁻¹ (fun i => (x : Fin m → ZMod 2) i)]
    exact hx⟩
  invFun x := ⟨fun i => (x : Fin m → ZMod 2) (σ i), by
    have hx : ∑ i, (x : Fin m → ZMod 2) i = 0 := x.2
    show ∑ i, (x : Fin m → ZMod 2) (σ i) = 0
    rw [Equiv.sum_comp σ (fun i => (x : Fin m → ZMod 2) i)]
    exact hx⟩
  left_inv x := by
    apply Subtype.ext
    funext i
    simp
  right_inv x := by
    apply Subtype.ext
    funext i
    simp
  map_add' x y := by
    apply Subtype.ext
    funext i
    simp

@[expose] def permAct (m : ℕ) : Equiv.Perm (Fin m) →* MulAut (Multiplicative (evenWeight m)) where
  toFun σ := (permActEquiv m σ).toMultiplicative
  map_one' := by
    ext x
    simp [permActEquiv]
  map_mul' σ τ := by
    ext x
    simp [permActEquiv, mul_inv_rev]

@[expose] def altAct (m : ℕ) : alternatingGroup (Fin m) →* MulAut (Multiplicative (evenWeight m)) :=
  (permAct m).comp (alternatingGroup (Fin m)).subtype

@[expose] def slAct (F : Type) [Field F] :
    Matrix.SpecialLinearGroup (Fin 2) F →* MulAut (Multiplicative (Fin 2 → F)) where
  toFun A := (Matrix.SpecialLinearGroup.toLin' A).toAddEquiv.toMultiplicative
  map_one' := by
    ext x
    simp
  map_mul' A B := by
    ext x
    simp

theorem slAct_apply {F : Type} [Field F] (A : Matrix.SpecialLinearGroup (Fin 2) F)
    (x : Multiplicative (Fin 2 → F)) :
    Multiplicative.toAdd (slAct F A x) = (A : Matrix (Fin 2) (Fin 2) F).mulVec (Multiplicative.toAdd x) := by
  simp [slAct, Matrix.SpecialLinearGroup.toLin'_apply]

theorem permAct_apply (m : ℕ) (σ : Equiv.Perm (Fin m)) (x : Multiplicative (evenWeight m)) (i : Fin m) :
    ((Multiplicative.toAdd (permAct m σ x) : evenWeight m) : Fin m → ZMod 2) i =
      ((Multiplicative.toAdd x : evenWeight m) : Fin m → ZMod 2) (σ⁻¹ i) := rfl

end CFSG.Quasithin.C116Two
