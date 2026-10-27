module

public import CFSG.Quasithin.AppendixH.H12.Basic

public section

namespace CFSG.Quasithin.AppendixH.H12

open CFSG.Quasithin CFSG.Open CFSG.ASVolI.ChH

structure Trans {Γ : Type*} [Group Γ] (L' : Subgroup Γ) {G : Type*} [Group G] (L : Subgroup G)
    {V' V : Type*} [CommGroup V'] [CommGroup V] (ρ' : Γ →* MulAut V') (ρ : G →* MulAut V) where
  φ : ↥L' ≃* ↥L
  β : V' ≃* V
  compat : ∀ (g : ↥L') (v : V'), ρ (φ g : G) (β v) = β (ρ' (g : Γ) v)

namespace Trans

variable {Γ : Type*} [Group Γ] {L' : Subgroup Γ} {G : Type*} [Group G] {L : Subgroup G}
  {V' V : Type*} [CommGroup V'] [CommGroup V] {ρ' : Γ →* MulAut V'} {ρ : G →* MulAut V}
  (τ : Trans L' L ρ' ρ)

@[expose] def toG (X : Subgroup Γ) : Subgroup G :=
  ((X.subgroupOf L').map τ.φ.toMonoidHom).map L.subtype

@[expose] def fromG (Y : Subgroup G) : Subgroup Γ :=
  ((Y.subgroupOf L).map τ.φ.symm.toMonoidHom).map L'.subtype

@[expose] def toV (P : Subgroup V') : Subgroup V := P.map τ.β.toMonoidHom

@[expose] def iota {K : Type*} [Field K] (ι : K →+* AddMonoid.End (Additive V')) :
    K →+* AddMonoid.End (Additive V) where
  toFun c := (τ.β.toAdditive : Additive V' ≃+ Additive V).toAddMonoidHom.comp
    ((ι c).comp (τ.β.toAdditive : Additive V' ≃+ Additive V).symm.toAddMonoidHom)
  map_one' := by
    rw [map_one]
    refine AddMonoidHom.ext fun x => ?_
    show τ.β.toAdditive ((1 : AddMonoid.End (Additive V')) (τ.β.toAdditive.symm x)) =
      (1 : AddMonoid.End (Additive V)) x
    simp
  map_mul' a b := by
    rw [map_mul]
    refine AddMonoidHom.ext fun x => ?_
    show τ.β.toAdditive ((ι a * ι b : AddMonoid.End (Additive V')) (τ.β.toAdditive.symm x)) =
      τ.β.toAdditive ((ι a) (τ.β.toAdditive.symm
        (τ.β.toAdditive ((ι b) (τ.β.toAdditive.symm x)))))
    simp
  map_zero' := by
    rw [map_zero]
    refine AddMonoidHom.ext fun x => ?_
    show τ.β.toAdditive ((0 : AddMonoid.End (Additive V')) (τ.β.toAdditive.symm x)) =
      (0 : AddMonoid.End (Additive V)) x
    simp
  map_add' a b := by
    rw [map_add]
    refine AddMonoidHom.ext fun x => ?_
    show τ.β.toAdditive (((ι a + ι b : AddMonoid.End (Additive V')))
        (τ.β.toAdditive.symm x)) =
      τ.β.toAdditive ((ι a) (τ.β.toAdditive.symm x)) +
        τ.β.toAdditive ((ι b) (τ.β.toAdditive.symm x))
    rw [show ((ι a + ι b : AddMonoid.End (Additive V')) (τ.β.toAdditive.symm x)) =
      ι a (τ.β.toAdditive.symm x) + ι b (τ.β.toAdditive.symm x) from rfl, map_add]

@[expose] def form {K : Type*} (f : V' → V' → K) : V → V → K :=
  fun u v => f (τ.β.symm u) (τ.β.symm v)

end Trans

end CFSG.Quasithin.AppendixH.H12
