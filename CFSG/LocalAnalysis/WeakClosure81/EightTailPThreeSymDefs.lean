module

public import CFSG.Open.FusionDefs
public import CFSG.Timmesfeld.Bridge.Asc72Defs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open Equiv Equiv.Perm CFSG.Open CFSG.Timmesfeld.Bridge.Asc72

@[expose] def symPi {Y : Type} [Group Y] {m : ℕ} (e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)) :
    Y →* Perm (Fin m) :=
  e.toMonoidHom.comp (QuotientGroup.mk' (fusionOddCore Y))

@[expose] def symT {Y : Type} [Group Y] (t : Y) (P : Subgroup Y) : Set Y :=
  {y | IsConj t y} ∩ (P : Set Y)

structure SymSetting {Y : Type} [Group Y] [Finite Y] {m : ℕ}
    (e : Y ⧸ fusionOddCore Y ≃* Perm (Fin m)) (t : Y) (P : Sylow 2 Y) : Prop where
  six_le : 6 ≤ m
  mul_self : t * t = 1
  swap : (symPi e t).IsSwap
  oddClass : IsOddTranspClass {y : Y | IsConj t y}
  mem : t ∈ (P : Subgroup Y)
  central : ∀ y ∈ (P : Subgroup Y), t * y = y * t

end CFSG.LocalAnalysis.WeakClosure81

end
