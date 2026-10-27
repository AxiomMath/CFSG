module

public import CFSG.LocalAnalysis.WeakClosure81.EightOne
public import CFSG.LocalAnalysis.WeakClosure81.SevenDefs

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Open Subgroup

variable {G : Type*} [Group G]

@[expose] def omegaOrb (V H T : Subgroup G) : Set (Subgroup G) :=
  {U | ∃ k ∈ kSub V H (eSub V H T), U = conjSubgroup V k}

@[expose] def kGen (V H T : Subgroup G) : Subgroup G :=
  ⨆ U ∈ omegaOrb V H T, U

@[expose] def CentralizersInM (V H T : Subgroup G) : Prop :=
  ∀ z ∈ T, (∀ t ∈ T, z * t = t * z) → z ≠ 1 →
    H ⊓ Subgroup.centralizer ({z} : Set G) ≤ Subgroup.normalizer (V : Set G)

@[expose] def NormalizersInM (V H W : Subgroup G) : Prop :=
  ∀ X : Subgroup G, X ≠ ⊥ →
    X ≤ Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (W : Set G) →
    Subgroup.normalizer (V : Set G) ⊓ Subgroup.normalizer (W : Set G) ≤
      Subgroup.normalizer (X : Set G) →
    H ⊓ Subgroup.normalizer (X : Set G) ≤ Subgroup.normalizer (V : Set G)

end CFSG.LocalAnalysis.WeakClosure81
