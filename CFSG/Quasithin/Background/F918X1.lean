module

public import CFSG.Quasithin.Background.B4Statement
public import CFSG.Quasithin.Background.B5NonInputs
public import CFSG.Quasithin.Background.F918X0

public section

namespace CFSG.Quasithin.F918X

open CFSG.Quasithin

@[expose] def CentralData {W : Type} [CommGroup W] (L : Subgroup (MulAut W)) : Prop :=
  Subgroup.center ↥L = ⊥ ∨ IsL345Type ↥L ∨
    (Nat.card (Subgroup.center ↥L) = 3 ∧
      Nonempty (↥L ⧸ Subgroup.center ↥L ≃* ↥(alternatingGroup (Fin 6))))

@[expose] def Case1Twist : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L A : Subgroup (MulAut V), B4Hyp G L → B42Case1 G L A → StableMod L ∧ CentralData L

@[expose] def Case2Twist : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B4Hyp G L → B42Case2 G L → TwoClassMod L ∧ CentralData L

@[expose] def Case3TwistOne : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B4Hyp G L → BinaryNaturalSp4 (ffJ G) ⊤ ⊥ 1 →
      TwoClassMod L ∧ CentralData L

@[expose] def Case3TwistBig : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (n : ℕ), 2 ≤ n → B4Hyp G L → BinaryNaturalSp4 (ffJ G) ⊤ ⊥ n →
      ffJ G = L → TwoClassMod L ∧ CentralData L

@[expose] def Case4TwistOne : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B4Hyp G L → G2Natural (ffJ G) ⊤ ⊥ 1 → StableMod L ∧ CentralData L

@[expose] def Case4TwistBig : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ (G L : Subgroup (MulAut V)) (n : ℕ), 2 ≤ n → B4Hyp G L → G2Natural (ffJ G) ⊤ ⊥ n →
      ffJ G = L → StableMod L ∧ CentralData L

@[expose] def Case5Twist : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L A : Subgroup (MulAut V), B4Hyp G L → B42Case5 G A → StableMod L ∧ CentralData L

@[expose] def Case6Twist : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L A : Subgroup (MulAut V), B4Hyp G L → B42Case6 G L A → TwoClassMod L ∧ CentralData L

@[expose] def Case7Twist : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L A : Subgroup (MulAut V), B4Hyp G L → B42Case7 G L A → TwoClassMod L ∧ CentralData L

@[expose] def Case8Twist : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L A : Subgroup (MulAut V), B4Hyp G L → B42Case8 G L A → TwoClassMod L ∧ CentralData L

@[expose] def Case9Twist : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L : Subgroup (MulAut V), B4Hyp G L → B42Case9 G L → TwoClassMod L ∧ CentralData L

@[expose] def Case10Twist : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L A : Subgroup (MulAut V), B4Hyp G L → B42Case10 G L A → StableMod L ∧ CentralData L

@[expose] def Case11Twist : Prop :=
  ∀ (V : Type) [CommGroup V] [Finite V], (∀ v : V, v ^ 2 = 1) →
    ∀ G L A : Subgroup (MulAut V), B4Hyp G L → B42Case11 G L A → TwoClassMod L ∧ CentralData L

@[expose] def NoOddCoverHatA6 : Prop :=
  ∀ (E Γ : Type) [Group E] [Finite E] [Group Γ], CFSG.IsQuasisimple E →
    Nat.card (Subgroup.center Γ) = 3 →
    Nonempty (Γ ⧸ Subgroup.center Γ ≃* ↥(alternatingGroup (Fin 6))) →
    ∀ f : E →* Γ, Function.Surjective f → (∀ x ∈ f.ker, Odd (orderOf x)) → Function.Injective f

end CFSG.Quasithin.F918X
