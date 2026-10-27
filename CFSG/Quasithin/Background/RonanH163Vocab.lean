module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.Quasithin.Background.D2Basic
public import CFSG.Quasithin.Background.RonanH143Vocab
public import CFSG.Sporadic.Schreier.J4SSylowBase

public section

open scoped Pointwise

namespace CFSG.Quasithin.RonanH163

open CFSG.Open CFSG.Quasithin CFSG.Monster.Code CFSG.Quasithin.RonanH143

@[expose] def IsActsInv {A : Type*} [Group A] (acts : Set (A → A)) (U : Subgroup A) : Prop :=
  ∀ f ∈ acts, ∀ u ∈ U, f u ∈ U

@[expose] def IsChiefFactorUnder {A : Type*} [Group A] (acts : Set (A → A)) (X Y : Subgroup A) :
    Prop :=
  X < Y ∧ IsActsInv acts X ∧ IsActsInv acts Y ∧
    ∀ W : Subgroup A, X ≤ W → W ≤ Y → IsActsInv acts W → W = X ∨ W = Y

@[expose] def actsOnModule {V : Type*} [CommGroup V] (Y : Subgroup (MulAut V)) : Set (V → V) :=
  {f | ∃ y ∈ Y, f = fun v => y v}

@[expose] def rImg {V : Type*} [CommGroup V] {Γ : Subgroup P24} (ρ : ↥Γ →* MulAut V)
    (A : Subgroup P24) : Subgroup (MulAut V) :=
  (A.subgroupOf Γ).map ρ

@[expose] def cenM {V : Type*} [CommGroup V] {Γ : Subgroup P24} (ρ : ↥Γ →* MulAut V)
    (W : Subgroup V) : Subgroup ↥Γ :=
  (centSub W).comap ρ

@[expose] def InducesOnSub {V : Type*} [CommGroup V] (G : Subgroup (MulAut V)) (U Z : Subgroup V)
    (A : Type*) [CommGroup A] (S : Subgroup A) (Γ : Subgroup (MulAut A)) : Prop :=
  Z ≤ U ∧ (∀ g ∈ G, ∀ u ∈ U, g u ∈ U) ∧ (∀ g ∈ G, ∀ z ∈ Z, g z ∈ Z) ∧
  ∃ β : ↥U →* A, β.range = S ∧ (∀ u : ↥U, β u = 1 ↔ (u : V) ∈ Z) ∧
    (∀ g ∈ G, ∃ γ ∈ Γ, ∀ u u' : ↥U, (u' : V) = g u → β u' = γ (β u)) ∧
    (∀ γ ∈ Γ, ∃ g ∈ G, ∀ u u' : ↥U, (u' : V) = g u → β u' = γ (β u))

@[expose] def IsTranspAxis {V : Type*} [CommGroup V] (g : MulAut V) (U W : Subgroup V) (c : V) :
    Prop :=
  (∀ x ∈ W, g x * x⁻¹ ∈ U) ∧ ∀ x : V, x ∉ W → g x * x⁻¹ * c⁻¹ ∈ U

@[expose] def FullTranspAxis {V : Type*} [CommGroup V] (G X : Subgroup (MulAut V)) (U W : Subgroup V) :
    Prop :=
  (∀ g ∈ X, ∃ c ∈ W, IsTranspAxis g U W c) ∧ (∀ c ∈ W, ∃ g ∈ X, IsTranspAxis g U W c) ∧
  (∀ g ∈ X, (∀ x : V, g x * x⁻¹ ∈ U) → g = 1) ∧
  (∀ h ∈ G, ∀ g ∈ X, ∀ c : V, IsTranspAxis g U W c → IsTranspAxis (h * g * h⁻¹) U W (h c))

@[expose] def Chain163 {V : Type*} [CommGroup V] {Γ : Subgroup P24} (ρ : ↥Γ →* MulAut V)
    (Q : Finset (Finset (Fin 24))) (V₈ V₉ : Subgroup V) : Prop :=
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Q))) ⊥ (fixV (rImg ρ (KY Γ Q))) ∧
  rk ↥(fixV (rImg ρ (KY Γ Q))) = 4 ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Q))) (fixV (rImg ρ (KY Γ Q))) V₈ ∧
  rk ↥V₈ = 8 ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Q))) V₈ V₉ ∧ rk ↥V₉ = 9 ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Q))) V₉ ⊤

@[expose] def Concl163 {V : Type*} [CommGroup V] {Γ : Subgroup P24} (ρ : ↥Γ →* MulAut V)
    (Q : Finset (Finset (Fin 24))) : Prop :=
  (∃ V₈ V₉ : Subgroup V,
    Chain163 ρ Q V₈ V₉ ∧
    FullTranspAxis (rImg ρ (MY Γ Q)) (rImg ρ (KY Γ Q)) (fixV (rImg ρ (KY Γ Q))) V₉) ∧
  InducesOnSub (rImg ρ (MY Γ Q)) (fixV (rImg ρ (KY Γ Q))) ⊥ (G6.PermMod 5) (G6.coreMod 5)
    (G6.permAct 5).range ∧
  (cenM ρ (fixV (rImg ρ (KY Γ Q))) = (KY Γ Q).subgroupOf Γ ∧ IsPGroup 2 ↥(KY Γ Q))

end CFSG.Quasithin.RonanH163
