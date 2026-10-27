module

public import CFSG.Quasithin.AppendixH.H15.Vocab

public section

open scoped Pointwise Matrix commutatorElement

namespace CFSG.ASVolI.ChH

open CFSG.Quasithin CFSG.Open CFSG.Monster.Code CFSG.Quasithin.H.Mathieu

@[expose] def cenMS {V : Type*} [CommGroup V] {Γ : Subgroup S24} (ρ : ↥Γ →* MulAut V)
    (W : Subgroup V) : Subgroup S24 :=
  (cenM ρ W).map Γ.subtype

@[expose] def IsCenterGen (T₀ : Subgroup S24) (z : S24) : Prop :=
  z ∈ T₀ ∧ ∀ t ∈ T₀, (t ∈ Subgroup.zpowers z ↔ ∀ s ∈ T₀, s * t = t * s)

@[expose] def Chain163 {V : Type*} [CommGroup V] {Γ : Subgroup S24} (ρ : ↥Γ →* MulAut V)
    (Q : Finset (Finset (Fin 24))) (V₈ V₉ : Subgroup V) : Prop :=
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Q))) ⊥ (fixV (rImg ρ (KY Γ Q))) ∧
  rk ↥(fixV (rImg ρ (KY Γ Q))) = 4 ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Q))) (fixV (rImg ρ (KY Γ Q))) V₈ ∧
  rk ↥V₈ = 8 ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Q))) V₈ V₉ ∧ rk ↥V₉ = 9 ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Q))) V₉ ⊤

@[expose] def Chain164 {V : Type*} [CommGroup V] {Γ : Subgroup S24} (ρ : ↥Γ →* MulAut V)
    (Hx : Finset (Fin 24)) (V₅ V₆ : Subgroup V) : Prop :=
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Hx))) ⊥ (fixV (rImg ρ (KY Γ Hx))) ∧
  rk ↥(fixV (rImg ρ (KY Γ Hx))) = 1 ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Hx))) (fixV (rImg ρ (KY Γ Hx))) V₅ ∧
  rk ↥V₅ = 5 ∧ V₅ = commV (rImg ρ (KY Γ Hx)) ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Hx))) V₅ V₆ ∧ rk ↥V₆ = 6 ∧
  IsChiefFactorUnder (actsOnModule (rImg ρ (MY Γ Hx))) V₆ ⊤

end CFSG.ASVolI.ChH
