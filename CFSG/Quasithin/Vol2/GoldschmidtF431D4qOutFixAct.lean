module

public import CFSG.LocalAnalysis.ComponentClassification.AS76bSec8D4Unip
public import CFSG.Quasithin.Vol2.GoldschmidtF431D4qStructNorm

public section

namespace CFSG.Quasithin.H13.F431.D4q.Out

open CFSG.ComponentClassification.RankTwoExceptional.D4 CFSG.Quasithin.H13.F431.D4q.Struct
  CFSG.LieType.Chevalley CFSG.Blueprint CFSG.Blueprint.Chevalley

set_option linter.unusedSectionVars false


section Entrywise

variable {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K)

theorem map_pinnedX (α : Fin TwistTag.D4.tag.rank → ℤ) (c : K) :
    Units.map (entrywiseHom δ.toRingHom) (pinnedX TwistTag.D4.tag K α c) =
      pinnedX TwistTag.D4.tag K α (δ c) :=
  Units.ext (entrywise_pinnedX δ.toRingHom α c)

theorem map_trialityOrbitProd (α : Fin TwistTag.D4.tag.rank → ℤ) (c : K) :
    Units.map (entrywiseHom δ.toRingHom)
        (trialityOrbitProd K σ.toRingHom α c : ModGL TwistTag.D4.tag K) =
      (trialityOrbitProd K σ.toRingHom α (δ c) : ModGL TwistTag.D4.tag K) := by
  rw [coe_trialityOrbitProd, coe_trialityOrbitProd, map_mul, map_mul, map_pinnedX, map_pinnedX,
    map_pinnedX]
  have h1 : δ (σ c) = σ (δ c) := ringEquiv_comm_of_finite σ δ c
  have h2 : δ (σ (σ c)) = σ (σ (δ c)) := by rw [ringEquiv_comm_of_finite σ δ, h1]
  simp only [RingEquiv.toRingHom_eq_coe, RingHom.coe_coe, h1, h2]

theorem map_d4x₁ (a : K) :
    Units.map (entrywiseHom δ.toRingHom) (d4x₁ K σ a) = d4x₁ K σ (δ a) :=
  map_trialityOrbitProd σ δ _ a

theorem map_d4x₂ (b : K) :
    Units.map (entrywiseHom δ.toRingHom) (d4x₂ K b) = d4x₂ K (δ b) :=
  map_pinnedX δ _ b

theorem map_d4x₃ (c : K) :
    Units.map (entrywiseHom δ.toRingHom) (d4x₃ K σ c) = d4x₃ K σ (δ c) :=
  map_trialityOrbitProd σ δ _ c

theorem map_d4x₄ (d : K) :
    Units.map (entrywiseHom δ.toRingHom) (d4x₄ K σ d) = d4x₄ K σ (δ d) :=
  map_trialityOrbitProd σ δ _ d

theorem map_d4x₅ (e : K) :
    Units.map (entrywiseHom δ.toRingHom) (d4x₅ K e) = d4x₅ K (δ e) :=
  map_pinnedX δ _ e

theorem map_d4x₆ (f : K) :
    Units.map (entrywiseHom δ.toRingHom) (d4x₆ K f) = d4x₆ K (δ f) :=
  map_pinnedX δ _ f

theorem map_d4v (b c d e f : K) :
    Units.map (entrywiseHom δ.toRingHom) (d4v K σ b c d e f) =
      d4v K σ (δ b) (δ c) (δ d) (δ e) (δ f) := by
  rw [d4v, d4v, map_mul, map_mul, map_mul, map_mul, map_d4x₂, map_d4x₃, map_d4x₄, map_d4x₅,
    map_d4x₆]

theorem map_d4coord (a b c d e f : K) :
    Units.map (entrywiseHom δ.toRingHom) (d4x₁ K σ a * d4v K σ b c d e f) =
      d4x₁ K σ (δ a) * d4v K σ (δ b) (δ c) (δ d) (δ e) (δ f) := by
  rw [map_mul, map_d4x₁, map_d4v]

end Entrywise

section Fixed

variable {K : Type} [Field K] [Finite K] (σ δ : K ≃+* K)

theorem coe_fieldActor_coord (u : Cm σ) {a b c d e f : K}
    (hu : (u : ModGL TwistTag.D4.tag K) = d4x₁ K σ a * d4v K σ b c d e f) :
    ((fieldActor σ δ u : Cm σ) : ModGL TwistTag.D4.tag K) =
      d4x₁ K σ (δ a) * d4v K σ (δ b) (δ c) (δ d) (δ e) (δ f) := by
  rw [coe_fieldActor, hu, map_d4coord]

theorem fieldActor_fix_iff (u : Cm σ) {a b c d e f : K}
    (hu : (u : ModGL TwistTag.D4.tag K) = d4x₁ K σ a * d4v K σ b c d e f) :
    fieldActor σ δ u = u ↔
      δ a = a ∧ δ b = b ∧ δ c = c ∧ δ d = d ∧ δ e = e ∧ δ f = f := by
  constructor
  · intro h
    have h1 : ((fieldActor σ δ u : Cm σ) : ModGL TwistTag.D4.tag K) =
        (u : ModGL TwistTag.D4.tag K) := congrArg Subtype.val h
    rw [coe_fieldActor_coord σ δ u hu, hu] at h1
    exact d4coord_injective σ h1
  · rintro ⟨h1, h2, h3, h4, h5, h6⟩
    refine Subtype.ext ?_
    rw [coe_fieldActor_coord σ δ u hu, hu, h1, h2, h3, h4, h5, h6]

end Fixed

end CFSG.Quasithin.H13.F431.D4q.Out
