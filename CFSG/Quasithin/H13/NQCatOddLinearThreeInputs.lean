module

public import CFSG.CharacterTheory.Wreathed.OddLinearThreeCentralizerCore
public import CFSG.LocalAnalysis.ComponentInitial.LinearFlagElation
public import CFSG.Assembly.Defs
public import CFSG.Foundations.Basic

public section

namespace CFSG.Quasithin.H13.NQCat

open Subgroup Module CFSG.Wreathed.OddLinearThreeCentralizerCore
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag

variable {F : Type*} [Field F]

@[expose] def preservingFixing (V₁ V₂ : Submodule F (Fin 3 → F)) : Subgroup (SL3 F) where
  carrier := {g | (∀ v ∈ V₁, Matrix.SpecialLinearGroup.toLin' g v ∈ V₁) ∧
    ∀ v ∈ V₂, Matrix.SpecialLinearGroup.toLin' g v = v}
  one_mem' := ⟨fun v hv => by simpa using hv, fun v _ => by simp⟩
  mul_mem' := by
    rintro g h ⟨hg1, hg2⟩ ⟨hh1, hh2⟩
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    · rw [map_mul, LinearEquiv.mul_apply]
      exact hg1 _ (hh1 v hv)
    · rw [map_mul, LinearEquiv.mul_apply, hh2 v hv, hg2 v hv]
  inv_mem' := by
    rintro g ⟨hg1, hg2⟩
    have hinv : ∀ w, Matrix.SpecialLinearGroup.toLin' g⁻¹ (Matrix.SpecialLinearGroup.toLin' g w) =
        w := fun w => by
      rw [← LinearEquiv.mul_apply, ← map_mul, inv_mul_cancel, map_one]
      rfl
    refine ⟨fun v hv => ?_, fun v hv => ?_⟩
    ·
      let r : V₁ →ₗ[F] V₁ := (Matrix.SpecialLinearGroup.toLin' g).toLinearMap.restrict hg1
      have hr : Function.Injective r := fun a b hab => by
        have h := congrArg Subtype.val hab
        exact Subtype.ext ((Matrix.SpecialLinearGroup.toLin' g).injective h)
      obtain ⟨w, hw⟩ := (LinearMap.injective_iff_surjective.mp hr) ⟨v, hv⟩
      have hgw : Matrix.SpecialLinearGroup.toLin' g w = v := congrArg Subtype.val hw
      rw [← hgw, hinv]
      exact w.2
    · have h := hinv v
      rwa [hg2 v hv] at h

@[expose] def OddLinearThreeInvolutionSylowStructure (F : Type*) [Field F] [Finite F] : Prop :=
  Odd (Nat.card F) → 5 ≤ Nat.card F →
  ∀ (D : Subgroup (SL3 F)) [D.Normal], D ≤ scalars 3 F →
    (∀ T : Sylow 2 (SL3 F ⧸ D), IsCyclic (center (T : Subgroup (SL3 F ⧸ D))) ∧
      ∀ E : Subgroup (SL3 F ⧸ D), E ≤ T → IsElementaryAbelian 2 E → Nat.card E ≤ 4) ∧
    ∀ t : SL3 F ⧸ D, orderOf t = 2 →
      ∃ z : SL3 F, orderOf z = 2 ∧ QuotientGroup.mk' D z = t ∧
        (∀ w : SL3 F, orderOf w = 2 → QuotientGroup.mk' D w = t → w = z) ∧
        finrank F (minusSpace (matrixAction F z).toLinearMap) = 2 ∧
        finrank F (plusSpace (matrixAction F z).toLinearMap) = 1 ∧
        (CFSG.perfectResidual (centralizer ({t} : Set (SL3 F ⧸ D)))).map
            (centralizer ({t} : Set (SL3 F ⧸ D))).subtype =
          (preservingFixing (minusSpace (matrixAction F z).toLinearMap)
            (plusSpace (matrixAction F z).toLinearMap)).map (QuotientGroup.mk' D) ∧
        Set.InjOn (QuotientGroup.mk' D) (preservingFixing
          (minusSpace (matrixAction F z).toLinearMap) (plusSpace (matrixAction F z).toLinearMap)) ∧
        Nonempty (↥((preservingFixing (minusSpace (matrixAction F z).toLinearMap)
          (plusSpace (matrixAction F z).toLinearMap)).map (QuotientGroup.mk' D)) ≃*
            Matrix.SpecialLinearGroup (Fin 2) F) ∧
        t ∈ (preservingFixing (minusSpace (matrixAction F z).toLinearMap)
          (plusSpace (matrixAction F z).toLinearMap)).map (QuotientGroup.mk' D) ∧
        ∀ l ∈ (preservingFixing (minusSpace (matrixAction F z).toLinearMap)
          (plusSpace (matrixAction F z).toLinearMap)).map (QuotientGroup.mk' D), l * t = t * l

end CFSG.Quasithin.H13.NQCat
