module

public import CFSG.RankThree.PartTwo.Sec19.SeitzTrialityModel

public section

open CFSG.RankThree.PartTwo.Sec19
open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag
open scoped commutatorElement

namespace CFSG.RankThree.PartTwo.Sec4.E27


variable {n : ℕ} {X : Type} [Field X] [Finite X] {σ : X ≃+* X}

noncomputable abbrev cenX (σ : X ≃+* X) (x : C0 σ) : Subgroup (C0 σ) :=
  Subgroup.centralizer ({x} : Set (C0 σ))

noncomputable abbrev layerSub (σ : X ≃+* X) (x : C0 σ) : Subgroup (C0 σ) := ⁅cenX σ x, cenX σ x⁆

@[expose] def LayerLinearModel (σ : X ≃+* X) (x : C0 σ) : Prop :=
  ∃ (F : Type) (_ : Field F) (_ : Finite F), 4 ≤ Nat.card F ∧ 3 ∣ Nat.card F - 1 ∧
    ∃ e : layerSub σ x ≃*
        Matrix.SpecialLinearGroup (Fin 3) F,
      ∀ g ∈ cenX σ x, ∃ N : Matrix.GeneralLinearGroup (Fin 3) F,
        ∀ d d' : layerSub σ x,
          (d' : C0 σ) = g * d * g⁻¹ →
            ((e d' : Matrix.SpecialLinearGroup (Fin 3) F) : Matrix (Fin 3) (Fin 3) F) =
              (N : Matrix (Fin 3) (Fin 3) F) * ((e d : Matrix.SpecialLinearGroup (Fin 3) F) :
                Matrix (Fin 3) (Fin 3) F) * ((N⁻¹ : Matrix.GeneralLinearGroup (Fin 3) F) :
                  Matrix (Fin 3) (Fin 3) F)

@[expose] def LayerUnitaryModel (σ : X ≃+* X) (n : ℕ) (x : C0 σ) : Prop :=
  ∃ (F : Type) (_ : Field F) (hF : UnitaryFieldData 2 n F),
    ∃ e : layerSub σ x ≃*
        unitarySU 2 n F 3,
      ∀ g ∈ cenX σ x,
        ∃ A : CFSG.RankThree.PartTwo.KFacts.unitaryIsom3 hF,
          ∀ d d' : layerSub σ x,
            (d' : C0 σ) = g * d * g⁻¹ →
              e d' = CFSG.RankThree.PartTwo.KFacts.suConj hF A (e d)

end CFSG.RankThree.PartTwo.Sec4.E27
