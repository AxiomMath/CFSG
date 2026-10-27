module

public import CFSG.LocalAnalysis.UniquenessCase.UCFront09b
public import CFSG.Quasithin.Background.A3Structure316
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8U37B
public import CFSG.GH74.GLS.IVK.Proofs2.Std44

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F09 (IsSL2Cover)

@[expose] def U37Outer : Prop :=
  ∀ (A : Type) [Group A] [Finite A] (X : Subgroup A), LieModel ↥X .PSU 3 7 1 →
    ∀ E : Subgroup A, E ≤ X → IsSL2Cover ↥E 7 1 → ∀ D₃ : Subgroup A, D₃ ≤ E →
      Nat.card D₃ = 3 → ∃ g ∈ X, g ∈ normalizer (E : Set A) ∧ g ∈ normalizer (D₃ : Set A) ∧
        ¬ ∃ e ∈ E, ∀ x ∈ E, g * x * g⁻¹ = e * x * e⁻¹

theorem u37_centralizer_gu2 {X : Type} [Group X] [Finite X] (hX : LieModel X .PSU 3 7 1)
    {z : X} (hz : orderOf z = 2) :
    ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 49 ∧
      Nonempty (↥(centralizer ({z} : Set X)) ≃* ↥(CFSG.Quasithin.StatedGU 2 7 F)) := by
  have hclass : StatedClassicalModel X .PSU 3 7 1 :=
    LieModel.statedClassicalModel hX (by decide)
  obtain ⟨-, F, hFfield, hFfin, hFcard, ⟨e⟩⟩ := hclass
  have hdata : CFSG.LocalAnalysis.ComponentInitial.UnitaryFieldData 7 1 F :=
    ⟨by norm_num, le_rfl, by rw [hFcard]; norm_num⟩
  have hw : orderOf (e z) = 2 := by rw [MulEquiv.orderOf_eq]; exact hz
  obtain ⟨N, hN, hcard, ⟨iso⟩⟩ :=
    CFSG.GH74.GLS.IVK.Proofs2.Lemma41aU3.u37_exists_centralizer_quotient_card
      (p := 7) (n := 1) hdata (by norm_num) hw
  have hNcard : Nat.card N = 1 := by rw [hcard]; norm_num
  have hbot : N = ⊥ := Subgroup.card_eq_one.1 hNcard
  refine ⟨F, hFfield, hFfin, by rw [hFcard]; norm_num, ⟨?_⟩⟩
  exact (CFSG.GH74.GLS.IVK.Proofs2.centralizerEquiv e z).trans
    (iso.trans ((QuotientGroup.quotientMulEquivOfEq hbot).trans QuotientGroup.quotientBot))

theorem u37Outer_of_centralizer
    (h : ∀ (X : Type) (_ : Group X) (_ : Finite X), LieModel X .PSU 3 7 1 →
      ∀ z : X, orderOf z = 2 →
        ∃ (F : Type) (_ : Field F) (_ : Finite F), Nat.card F = 49 ∧
          Nonempty (↥(centralizer ({z} : Set X)) ≃* ↥(CFSG.Quasithin.StatedGU 2 7 F))) :
    U37Outer := by
  intro A _ _ X hX E hE hEsl D₃ hD₃E hD₃
  exact u37_exists_outer_of_centralizer_structure h A X hX E hE hEsl D₃ hD₃E hD₃

theorem u37Outer_holds : U37Outer :=
  u37Outer_of_centralizer fun _ _ _ hX _ hz => u37_centralizer_gu2 hX hz

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
