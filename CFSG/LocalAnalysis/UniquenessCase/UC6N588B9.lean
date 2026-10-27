module

import all CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.GroupA10Perm
public import CFSG.Blueprint.SourceClassicalTransport
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.LocalAnalysis.UniquenessCase.UC6N588B7
public import CFSG.RankThree.PartTwo.Sec4.Census.Item44TwoCoverModels

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC6.A10N588

open Equiv Equiv.Perm Subgroup
open CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.A10Perm

@[expose] def T5' : Finset (Fin 10) := {0, 1, 2, 3, 4}

theorem t₀_support : (t₀ : Perm (Fin 10)).support = {0, 1, 2} := by decide +kernel

theorem t₀_isThreeCycle : (t₀ : Perm (Fin 10)).IsThreeCycle :=
  _root_.card_support_eq_three_iff.1 (by rw [t₀_support]; rfl)

theorem a₁_mem_T5' : a₁ ∈ altA T5' := mem_altA.2 (by decide +kernel)

theorem T5'_T5 : Disjoint T5' T5 := by decide

theorem altA_mono {T T' : Finset (Fin 10)} (h : T ⊆ T') : altA T ≤ altA T' :=
  fun _ hx => mem_altA.2 ((mem_altA.1 hx).trans h)

theorem a₁_comm_T5 {x : A10} (hx : x ∈ altA T5) : a₁ * x = x * a₁ :=
  commute_altA T5'_T5 a₁_mem_T5' hx

theorem t₀_a₁_ne : t₀ * a₁ ≠ a₁ * t₀ := by decide +kernel

theorem a₂_x₃_ne : a₂ * x₃ ≠ x₃ * a₂ := by decide +kernel

theorem commute_t₀_of_fix {σ : A10} (hσ : ∀ i : Fin 10, (i : ℕ) < 5 → (σ : Perm (Fin 10)) i = i) :
    σ * t₀ = t₀ * σ := by
  apply commute_of_disjoint_support
  rw [t₀_support, Finset.disjoint_right]
  intro x hx hσx
  apply Equiv.Perm.mem_support.1 hσx
  apply hσ
  have h012 : ∀ y : Fin 10, y ∈ ({0, 1, 2} : Finset (Fin 10)) → (y : ℕ) < 5 := by decide
  exact h012 x hx

end CFSG.LocalAnalysis.UniquenessCase.UC6.A10N588
