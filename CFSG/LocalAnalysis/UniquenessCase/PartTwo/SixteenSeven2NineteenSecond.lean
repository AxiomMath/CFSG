module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2NineteenDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAk
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2EighteenBridge

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
  CFSG.LocalAnalysis.WeakClosure81
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c167_second_of_tilde (D : Data G) {V : Subgroup G} (hV : IsElemAbelian 2 V)
    (hM : D.M ≤ normalizer (V : Set G)) {A : Subgroup G} (hAM : A ≤ D.M)
    (hAel : IsElemAbelian 2 A) (hrk : 2 < rk ↥(barSub ⊥ V hV A))
    (h2 : Two19 (Mbar D.M ⊥ V hV)) : Second19 V A := by
  have hAst : A ≤ stabTil ⊥ V := fun m hm => s16c167_mem_stabTil_bot (hM (hAM hm))
  have hel : IsElemAbelian2 (barSub ⊥ V hV A) := isElemAbelian2_barSub hV hAel
  have hEX : barSub ⊥ V hV A ≤ Mbar D.M ⊥ V hV := barSub_mono ⊥ V hV hAM
  have hsq : ∀ e ∈ barSub ⊥ V hV A, e * e = 1 := by
    intro e he
    rw [← pow_two]
    exact hel.2 e he
  have hrkE : 3 ≤ rk ↥(barSub ⊥ V hV A) := by omega
  obtain ⟨F₁, F₂, hF₁, hF₂, hne, hm₁, hm₂, hfx₁, hfx₂⟩ :=
    h2 (barSub ⊥ V hV A) hEX hsq hel.1 hrkE
  intro B U hBU
  have hB₁A : preBarSub A ⊥ V hV F₁ ≤ A := inf_le_left
  have hB₁st : preBarSub A ⊥ V hV F₁ ≤ stabTil ⊥ V := hB₁A.trans hAst
  have hbar₁ : barSub ⊥ V hV (preBarSub A ⊥ V hV F₁) = F₁ := by
    rw [barSub_preBarSub]
    exact inf_eq_left.2 hF₁
  have hmq₁ : E3.mQuot A (preBarSub A ⊥ V hV F₁) = 1 :=
    (mQuot_barSub_preBarSub_gen hV hAst hF₁).symm.trans hm₁
  have hpre₁ : V ⊓ centralizer (preBarSub A ⊥ V hV F₁ : Set G) ≠
      V ⊓ centralizer (A : Set G) := by
    intro heq
    apply hfx₁
    have hpre : preCTilde ⊥ V (preBarSub A ⊥ V hV F₁) hV = preCTilde ⊥ V A hV := by
      rw [preCTilde_bot_eq hV hB₁st, preCTilde_bot_eq hV hAst, heq]
    have hfix := fixV_barSub_eq_of_preCTilde_eq hV hpre
    rwa [hbar₁] at hfix
  have hHyp₁ : Hyperplane1618 V A (preBarSub A ⊥ V hV F₁)
      (V ⊓ centralizer (preBarSub A ⊥ V hV F₁ : Set G)) :=
    ⟨hB₁A, hmq₁, rfl, hpre₁⟩
  have hB₂A : preBarSub A ⊥ V hV F₂ ≤ A := inf_le_left
  have hB₂st : preBarSub A ⊥ V hV F₂ ≤ stabTil ⊥ V := hB₂A.trans hAst
  have hbar₂ : barSub ⊥ V hV (preBarSub A ⊥ V hV F₂) = F₂ := by
    rw [barSub_preBarSub]
    exact inf_eq_left.2 hF₂
  have hmq₂ : E3.mQuot A (preBarSub A ⊥ V hV F₂) = 1 :=
    (mQuot_barSub_preBarSub_gen hV hAst hF₂).symm.trans hm₂
  have hpre₂ : V ⊓ centralizer (preBarSub A ⊥ V hV F₂ : Set G) ≠
      V ⊓ centralizer (A : Set G) := by
    intro heq
    apply hfx₂
    have hpre : preCTilde ⊥ V (preBarSub A ⊥ V hV F₂) hV = preCTilde ⊥ V A hV := by
      rw [preCTilde_bot_eq hV hB₂st, preCTilde_bot_eq hV hAst, heq]
    have hfix := fixV_barSub_eq_of_preCTilde_eq hV hpre
    rwa [hbar₂] at hfix
  have hHyp₂ : Hyperplane1618 V A (preBarSub A ⊥ V hV F₂)
      (V ⊓ centralizer (preBarSub A ⊥ V hV F₂ : Set G)) :=
    ⟨hB₂A, hmq₂, rfl, hpre₂⟩
  have hneB : preBarSub A ⊥ V hV F₁ ≠ preBarSub A ⊥ V hV F₂ := by
    intro h
    apply hne
    have h' := congrArg (barSub ⊥ V hV) h
    rwa [hbar₁, hbar₂] at h'
  by_cases hcase : preBarSub A ⊥ V hV F₁ = B
  · refine ⟨preBarSub A ⊥ V hV F₂,
      V ⊓ centralizer (preBarSub A ⊥ V hV F₂ : Set G), hHyp₂, ?_⟩
    intro hB₂
    exact hneB (hcase.trans hB₂.symm)
  · exact ⟨preBarSub A ⊥ V hV F₁,
      V ⊓ centralizer (preBarSub A ⊥ V hV F₁ : Set G), hHyp₁, hcase⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
