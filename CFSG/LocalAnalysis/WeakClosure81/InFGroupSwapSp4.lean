module

public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4Y1
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4CaseJ
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4CaseX
public import CFSG.LocalAnalysis.WeakClosure81.InFGroupSwapSp4CaseW
public import CFSG.LocalAnalysis.WeakClosure81.GF2RepsAsch5Bridge

public section

namespace CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Setting

open Subgroup CFSG.Open CFSG.Quasithin
open CFSG.LocalAnalysis.UniquenessCase.PartTwo (InCalEi IsOmegaColl)
open CFSG.LocalAnalysis.UniquenessCase.UC22.F12 (eGenP)
open scoped commutatorElement

variable {Q : Type} [Group Q] [Finite Q] {L T P₀ P₁ : Subgroup Q} {n : ℕ}
  {F : Type} [Field F] [Finite F] {w : F × F → Q}

private theorem top_not_le_normalizer_inf (h : Setting L T P₀ P₁ n w) :
    ¬ (⊤ : Subgroup Q) ≤ normalizer ((T ⊓ L : Subgroup Q) : Set Q) := by
  intro htop
  have hnormal : (T ⊓ L : Subgroup Q).Normal :=
    Subgroup.normalizer_eq_top_iff.mp (top_le_iff.mp htop)
  have hnormU : (⊤ : Subgroup Q) ≤ normalizer ((T ⊓ L : Subgroup Q) : Set Q) :=
    le_of_eq (Subgroup.normalizer_eq_top_iff.mpr hnormal).symm
  have h2 : IsPGroup 2 (T ⊓ L : Subgroup Q) := h.sylow.isPGroup.to_inf_left
  have hle : T ⊓ L ≤ pCoreOf 2 (⊤ : Subgroup Q) :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 le_top hnormU h2
  exact h.inf_ne_bot (le_bot_iff.mp (hle.trans (le_of_eq h.pCoreOf_top_eq_bot)))

private theorem exists_inCalEi_of_large_no_swap (h : Setting L T P₀ P₁ n w)
    {Ω : Set (Subgroup Q)} (hΩ : IsOmegaColl Ω)
    (hlarge : ∀ A ∈ Ω, A ≤ T → 2 ^ n < Nat.card ↥A)
    (hstab : ∀ A ∈ Ω, A ≤ T → ∀ a ∈ A, P₀.map (MulAut.conj a).toMonoidHom = P₀) :
    ∃ A ∈ Ω, A ≤ T ∧ ∃ K : Subgroup Q, InCalEi n T A K ∧
      ¬ K ≤ normalizer ((T ⊓ L : Subgroup Q) : Set Q) := by
  classical
  have hY : ∀ A ∈ Ω, A ≤ T → ∀ t ∈ T,
      (∀ a ∈ A, t * a = a * t) → P₀.map (MulAut.conj t).toMonoidHom = P₀ := by
    intro A hAΩ hAT t ht htA
    exact stab_of_commute h hAT (hΩ.elemAbelian A hAΩ) (hstab A hAΩ hAT)
      (hlarge A hAΩ hAT) ht htA
  by_cases hex : ∃ A ∈ Ω, A ≤ T ∧
      (¬ ⁅A, perfectCore P₀⁆ ≤ pCoreOf 2 (perfectCore P₀) ∨
        ¬ ⁅A, perfectCore P₁⁆ ≤ pCoreOf 2 (perfectCore P₁))
  · obtain ⟨A, hAΩ, hAT, hc⟩ := hex
    rcases hc with hc | hc
    · exact ⟨A, hAΩ, hAT, exists_inCalEi_of_not_commutator_le h hAT
        (hΩ.elemAbelian A hAΩ) (hY A hAΩ hAT) (Or.inl rfl) hc⟩
    · exact ⟨A, hAΩ, hAT, exists_inCalEi_of_not_commutator_le h hAT
        (hΩ.elemAbelian A hAΩ) (hY A hAΩ hAT) (Or.inr rfl) hc⟩
  · exfalso
    refine false_of_forall_commutator_le h hΩ ?_
    intro A hAΩ hAT
    refine ⟨?_, ?_⟩
    · by_contra hc
      exact hex ⟨A, hAΩ, hAT, Or.inl hc⟩
    · by_contra hc
      exact hex ⟨A, hAΩ, hAT, Or.inr hc⟩

theorem exists_inCalEi (h : Setting L T P₀ P₁ n w) {Ω : Set (Subgroup Q)}
    (hΩ : IsOmegaColl Ω) :
    ∃ A ∈ Ω, A ≤ T ∧ ∃ K : Subgroup Q, InCalEi n T A K ∧
      ¬ K ≤ normalizer ((T ⊓ L : Subgroup Q) : Set Q) := by
  classical
  by_cases hsmall : ∃ A ∈ Ω, A ≤ T ∧ Nat.card ↥A ≤ 2 ^ n
  · obtain ⟨A, hAΩ, hAT, hcard⟩ := hsmall
    refine ⟨A, hAΩ, hAT, ⊤, ?_, top_not_le_normalizer_inf h⟩
    exact inCalEi_top_of_almostSimple h.almostSimple h.sylow (hΩ.ne_bot A hAΩ)
      (mQuot_pCoreOf_top_le_of_card_le h.almostSimple (hΩ.elemAbelian A hAΩ).isPGroup hcard)
  · by_cases hswap : ∃ A ∈ Ω, A ≤ T ∧ 2 ^ n < Nat.card ↥A ∧
        ∃ a ∈ A, P₀.map (MulAut.conj a).toMonoidHom ≠ P₀
    · obtain ⟨A, hAΩ, hAT, hcard, hAS⟩ := hswap
      exact exists_inCalEi_of_not_stab h hΩ hAΩ hAT hcard hAS
    · have hlarge : ∀ A ∈ Ω, A ≤ T → 2 ^ n < Nat.card ↥A := by
        intro A hAΩ hAT
        by_contra hle
        exact hsmall ⟨A, hAΩ, hAT, Nat.le_of_not_lt hle⟩
      have hstab : ∀ A ∈ Ω, A ≤ T → ∀ a ∈ A,
          P₀.map (MulAut.conj a).toMonoidHom = P₀ := by
        intro A hAΩ hAT a ha
        by_contra hne
        exact hswap ⟨A, hAΩ, hAT, hlarge A hAΩ hAT, a, ha, hne⟩
      exact exists_inCalEi_of_large_no_swap h hΩ hlarge hstab

theorem inFFor (h : Setting L T P₀ P₁ n w) :
    CFSG.LocalAnalysis.UniquenessCase.UC22.F12.InFFor n (⊤ : Subgroup Q) T := by
  intro Ω hΩ hne hbot
  have hΩ' : IsOmegaColl Ω := isOmegaColl_of_isInvColl_top hΩ hne hbot
  obtain ⟨A, hAΩ, hAT, K, hK, hKnot⟩ := exists_inCalEi h hΩ'
  have hEP : CFSG.LocalAnalysis.UniquenessCase.UC22.F12.IsEP n ⊤ T A K :=
    isEP_of_inCalEi hAT (hΩ'.elemAbelian A hAΩ) hK
  have hKE : K ≤ eGenP n ⊤ T Ω :=
    le_iSup₂_of_le A hAΩ (le_iSup_of_le hAT (le_iSup₂_of_le K hEP le_rfl))
  have hEN : T ≤ normalizer ((eGenP n ⊤ T Ω : Subgroup Q) : Set Q) :=
    le_normalizer_eGenP n hΩ
  have htop : eGenP n ⊤ T Ω ⊔ T = ⊤ := by
    rcases eq_top_or_le_normalizer h
      (le_sup_right : T ≤ eGenP n ⊤ T Ω ⊔ T) with htop | hle
    · exact htop
    · exact absurd (hKE.trans (le_sup_left.trans hle)) hKnot
  rw [← Subgroup.coe_mul_of_right_le_normalizer_left (eGenP n ⊤ T Ω) T hEN, htop]

end CFSG.LocalAnalysis.WeakClosure81.SwapSp4.Setting
