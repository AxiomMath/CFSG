module

public import CFSG.Timmesfeld.ARS.CaseHFinal
public import CFSG.Timmesfeld.ARS.LinearMain
public import CFSG.Timmesfeld.ARS.CaseHConnected
public import CFSG.Timmesfeld.ARS.CaseHU33

public section

namespace CFSG.Timmesfeld.CorB

open CFSG.Timmesfeld.ARS CFSG.LieType CFSG.LieType.Steinberg CFSG.Blueprint

variable {G : Type} [Group G] {R : Set (Subgroup G)}

@[expose] def NoOppCentral (R : Set (Subgroup G)) : Prop :=
  ∀ A ∈ R, ∀ B ∈ centralSet R A, ∀ C ∈ centralSet R A, ¬ Opposite B C

@[expose] def ARSOutcomeTwo (G : Type) [Group G] (R : Set (Subgroup G)) : Prop :=
  (∃ f : ℕ, 1 ≤ f ∧ (∃ A ∈ R, Nat.card A = 2 ^ f) ∧ LieModel G .PSL 3 2 f) ∨
  (∃ f : ℕ, 2 ≤ f ∧ (∃ A ∈ R, Nat.card A = 2 ^ f) ∧ LieModel G .G2 0 2 f) ∨
  (∃ f : ℕ, 1 ≤ f ∧ (∃ A ∈ R, Nat.card A = 2 ^ f) ∧ LieModel G .trialityD4 0 2 f) ∨
  LieModel G .PSU 3 3 1

theorem sigmaSet_eq_lambdaSet (h : ARS.Hyp G R) (hno : NoOppCentral R) {A : Subgroup G}
    (hA : A ∈ R) : sigmaSet R A = lambdaSet R A := by
  have := h.finite
  refine Set.Subset.antisymm (fun B hBs => ?_) (fun B hB => hB.1)
  by_contra hBl
  have hBR : B ∈ R := hBs.1
  have hAI : A ∉ isolatedSet R B := by
    intro hI
    have hmem : A ∈ {X | X ∈ R ∧ X ≤ M R B} := ⟨hA, (Q_eq_M h hBR).1 ▸ QD.le_Q hI⟩
    rw [(Q_eq_M h hBR).2.1] at hmem
    rcases hmem with h1 | h1
    · exact hBs.2.1 h1.symm
    · exact hBl (mem_lambdaSet_comm hBR h1)
  obtain ⟨C, hCc, hAC⟩ := QD.exists_opposite_of_notMem_isolatedSet ⟨hA, hBs.2.2.symm⟩ hAI
  exact hno B hBR A ⟨hA, hBs.2.2.symm⟩ C hCc hAC

theorem outcomeTwo_caseL (h : ARS.Hyp G R) (hno : NoOppCentral R) {A : Subgroup G} (hA : A ∈ R)
    (hmax : ¬ IsCoatom (Subgroup.normalizer (A : Set G))) : ARSOutcomeTwo G R := by
  have := h.finite
  have hR := h.root
  have hiso := h.noIsolated
  have hnd := h.nondeg
  have hΩ : ∀ A ∈ R, ∀ B ∈ R, omegaSet R B = omegaSet R A → B = A :=
    fun _ hA _ hB e => eq_of_omegaSet_eq h hA hB e
  obtain ⟨Δ, hΔ, hAΔ⟩ := (exists_isTI_iff h hA).1 hmax
  obtain ⟨m, hm⟩ := Sec5.exists_card_gen_eq_pow hR hiso hnd hΩ hΔ.isWeakTI hAΔ
  obtain ⟨hm2, X, hX⟩ := Linear.exists_isRootFrame hR hiso hnd hΩ hΔ hAΔ hm
  have hm3 : m = 2 := by
    by_contra hm3
    have i0 : (⟨0, by omega⟩ : Fin (m + 1)) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
    have i1 : (⟨1, by omega⟩ : Fin (m + 1)) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
    have i2 : (⟨0, by omega⟩ : Fin (m + 1)) ≠ ⟨2, by omega⟩ := by simp [Fin.ext_iff]
    have i3 : (⟨1, by omega⟩ : Fin (m + 1)) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
    have i4 : (⟨0, by omega⟩ : Fin (m + 1)) ≠ ⟨1, by omega⟩ := by simp [Fin.ext_iff]
    have i5 : (⟨2, by omega⟩ : Fin (m + 1)) ≠ ⟨3, by omega⟩ := by simp [Fin.ext_iff]
    exact hno _ (hX.mem _ _ i0) _ ⟨hX.mem _ _ i1, hX.commuting _ _ _ _ i0 i1 i2 i3⟩ _
      ⟨hX.mem _ _ i1.symm, hX.commuting _ _ _ _ i0 i1.symm i4 i5⟩ (hX.opposite _ _ i1)
  subst hm3
  obtain ⟨f, hf, hcard, hL⟩ := hX.lieModel hR hiso h.center hm2
  exact Or.inl ⟨f, hf, ⟨A, hA, hcard A hA⟩, hL⟩

theorem outcomeTwo_caseH (h : ARS.Hyp G R) {A : Subgroup G} (hA : A ∈ R)
    (hmax : IsCoatom (Subgroup.normalizer (A : Set G))) (hσ : sigmaSet R A = lambdaSet R A) :
    ARSOutcomeTwo G R := by
  have hH : SigmaEqLambda R := sigmaEqLambda_of_mem h.root hA hσ
  have h3 := CaseH.three_le_ncard_linesThrough h hH hA hmax
  by_cases h23 : Nat.card A = 2 ∧ (linesThrough R A).ncard = 3
  · exact Or.inr (Or.inr (Or.inr (lieModel_PSU_of_caseH h hH hA h23.1 h23.2)))
  · have hT := CaseH.mTransitive_of_not_two_three h hH hA h3 h23
    rcases caseHFrameInput G R h hH hT A hA h3 h23 with ⟨f, hf, hAf, hG⟩ | ⟨f, hf, hAf, hG⟩
    · obtain ⟨F, _, _, hF, φ, hc, hgen, hnt⟩ := hG
      have hq : 3 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
      obtain ⟨-, -, -, -, hmodel⟩ :=
        exists_lieModel_of_coneCompatible_G2 Nat.prime_two (by omega) hq hF h.center hc hgen hnt
      exact Or.inr (Or.inl ⟨f, hf, ⟨A, hA, hAf⟩, hmodel⟩)
    · obtain ⟨F, _, _, hF, σ, hσ', φ, hc, hgen, hnt⟩ := hG
      obtain ⟨-, -, -, -, hmodel⟩ :=
        exists_lieModel_of_coneCompatible_twistedD4 Nat.prime_two hf hF σ hσ' h.center hc hgen hnt
      exact Or.inr (Or.inr (Or.inl ⟨f, hf, ⟨A, hA, hAf⟩, hmodel⟩))

theorem outcomeTwo_of_noOppCentral (h : ARS.Hyp G R) (hno : NoOppCentral R) :
    ARSOutcomeTwo G R := by
  obtain ⟨A, hA, -⟩ := h.nondeg
  by_cases hmax : IsCoatom (Subgroup.normalizer (A : Set G))
  · exact outcomeTwo_caseH h hA hmax (sigmaSet_eq_lambdaSet h hno hA)
  · exact outcomeTwo_caseL h hno hA hmax

end CFSG.Timmesfeld.CorB
