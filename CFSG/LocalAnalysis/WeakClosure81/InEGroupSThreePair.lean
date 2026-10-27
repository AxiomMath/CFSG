module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.OmegaCollInvColl
import CFSG.LocalAnalysis.WeakClosure81.GenEiConj
import CFSG.LocalAnalysis.WeakClosure81.InCalEOneMembers
import CFSG.LocalAnalysis.WeakClosure81.FiveTenWeak
import CFSG.Quasithin.Background.E6Hyp
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFAppendixIII.Basic

public section

namespace CFSG.LocalAnalysis.WeakClosure81

open CFSG.Quasithin CFSG.Quasithin.A1b CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
  (tA InCalEi genEi IsOmegaColl InEOmega InEGroup)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Bar2)

variable {G : Type} [Group G] [Finite G]

theorem le_genEi_sup_normalizer_of_bar2_perm_three {i : ℕ} {T P : Subgroup G}
    {Ω : Set (Subgroup G)} (hT : IsSylowIn 2 T ⊤) (hΩ : IsOmegaColl Ω) (hi : 1 ≤ i)
    (hTP : T ≤ P) (hP : Nonempty (Bar2 P ≃* Equiv.Perm (Fin 3))) :
    P ≤ genEi i T Ω ⊔ normalizer (E1.weakClosure T Ω : Set G) := by
  by_cases hex : ∃ A ∈ Ω, A ≤ T ∧ ¬ A ≤ pCoreOf 2 P
  · obtain ⟨A, hAΩ, hAT, hAO⟩ := hex
    have hA : IsElemAbelian 2 A := hΩ.elemAbelian A hAΩ
    have hTP' : T ⊓ P = T := inf_eq_left.mpr hTP
    have hτ : tA T A ≤ T ⊓ P := by
      rw [hTP']
      exact E1.tauOf_le ⊤ T A
    have hSyl : IsSylowIn 2 (T ⊓ P) P := by
      rw [hTP']
      exact E6.isSylowIn_of_le hT hTP le_top
    have hK : InCalEi i T A P :=
      inCalEi_of_bar2_mulEquiv_perm_three hAT hA hi hτ hSyl hP hAO
    exact (le_genEi_of_inCalEi hAΩ hAT hK).trans le_sup_left
  · have hno : ∀ A ∈ Ω, A ≤ T → A ≤ pCoreOf 2 P := by
      intro A hA hAT
      by_contra hAO
      exact hex ⟨A, hA, hAT, hAO⟩
    have hOT : pCoreOf 2 P ≤ T :=
      CFSG.Quasithin.pCoreOf_le_of_isSylowIn (E6.isSylowIn_of_le hT hTP le_top)
    have hWO : E1.weakClosure T Ω ≤ pCoreOf 2 P :=
      iSup₂_le fun A hA => iSup_le fun hAT => hno A hA hAT
    have hPle : P ≤ normalizer (E1.weakClosure T Ω : Set G) := by
      intro x hx
      refine mem_normalizer_weakClosure_of_isInvColl hΩ.isInvColl_top (mem_top x)
        fun w hw => hOT ?_
      exact (Subgroup.mem_normalizer_iff.mp
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P hx) w).mp (hWO hw)
    exact hPle.trans le_sup_right

theorem inEOmega_of_sThreePair {i : ℕ} {T P₁ P₂ : Subgroup G} {Ω : Set (Subgroup G)}
    (hT : IsSylowIn 2 T ⊤) (hΩ : IsOmegaColl Ω) (hi : 1 ≤ i) (hTP₁ : T ≤ P₁) (hTP₂ : T ≤ P₂)
    (hsup : P₁ ⊔ P₂ = ⊤) (hP₁ : Nonempty (Bar2 P₁ ≃* Equiv.Perm (Fin 3)))
    (hP₂ : Nonempty (Bar2 P₂ ≃* Equiv.Perm (Fin 3))) : InEOmega i T Ω := by
  have h₁ := le_genEi_sup_normalizer_of_bar2_perm_three hT hΩ hi hTP₁ hP₁
  have h₂ := le_genEi_sup_normalizer_of_bar2_perm_three hT hΩ hi hTP₂ hP₂
  apply top_unique
  rw [← hsup]
  exact sup_le h₁ h₂

theorem inEGroup_of_sThreePair {i : ℕ} (hi : 1 ≤ i)
    (h : ∀ T : Subgroup G, IsSylowIn 2 T ⊤ → ∃ P₁ P₂ : Subgroup G, T ≤ P₁ ∧ T ≤ P₂ ∧
      P₁ ⊔ P₂ = ⊤ ∧ Nonempty (Bar2 P₁ ≃* Equiv.Perm (Fin 3)) ∧
      Nonempty (Bar2 P₂ ≃* Equiv.Perm (Fin 3))) :
    InEGroup i G := by
  intro T hT Ω hΩ
  have hT' : IsSylowIn 2 T ⊤ := CFSG.ABGLocalTools.isSylowOf_iff.mp hT
  obtain ⟨P₁, P₂, hTP₁, hTP₂, hsup, hP₁, hP₂⟩ := h T hT'
  exact inEOmega_of_sThreePair hT' hΩ hi hTP₁ hTP₂ hsup hP₁ hP₂

end CFSG.LocalAnalysis.WeakClosure81
