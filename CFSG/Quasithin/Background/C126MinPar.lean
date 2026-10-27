module

public import CFSG.Quasithin.Background.C1PackSolvP

public section

namespace CFSG.Quasithin.C126

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 CFSG.Quasithin.C1Pack

variable {G : Type} [Group G] [Finite G]

theorem exists_minimal_parabolic_over_baum {U T M : Subgroup G} (h : MinParabolic U T M)
    (hF : CharTwo U) (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T U : Set G))
    (hSyl : IsSylowTwoOf (baum T) (twoResidual U ⊔ baum T)) :
    ∃ P : Subgroup G, baum T ≤ P ∧ P ≤ twoResidual U ⊔ baum T ∧ ¬ P ≤ M ∧ P ⊔ T = U ∧
      MinParabolic P (baum T) (P ⊓ M) ∧ CharTwo P ∧
      ¬ thompsonJ (baum T) ≤ Subgroup.centralizer (VZ (baum T) P : Set G) := by
  have hT := h.isSylow
  obtain ⟨-, -, hredU⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
  have hST : baum T ≤ T := inf_le_left
  have hKU : twoResidual U ≤ U := twoResidual_le U
  have hKN : U ≤ Subgroup.normalizer (twoResidual U : Set G) := le_normalizer_twoResidual U
  have hTS : T ≤ Subgroup.normalizer (baum T : Set G) :=
    Subgroup.le_normalizer.trans (normalizer_le_normalizer_baum T)
  have hSK : baum T ≤ Subgroup.normalizer (twoResidual U : Set G) := hST.trans (hT.1.trans hKN)
  have hY : ¬ twoResidual U ⊔ baum T ≤ M := by
    intro hle
    have hUM : U ≤ M := by
      rw [← sup_twoResidual_eq hT]
      exact sup_le h.le (le_sup_left.trans hle)
    exact absurd (lt_of_le_of_lt hUM h.maximal.1) (lt_irrefl _)
  obtain ⟨P, hSP, hPY, hPM, hmin⟩ := exists_minimal_not_le (S := baum T)
    (Y := twoResidual U ⊔ baum T) (M := M) le_sup_right hY
  have hsylP : IsSylowTwoOf (baum T) P := isSylowTwoOf_mono hSyl hSP hPY
  have hPU : P ≤ U := hPY.trans (sup_le hKU (hST.trans hT.1))
  have hnormP : ¬ P ≤ Subgroup.normalizer (baum T : Set G) := by
    intro hPN
    have hUS : ¬ U ≤ Subgroup.normalizer (baum T : Set G) := by
      intro hUN
      have hSO : baum T ≤ pCoreOf 2 U :=
        CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 (hST.trans hT.1) hUN
          (hT.2.1.to_le hST)
      exact hJ ((B6.thompsonJ_le_baum T).trans
        (hSO.trans (MinParabolic.pCoreOf_le_centralizer hredU)))
    have hlt : U ⊓ Subgroup.normalizer (baum T : Set G) < U :=
      lt_of_le_of_ne inf_le_left fun he => hUS (he ▸ inf_le_right)
    have hMN : U ⊓ Subgroup.normalizer (baum T : Set G) ≤ M :=
      h.le_of_lt (le_inf hT.1 hTS) hlt
    exact hPM ((le_inf hPU hPN).trans hMN)
  have hMin : MinParabolic P (baum T) (P ⊓ M) :=
    minParabolic_of_minimal hsylP (hST.trans h.le) hPM hmin hnormP
  have hPT : P ⊔ T = U :=
    h.eq_of_not_le le_sup_right (sup_le hPU hT.1) fun hle => hPM (le_sup_left.trans hle)
  have hFK : CharTwo (twoResidual U) := A4.charTwo_of_normal hKU hKN hF
  have hFY : CharTwo (twoResidual U ⊔ baum T) := A4.charTwo_sup hFK hSK (hT.2.1.to_le hST)
  have hFP : CharTwo P := C1GN.charTwo_of_le hFY hSyl hSP hPY
  exact ⟨P, hSP, hPY, hPM, hPT, hMin, hFP,
    C1Pack.not_thompsonJ_baum_le_centralizer h hF hMin hFP hPT hnormP hJ⟩

end CFSG.Quasithin.C126
