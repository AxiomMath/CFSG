module

public import CFSG.Quasithin.Background.C1PackSolvBasic
public import CFSG.Quasithin.Background.E2SolvTwo
public import CFSG.Quasithin.Background.A4Reduced
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.ReducedChar
public import CFSG.Quasithin.Background.C1GNBlockLemmas
public import CFSG.Quasithin.Background.C1GNNotation

public section

namespace CFSG.Quasithin.C1Pack

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6

variable {G : Type} [Group G] [Finite G]

theorem not_thompsonJ_baum_le_centralizer {U T M P MP : Subgroup G} (h : MinParabolic U T M)
    (hF : CharTwo U) (hP : MinParabolic P (baum T) MP) (hFP : CharTwo P) (hPT : P ⊔ T = U)
    (hnorm : ¬ P ≤ Subgroup.normalizer (baum T : Set G))
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T U : Set G)) :
    ¬ thompsonJ (baum T) ≤ Subgroup.centralizer (VZ (baum T) P : Set G) := by
  intro hJS
  have hT := h.isSylow
  obtain ⟨-, -, hredU⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
  obtain ⟨-, -, hredP⟩ := conjClosure_isTwoReducedIn_of_charTwo hP.isSylow hFP (le_refl _)
  have hUV : ¬ U ≤ Subgroup.centralizer (VZ T U : Set G) := fun hle =>
    hJ ((thompsonJ_le T).trans (hT.1.trans hle))
  by_cases hPV : P ≤ Subgroup.centralizer (VZ (baum T) P : Set G)
  ·
    have hEV : omegaOneCenterOf (thompsonJ T) ≤ VZ (baum T) P := by
      have h1 : quasithinOmegaOneCenter (baum T) = omegaOneCenterOf (thompsonJ T) := by
        rw [← omegaOneCenterOf_eq]
        exact omegaOneCenterOf_baum T
      show _ ≤ conjClosure (quasithinOmegaOneCenter (baum T)) P
      rw [h1]
      exact le_conjClosure _ _
    have hPE : P ≤ Subgroup.centralizer (omegaOneCenterOf (thompsonJ T) : Set G) :=
      hPV.trans (Subgroup.centralizer_le hEV)
    have hEJ : omegaOneCenterOf (thompsonJ T) ≤ thompsonJ T :=
      (Subgroup.closure_le _).mpr fun x hx => hx.1.1
    have hTE : T ≤ Subgroup.normalizer (omegaOneCenterOf (thompsonJ T) : Set G) :=
      (le_normalizer_thompsonJ T).trans
        (normalizer_le_normalizer_of_characteristic_subgroupOf hEJ
          (CFSG.QuasithinUnique.Setup.characteristic_omegaOneCenterOf (thompsonJ T)))
    have hUE : U ≤ Subgroup.normalizer (omegaOneCenterOf (thompsonJ T) : Set G) := by
      rw [← hPT]
      exact sup_le (hPE.trans (Subgroup.centralizer_le_normalizer _)) hTE
    have hVE : VZ T U ≤ omegaOneCenterOf (thompsonJ T) := by
      refine conjClosure_le fun g hg z hz => ?_
      exact (Subgroup.mem_normalizer_iff.mp (hUE hg) z).mp
        (omegaOneCenterOf_le_omegaOneCenterOf_thompsonJ T hz)
    set N : Subgroup G := U ⊓ Subgroup.centralizer (omegaOneCenterOf (thompsonJ T) : Set G)
      with hN
    have hNn : U ≤ Subgroup.normalizer (N : Set G) := fun g hg =>
      Subgroup.inf_normalizer_le_normalizer_inf ⟨Subgroup.le_normalizer hg,
        le_normalizer_centralizer hUE hg⟩
    have hPN : P ≤ N := le_inf (hPT ▸ le_sup_left) hPE
    have hsup : T ⊔ N = U := le_antisymm (sup_le hT.1 inf_le_left)
      (hPT ▸ sup_le (hPN.trans le_sup_right) le_sup_left)
    have h2 := isTwoQuotient_of_sup_eq hT.2.1 hNn hsup
    have hKN : twoResidual U ≤ N := twoResidual_le_of_isTwoQuotient inf_le_left hNn h2
    exact MinParabolic.not_twoResidual_le_centralizer hredU hUV
      ((hKN.trans inf_le_right).trans (Subgroup.centralizer_le hVE))
  ·
    have htfae := MinParabolic.tfae_thompsonJ hP hredP hPV
    have h1 : ⁅VZ (baum T) P, thompsonJ (baum T)⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hJS
    have h3 : baum (baum T) = baum (pCoreOf 2 P) := (htfae.out 1 3).1 h1
    rw [C1GN.baum_baum] at h3
    apply hnorm
    rw [h3]
    exact (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 P).trans
      (normalizer_le_normalizer_baum _)

theorem exists_minimal_parabolic_over_baum {U T M : Subgroup G} (h : MinParabolic U T M)
    (hF : CharTwo U) (hsolv : Group.IsSolvable ↥U)
    (hSQT : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p U ≤ 2)
    (hJ : ¬ thompsonJ T ≤ Subgroup.centralizer (VZ T U : Set G)) :
    ∃ P : Subgroup G, baum T ≤ P ∧ P ≤ twoResidual U ⊔ baum T ∧ ¬ P ≤ M ∧ P ⊔ T = U ∧
      MinParabolic P (baum T) (P ⊓ M) ∧ CharTwo P ∧
      ¬ thompsonJ (baum T) ≤ Subgroup.centralizer (VZ (baum T) P : Set G) ∧
      IsSylowTwoOf (baum T) (twoResidual U ⊔ baum T) := by
  have hT := h.isSylow
  obtain ⟨hVel, hredU⟩ : IsElemAbelian 2 (VZ T U) ∧ IsTwoReducedIn U (VZ T U) := by
    obtain ⟨-, hel, hred⟩ := conjClosure_isTwoReducedIn_of_charTwo hT hF (le_refl _)
    exact ⟨hel, hred⟩
  obtain ⟨-, -, hSyl, -, -⟩ := E2_3_two_of_isSolvable hVel h hsolv hSQT hredU hJ
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
    not_thompsonJ_baum_le_centralizer h hF hMin hFP hPT hnormP hJ, hSyl⟩

end CFSG.Quasithin.C1Pack
