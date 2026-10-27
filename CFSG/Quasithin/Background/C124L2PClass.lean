module

public import CFSG.Quasithin.Background.C124L2PGlaub
public import CFSG.Quasithin.Background.C126NatClassG
public import CFSG.Quasithin.Background.A4Reduced
public import CFSG.Quasithin.Background.C1GNNotation

set_option linter.unusedSectionVars false

public section

namespace CFSG.Quasithin.C124.L2P

open CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin CFSG.Quasithin.B6 CFSG.LieType.BorelTits
  CFSG.Quasithin.C126.A5 E2
open CFSG.Quasithin.C124.L2 (R₂)
open scoped MatrixGroups

variable {G : Type} [Group G] [Finite G]

namespace Setup

variable {X R Y V : Subgroup G} {hV : IsElemAbelian 2 V} (s : Setup X R Y V hV)

include s

theorem P₃_le_normalizer : Y ⊔ baum R ≤ Subgroup.normalizer (Y : Set G) :=
  sup_le Subgroup.le_normalizer s.S_norm

theorem P₃_le_P₁ : Y ⊔ baum R ≤ Y ⊔ R₂ X R Y := sup_le_sup_left s.S_le_R₂ Y

theorem charTwo_P₃ : CharTwo (Y ⊔ baum R) := by
  have hY : CharTwo Y := A4.charTwo_of_normal (le_sup_left : Y ≤ Y ⊔ R₂ X R Y)
    (fun g hg => sup_le Subgroup.le_normalizer s.R₂_le_normalizer hg) s.charTwo_P₁
  exact A4.charTwo_sup hY s.S_norm (s.R_pGroup.to_le s.S_le_R)

theorem sqtk_P₃ : IsSQTKTC (Y ⊔ baum R) :=
  C1GN.IsSQTKTC.mono (sup_le s.Y_le s.S_le_X) s.sqtk

theorem twoResidual_P₃ : twoResidual (Y ⊔ baum R) = Y := by
  refine le_antisymm (twoResidual_le_of_isTwoQuotient le_sup_left s.P₃_le_normalizer
    (isTwoQuotient_of_sup_eq (s.R_pGroup.to_le s.S_le_R) s.P₃_le_normalizer (sup_comm _ _))) ?_
  have := twoResidual_mono (le_sup_left : Y ≤ Y ⊔ baum R)
  rwa [s.Y_res] at this

theorem hJ_S (hE23 : E2.E23Statement) (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) :
    ¬ thompsonJ (baum R) ≤ Subgroup.centralizer (VZ (baum R) (Y ⊔ baum R) : Set G) := by
  intro hJS
  obtain ⟨M, hM⟩ := s.minParabolic_P₃ hE23 hYS
  obtain ⟨-, -, hredP⟩ := conjClosure_isTwoReducedIn_of_charTwo hM.isSylow s.charTwo_P₃
    (Z := quasithinOmegaOneCenter (baum R)) le_rfl
  by_cases hPV : Y ⊔ baum R ≤ Subgroup.centralizer (VZ (baum R) (Y ⊔ baum R) : Set G)
  · apply s.Y_not_C
    have hZV : quasithinOmegaOneCenter (baum R) ≤ VZ (baum R) (Y ⊔ baum R) :=
      le_conjClosure _ _
    exact le_sup_left.trans (hPV.trans (Subgroup.centralizer_le hZV))
  · have htfae := MinParabolic.tfae_thompsonJ hM hredP hPV
    have h1 : ⁅VZ (baum R) (Y ⊔ baum R), thompsonJ (baum R)⁆ = ⊥ := by
      rw [Subgroup.commutator_comm, Subgroup.commutator_eq_bot_iff_le_centralizer]
      exact hJS
    have h3 : baum (baum R) = baum (pCoreOf 2 (Y ⊔ baum R)) := (htfae.out 1 3).1 h1
    rw [C1GN.baum_baum] at h3
    apply hYS
    have hh := (le_normalizer_pCoreOf 2 (Y ⊔ baum R)).trans
      (normalizer_le_normalizer_baum (pCoreOf 2 (Y ⊔ baum R)))
    rw [← h3] at hh
    exact le_sup_left.trans hh

theorem inClassG_P₃ (hE23 : E2.E23Statement) (hYS : ¬ Y ≤ Subgroup.normalizer (baum R : Set G)) :
    InClassG (Y ⊔ baum R) (baum R) := by
  obtain ⟨M, hM⟩ := s.minParabolic_P₃ hE23 hYS
  exact C126.Nat.inClassG_of_e23 hE23 hM s.charTwo_P₃ s.sqtk_P₃ (C1GN.baum_baum R)
    (s.hJ_S hE23 hYS)

theorem R_ne_bot : R ≠ ⊥ := by
  intro hR
  apply s.hJ
  exact (B6.thompsonJ_le R).trans (hR ▸ bot_le)

theorem dichotomy_all (hE23 : E2.E23Statement) {C₁ C₂ : Subgroup G → Subgroup G}
    (hC : IsGNChoice C₁ C₂) :
    Y ≤ Subgroup.centralizer (C₁ (baum R) : Set G) ∨
      Y ≤ Subgroup.normalizer (C₂ (baum R) : Set G) ∨
      (IsBlock2 (Y ⊔ baum R) Y ∧ ((∃ n : ℕ, 1 < n ∧ IsLin2Type Y n) ∨ IsAltType Y 3)) := by
  have hSp : IsPGroup 2 (baum R) := s.R_pGroup.to_le s.S_le_R
  have hS0 : baum R ≠ ⊥ := C1GN.baum_ne_bot s.R_pGroup s.R_ne_bot
  obtain ⟨-, h1Z, -, -, h2B, h2char, -⟩ := hC.pair (baum R) hSp hS0
  rw [C1GN.baum_baum] at h2B h2char
  by_cases hYS : Y ≤ Subgroup.normalizer (baum R : Set G)
  · right; left
    exact hYS.trans (normalizer_le_normalizer_of_characteristic_subgroupOf h2B h2char)
  · have hcls : InClassG (Y ⊔ baum R) (baum (baum R)) := by
      rw [C1GN.baum_baum]
      exact s.inClassG_P₃ hE23 hYS
    rcases hC.dichotomy hSp hS0 hcls with h | h | h
    · left
      intro y hy
      refine Subgroup.mem_centralizer_iff.2 fun c hc => ?_
      exact (Subgroup.mem_centralizer_iff.1 (h hc).2 y (Subgroup.mem_sup_left hy)).symm
    · right; left
      exact le_sup_left.trans h
    · right; right
      rw [s.twoResidual_P₃] at h
      exact h

end Setup

end CFSG.Quasithin.C124.L2P
