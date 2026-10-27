module

import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountTwoLower
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountTwoModel
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountAmbient
import CFSG.LocalAnalysis.UniquenessCase.UC22FunCountCommute
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KGroupProofsA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.TenSix.FunGeneral
import CFSG.LocalAnalysis.ProperTwoGeneratedCore.ComponentNumberRestrictionsFull
import CFSG.CGT.Timmesfeld75.NodeAux
public import CFSG.LocalAnalysis.UniquenessCase.FundamentalLie
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR34Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.ClassicalInvolution.Generic CFSG.ClassicalInvolution.RouteD
open CFSG.LocalAnalysis.UniquenessCase
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
open F14


theorem ncard_funSet_eq_two_of_funTwoType {X : Type} [Group X] [Finite X] [IsSimpleGroup X]
    {t : StatedLieTag} {n p f : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hadm : StatedLieAdmissible t n p f) (hX : CFSG.Blueprint.LieModel X t n p f)
    (htwo : FunTwoType t n) (P : Sylow 2 X) :
    (FunSet (fundPred (p ^ f)) X (P : Subgroup X)).ncard = 2 := by
  have : Fact p.Prime := ⟨hp⟩
  have hfund : IsFundTag t := by cases t <;> simp_all [FunTwoType, IsFundTag]
  obtain ⟨ψ, hψs, hψk⟩ := CFSG.ClassicalInvolution.Upgrade.lieModelCentralCover
    t n p f hp hp2 hfund hadm X hX
  obtain ⟨R, hR, S, hS, hc⟩ := exists_commuting_modelFund_of_funTwoType hp2 hadm htwo
  have hnc : ∃ a b : X, a * b ≠ b * a := by
    rcases CFSG.ClassicalInvolution.ModelFacts.nonempty_equiv_sl2_galoisField_of_mem_fundamentalSubgroups
        hp2 hfund hadm hR with ⟨⟨eR⟩⟩ | ⟨_, ⟨eR⟩⟩
    · obtain ⟨a, _, b, _, hab⟩ := F14.exists_noncommuting_map_of_equiv_sl2 ψ hψk eR
      exact ⟨ψ a, ψ b, hab⟩
    · obtain ⟨a, _, b, _, hab⟩ := F14.exists_noncommuting_map_of_equiv_sl2 ψ hψk eR
      exact ⟨ψ a, ψ b, hab⟩
  have hZ : Subgroup.center X = ⊥ :=
    CFSG.CGT.Timmesfeld75.center_eq_bot_of_simple_nonabelian X hnc
  have hXq := hX.quotient_center hZ
  have hL2 : ¬ IsL2Over17 (X ⧸ Subgroup.center X) (p ^ f) := by
    intro h2
    exact k_LieModelNotL2_holds (X ⧸ Subgroup.center X) t n p f (p ^ f) hp2
      (by
        by_cases ht : t = .PSL
        · subst t; right; change n = 4 ∨ n = 5 at htwo; omega
        · exact Or.inl ht) hadm hXq h2
  have hup : (FunSet (fundPred (p ^ f)) X (P : Subgroup X)).ncard ≤ 2 := by
    apply CFSG.ProperTwoGeneratedCore.ncard_le_two_of_no_three
    intro K₁ h₁ K₂ h₂ K₃ h₃ h12 h13 h23
    have c12 := funSet_commute_of_lieModel hp hp2 ⟨t, n, f, hadm, rfl, hXq⟩ hL2 P h₁ h₂ h12
    have c13 := funSet_commute_of_lieModel hp hp2 ⟨t, n, f, hadm, rfl, hXq⟩ hL2 P h₁ h₃ h13
    have c23 := funSet_commute_of_lieModel hp hp2 ⟨t, n, f, hadm, rfl, hXq⟩ hL2 P h₂ h₃ h23
    obtain ⟨R₁, hR₁, e₁, _⟩ := exists_mem_fundamentalSubgroups_of_mem_funSet
      hp hp2 hadm hX htwo hL2 ψ hψs hψk P h₁
    obtain ⟨R₂, hR₂, e₂, _⟩ := exists_mem_fundamentalSubgroups_of_mem_funSet
      hp hp2 hadm hX htwo hL2 ψ hψs hψk P h₂
    obtain ⟨R₃, hR₃, e₃, _⟩ := exists_mem_fundamentalSubgroups_of_mem_funSet
      hp hp2 hadm hX htwo hL2 ψ hψs hψk P h₃
    have n12 : R₁ ≠ R₂ := fun h => h12 (e₁.trans (by rw [h]; exact e₂.symm))
    have n13 : R₁ ≠ R₃ := fun h => h13 (e₁.trans (by rw [h]; exact e₃.symm))
    have n23 : R₂ ≠ R₃ := fun h => h23 (e₂.trans (by rw [h]; exact e₃.symm))
    have key : ∀ {A B : Subgroup (modelUniv t n p f hp).K},
        A ∈ ModelFund p t n f → ⁅A.map ψ, B.map ψ⁆ = ⊥ → Commutes A B := by
      intro A B hA hAB
      apply commutes_modelFund_of_commutes_map hp2 hfund hadm ψ hψk hA
      intro a ha b hb
      exact (Subgroup.mem_centralizer_iff.mp
        (Subgroup.commutator_eq_bot_iff_le_centralizer.mp hAB ha) b hb).symm
    apply no_three_commuting_modelFund_of_funTwo hp2 hadm htwo hR₁ hR₂ hR₃ n12 n13 n23
    · exact key hR₁ (by rw [← e₁, ← e₂]; exact c12)
    · exact key hR₁ (by rw [← e₁, ← e₃]; exact c13)
    · exact key hR₂ (by rw [← e₂, ← e₃]; exact c23)
  exact le_antisymm hup (two_le_ncard_funSet_of_funTwoType hp hp2 hadm hX htwo P)

end CFSG.LocalAnalysis.UniquenessCase.UC22
