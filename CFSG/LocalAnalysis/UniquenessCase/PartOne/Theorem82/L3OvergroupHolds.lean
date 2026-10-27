module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.KInputL3Overgroup
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.L3OvSL2Two
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.L3OvEvenMatrix
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.L3OvEvenTransport
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82.L3OvContra
import CFSG.LocalAnalysis.EvenBN.GMSK.U3Perfect
import CFSG.ClassicalGroups.PCoreSection
import CFSG.LargeExtraspecial.S63AJ2CentAbs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82

open CFSG.LocalAnalysis.EvenBN.GMSK (eq_bot_of_isPerfect_of_le_normalizer_of_lieModel_PSU3)

theorem l3Overgroup_holds : L3Overgroup := by
  intro X _ _ hX Z Y K hZ hZY hYK hKK hZK hcomm
  have hQ : CFSG.Open.pCoreOf 2 K ≠ ⊥ := by
    intro h
    exact hcomm (by rw [h]; exact Subgroup.commutator_bot_left Z)
  have hodd : ∀ {ℓ f : ℕ}, ℓ ≠ 2 →
      (CFSG.Blueprint.LieModel X .PSL 3 ℓ f ∨ CFSG.Blueprint.LieModel X .PSU 3 ℓ f) → False := by
    intro ℓ f hℓ hL
    have hc := pCoreOf_two_commute_of_lieModel_odd hℓ hL hKK
    refine hcomm ((Subgroup.commutator_eq_bot_iff_le_centralizer).mpr fun a ha => ?_)
    exact Subgroup.mem_centralizer_iff.mpr fun z hz => (hc a ha z (hZK hz)).symm
  rcases hX with ⟨ℓ, f, hmod, hL⟩ | ⟨ℓ, f, -, hL⟩
  · by_cases hℓ : ℓ = 2
    · subst hℓ
      exact l3Overgroup_psl_two (l3OvMatrix_of_dickson l3OvDickson_holds) hL hmod hZ hZY hYK hKK
        hZK hQ
    · exact (hodd hℓ (Or.inl hL)).elim
  · by_cases hℓ : ℓ = 2
    · subst hℓ
      have hK1 := eq_bot_of_isPerfect_of_le_normalizer_of_lieModel_PSU3
        hL (CFSG.ClassicalGroups.PCoreSection.isPGroup_pCoreOf 2 K) hQ
        (CFSG.LargeExtraspecial.S63.isPerfect_of_commutator_eq hKK)
        (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 K)
      have hZ1 : Nat.card Z = 1 := by
        rw [Subgroup.card_eq_one, eq_bot_iff]
        exact hZK.trans hK1.le
      omega
    · exact (hodd hℓ (Or.inr hL)).elim

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82
