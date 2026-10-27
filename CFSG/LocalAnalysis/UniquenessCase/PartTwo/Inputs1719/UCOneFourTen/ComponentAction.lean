module

public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs3
import CFSG.GroupTheory.LocalCores.ComponentCentralizer
import CFSG.GroupTheory.LocalCores.ComponentRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UCOneFourTen.AlmostSimple
import CFSG.RankThree.PartTwo.Sec4.Census.Item44RankTwo

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

variable {X : Type} [Group X] [Finite X]

theorem exists_component_inner (hKSch : UCK.KSch) (hK : CFSG.Open.IsKGroup X)
    (hp : ∀ p : ℕ, p.Prime → p ≠ 2 → CFSG.Open.pRank p (⊤ : Subgroup X) ≤ 3)
    (hO2 : CFSG.pCore 2 X = ⊥) {L : Subgroup X} {n : ℕ} (hLp : ⁅L, L⁆ = L)
    (hSz : IsSz (Bar2 L) n) (hLO : ⁅L, CFSG.oddCore X⁆ = ⊥) :
    ∃ C : Subgroup X, CFSG.Open.IsQuasisimple ↥C ∧ CFSG.Open.IsSubnormal C ⊤ ∧
      L ≤ normalizer (C : Set X) ∧ (∀ l ∈ L, ∃ c ∈ C, ∀ x ∈ C, l * x * l⁻¹ = c * x * c⁻¹) ∧
      ¬ L ≤ centralizer (C : Set X) := by
  classical
  have hLne : L ≠ ⊥ := ne_bot_of_isSz hSz
  have hnorm : ∀ C : Subgroup X, CFSG.IsComponent C → L ≤ normalizer (C : Set X) :=
    fun C hC => CFSG.LocalCores.perfect_le_normalizer_of_isComponent hLp hp hC
  have hinner : ∀ (C : Subgroup X) (hC : CFSG.IsComponent C),
      ∀ l ∈ L, ∃ c ∈ C, ∀ y ∈ C, l * y * l⁻¹ = c * y * c⁻¹ :=
    fun C hC => CFSG.LocalCores.exists_inner_of_le_normalizer hLp hC
      (hKSch _ hC.1.2.1 ((hK.subgroup C).quotient _)) (hnorm C hC)
  have hex : ∃ C : Subgroup X, CFSG.IsComponent C ∧ ¬ L ≤ centralizer (C : Set X) := by
    by_contra h
    push Not at h
    have hLF : L ≤ centralizer (CFSG.fittingSubgroup X : Set X) :=
      Subgroup.commutator_eq_bot_iff_le_centralizer.mp (le_bot_iff.mp
        ((Subgroup.commutator_mono le_rfl
          (CFSG.RankThree.PartTwo.Sec4.Census.fittingSubgroup_le_oddCore hO2)).trans hLO.le))
    have hFs : L ≤ centralizer (CFSG.generalizedFitting X : Set X) :=
      CFSG.LocalCores.le_centralizer_generalizedFitting hLF h
    have hLs : L ≤ CFSG.generalizedFitting X :=
      hFs.trans (CFSG.centralizer_generalizedFitting_le X)
    have hab : ⁅L, L⁆ = ⊥ := by
      refine Subgroup.commutator_eq_bot_iff_le_centralizer.mpr fun l₁ hl₁ => ?_
      refine Subgroup.mem_centralizer_iff.mpr fun l₂ hl₂ => ?_
      exact Subgroup.mem_centralizer_iff.mp (hFs hl₁) l₂ (hLs hl₂)
    rw [hLp] at hab
    exact hLne hab
  obtain ⟨C, hC, hnc⟩ := hex
  have hCopen := (CFSG.isComponent_iff_open C).mp hC
  exact ⟨C, hCopen.2.2, hCopen.2.1, hnorm C hC, hinner C hC, hnc⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.UC410
