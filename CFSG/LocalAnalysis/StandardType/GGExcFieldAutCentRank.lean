module

public import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutDefs
import CFSG.LocalAnalysis.StandardType.GGSixOrderPAutPSLNonsplitGroup
import CFSG.LocalAnalysis.StandardType.GGSixTrialityL613
import CFSG.LocalAnalysis.RankThreeTheoremC.PGroupRankTwoCharSubgroupOf

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank
open CFSG.Open (IsElemAbelian)

section Input

@[expose] def GGExcFieldAutCentRank (t : StatedLieTag) : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (Bs G₀ : Subgroup G) (n f : ℕ)
    (ψ : (ggU t n f).K →* G),
    GGSixFusionSetting p Bs G₀ (ggU t n f).D t n f ψ →
    ∀ y ∈ Subgroup.normalizer (G₀ : Set G), orderOf y = p →
      GGPsiDiagField (ggU t n f).D ψ y → ¬ GGPsiInnerDiag (ggU t n f).D ψ y →
      ∃ E₀ : Subgroup G, E₀ ≤ G₀ ∧ IsElemAbelian p E₀ ∧ (∀ x ∈ E₀, y * x = x * y) ∧
        Nat.card Bs ≤ p * Nat.card E₀

theorem ggOrdPFieldConjAt_of_centRank {t : StatedLieTag} (h : GGExcFieldAutCentRank t) :
    GGOrdPFieldConjAt t := by
  intro G _ _ p Bs G₀ n f ψ hS _ y hyM hyp hdf hni
  obtain ⟨E₀, hE₀G, hE₀, hcomm, hcard⟩ := h G p Bs G₀ n f ψ hS y hyM hyp hdf hni
  have hpp : p.Prime := hS.prime
  haveI : Fact p.Prime := ⟨hpp⟩
  have hyE : y ∉ E₀ := fun hy => hni (ggPsiInnerDiag_of_mem_range _ (by
    rw [hS.presents.2.1.1]
    exact hE₀G hy))
  obtain ⟨hE, hEcard⟩ := CFSG.LocalAnalysis.RankThreeTheoremC.isElemAbelian_sup_zpowers hE₀ hyE
    hyp fun a ha => (hcomm a ha).symm
  have hle : E₀ ⊔ Subgroup.zpowers y ≤ Subgroup.centralizer ({y} : Set G) := by
    refine sup_le ?_ ?_
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      exact hcomm x hx
    · intro x hx
      rw [Subgroup.mem_centralizer_iff]
      intro h hh
      rw [Set.mem_singleton_iff.mp hh]
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
      exact ((Commute.refl y).zpow_right k).eq
  refine OrdPNS.exists_conj_mem_centralizer_of_card hS ?_ hE ?_ ?_
  · exact sup_le (hE₀G.trans Subgroup.le_normalizer) (Subgroup.zpowers_le.mpr hyM)
  · rw [hEcard, mul_comm]
    exact hcard
  · intro x hx
    exact Subgroup.mem_centralizer_iff.mp (hle hx) y (Set.mem_singleton y)

end Input

end CFSG.StandardType
