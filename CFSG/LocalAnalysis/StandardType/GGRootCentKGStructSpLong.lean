module

public import CFSG.LocalAnalysis.StandardType.GGRootCentKGTagsDefs
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerPerfect
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotCentralizerB1
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotQ2Perfect
import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotBlocks
import CFSG.LocalAnalysis.StandardType.GGRootCentKGSummand
import CFSG.LocalAnalysis.StandardType.GGRootCentKGMarking
import CFSG.LocalAnalysis.StandardType.GGRootCentKGSpCent
import CFSG.LocalAnalysis.StandardType.GGSixLayerFactsCoresAlt
public import CFSG.ClassicalInvolution.Models.SymplecticPairs.Quadruple

public section

namespace CFSG.StandardType.KGSp

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21 CFSG.SeitzReduction.SymplecticPilot
open scoped commutatorElement

theorem exists_kgPieces_siegDiag {F : Type} [Field F] [Finite F] [CharP F 2] {f m : ℕ}
    (hF : Nat.card F = 2 ^ f) (hm : 1 ≤ m) {G : Type} [Group G] [Finite G]
    (ψ : StatedSp (m + 3) F →* G) (hψ : Function.Injective ψ) (i : Fin (m + 3))
    {E : Subgroup G}
    (hE : E ≤ ψ.range ⊓ Subgroup.centralizer {ψ (siegDiag F i 1)}) :
    ∃ 𝒥 : Set (Subgroup G),
      (∀ P : Subgroup G, P ≤ ψ.range ⊓ Subgroup.centralizer {ψ (siegDiag F i 1)} →
        ⁅P, P⁆ = P → P ≤ sSup 𝒥) ∧
      ∀ J ∈ 𝒥, GGRCSKGPiece (ψ.range ⊓ Subgroup.centralizer {ψ (siegDiag F i 1)}) E J := by
  classical
  let C₀ : Subgroup G := ψ.range ⊓ Subgroup.centralizer {ψ (siegDiag F i 1)}
  let Q : Subgroup G := (transvRadical F i).map ψ
  let L : Subgroup G := (complSp F i).map ψ
  have h3 : 3 ≤ m + 2 := by omega
  have hC₀ : C₀ = Q ⊔ (L ⊔ ⊥) := by
    show ψ.range ⊓ Subgroup.centralizer {ψ (siegDiag F i 1)} =
      (transvRadical F i).map ψ ⊔ ((complSp F i).map ψ ⊔ ⊥)
    rw [RCSTSp.range_inf_centralizer_of_injective hψ, centralizer_siegDiag_eq_sup,
      Subgroup.map_sup, sup_bot_eq]
  have hQ : pCoreOf 2 C₀ = Q := by
    show pCoreOf 2 (ψ.range ⊓ Subgroup.centralizer {ψ (siegDiag F i 1)}) =
      (transvRadical F i).map ψ
    rw [pCoreOf_range_inf_centralizer hψ,
      pCoreOf_centralizer_siegDiag (m := m + 2) h3 i]
  have hperfC : ⁅Subgroup.centralizer ({siegDiag F i 1} : Set (StatedSp (m + 3) F)),
      Subgroup.centralizer ({siegDiag F i 1} : Set (StatedSp (m + 3) F))⁆ =
      Subgroup.centralizer ({siegDiag F i 1} : Set (StatedSp (m + 3) F)) := by
    rcases LayerCores.card_eq_two_or_four_le (D := F) with h2 | h4
    · exact commutator_centralizer_siegDiag_two h2 (by omega) i
    · exact commutator_centralizer_siegDiag (m := m + 2) h4 (by omega)
  have hmapC : (Subgroup.centralizer ({siegDiag F i 1} : Set (StatedSp (m + 3) F))).map ψ =
      Q ⊔ L := by
    show (Subgroup.centralizer ({siegDiag F i 1} : Set (StatedSp (m + 3) F))).map ψ =
      (transvRadical F i).map ψ ⊔ (complSp F i).map ψ
    rw [centralizer_siegDiag_eq_sup, Subgroup.map_sup]
  have hperf : ⁅Q ⊔ L, Q ⊔ L⁆ = Q ⊔ L := by
    rw [← hmapC, ← Subgroup.map_commutator, hperfC, hmapC]
  have hLQ : L ≤ Subgroup.normalizer (Q : Set G) := by
    show (complSp F i).map ψ ≤ Subgroup.normalizer ((transvRadical F i).map ψ : Set G)
    exact ggRCST_map_le_normalizer ψ complSp_le_normalizer_transvRadical
  have hQL : Q ⊓ L = ⊥ := by
    show (transvRadical F i).map ψ ⊓ (complSp F i).map ψ = ⊥
    exact disjoint_iff.mp (Subgroup.disjoint_map hψ disjoint_transvRadical_complSp)
  have hcentbot : Subgroup.centralizer ((⊥ : Subgroup G) : Set G) = ⊤ := by
    ext x
    simp [Subgroup.mem_centralizer_iff]
  have hLM : L ≤ Subgroup.centralizer ((⊥ : Subgroup G) : Set G) := by
    rw [hcentbot]
    exact le_top
  have hmf : (m + 2, 2 ^ f) ≠ (2, 2) := by
    intro h
    have h1 := congrArg Prod.fst h
    simp only at h1
    omega
  have eL : ↥L ≃* ↥(StatedSp (m + 2) F) :=
    ((complSp F i).equivMapOfInjective ψ hψ).symm.trans
      (complSpEquiv (K := F) (m := m + 2) i).symm
  obtain ⟨hLq, hLm⟩ := isQuasisimple_largeEvenMarking_of_equiv_statedSp hF (by omega) hmf eL
  refine ⟨{Q ⊔ L}, ?_, ?_⟩
  · intro P hP _
    refine hP.trans ?_
    calc C₀ = Q ⊔ (L ⊔ ⊥) := hC₀
      _ = Q ⊔ L := by rw [sup_bot_eq]
      _ ≤ sSup ({Q ⊔ L} : Set (Subgroup G)) := by rw [sSup_singleton]
  · intro J hJ
    rw [Set.mem_singleton_iff] at hJ
    subst hJ
    exact ggRCSKGPiece_of_summand hC₀ hQ hLQ bot_le hLM hQL hperf hLq hLm hE

end CFSG.StandardType.KGSp

end
