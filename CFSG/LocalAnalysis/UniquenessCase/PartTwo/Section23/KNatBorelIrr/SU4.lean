module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.SU4Root
public import CFSG.Open.StatedDefs

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.RootTransfer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SU4Parabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23d.UnitaryTransport
import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherSylow
import CFSG.ClassicalGroups.UnitaryFlag.StatedBridge
public import CFSG.CGT.Timmesfeld75.Statements
public import CFSG.Foundations
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LBalanceComponentLifts
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.ComponentInitial.LayerComponentOrbit
public import CFSG.LocalAnalysis.SectionRank.EvenCover.Catalog
public import CFSG.LocalAnalysis.SectionRank.LargeRee.SuzukiData
public import CFSG.LocalAnalysis.SectionRank.OddCover.CatalogOdd
public import CFSG.LocalAnalysis.SectionRank.SectionAssemblyBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.J4LocalBase
public import CFSG.LocalAnalysis.SectionRank.Sporadic.MathieuLocalBase
public import CFSG.LocalAnalysis.SectionRank.TitsCover
public import CFSG.Quasithin.Background.A1bGroups
public import CFSG.Quasithin.Background.A3Components
public import CFSG.Quasithin.Background.A3ComponentsAmbient
public import CFSG.Quasithin.Background.Module
public import CFSG.RankThree.PartOne.S10.ThetaContract
public import CFSG.RankThree.PartOne.S12.InputsBase
public import CFSG.Sporadic.J4.Simple
public import CFSG.Sporadic.J4Base
public import CFSG.Sporadic.Mathieu.M12
public import CFSG.Sporadic.Mathieu.M24
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.ComplementTransfer
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.PFchapter1section1.proposition_4_c
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82
public import Certificates.Certificate43
import CFSG.ClassicalGroups.UnitaryFlag.PointSylow
import CFSG.LocalAnalysis.SteinbergSFSingleCommModel3UnitaryGen

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open Matrix CFSG.Open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
  CFSG.Quasithin.H13.U4Par
open CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher (flagStabilizer normalizer_hypUnitriangular)
open scoped MatrixGroups

section Helpers

variable {a : ℕ} {K : Type} [Field K] (h : UnitaryFieldData 2 a K)

theorem su4_sylow_normalizer_eq_hypBorel (U₀ : Sylow 2 ↥(hypSU h 2 0))
    (hU₀ : (U₀ : Subgroup ↥(hypSU h 2 0)) = hypUnitriangular h 2 0) :
    Subgroup.normalizer ((U₀ : Subgroup ↥(hypSU h 2 0)) : Set ↥(hypSU h 2 0)) =
      hypBorel h 2 0 := by
  rw [hU₀]
  exact normalizer_hypUnitriangular h (by norm_num) (by norm_num)

theorem su4_hypTransport_torusSL_mulVec {R : Matrix (Fin (2 * 2 + 0)) (HypIndex 2 0) K}
    (hR : IsHypTransport h R) {e₀ : Fin 4 → K}
    (he : R *ᵥ (Pi.single ie1 1 : HypIndex 2 0 → K) = e₀) (c : Kˣ) :
    (((hypTransport h hR (su4AlphaRoot h (torusSL c)) : StatedSU 4 (2 ^ a) K) : GL (Fin 4) K) :
      Matrix (Fin 4) (Fin 4) K) *ᵥ e₀ = (c : K) • e₀ := by
  refine (hypTransport_mulVec_of_eq h hR (su4AlphaRoot h (torusSL c)) he).trans ?_
  rw [su4AlphaRoot_torusSL_mulVec h c, Matrix.mulVec_smul, he]

end Helpers

theorem hasRootSL2_statedSU {a : ℕ} {K : Type} [Field K] [Finite K]
    (hK : Nat.card K = (2 ^ a) ^ 2) (ha : 1 ≤ a) :
    HasRootSL2 (StatedSU 4 (2 ^ a) K) (Pi.single 0 1 + Pi.single 1 1) := by
  have h : UnitaryFieldData 2 a K := unitaryFieldDataOfCard hK
  haveI : Finite (hypSU h 2 0) := finite_hypSU h
  obtain ⟨R, hR, he⟩ := KTabD.exists_isHypTransport_four h
  obtain ⟨U₀, hU₀⟩ := KAdjE.su4_exists_sylow_hypUnitriangular h
  refine hasRootSL2_of_leastParabolic (hypTransport h hR) U₀ (flagStabilizer h 2 0 {2}) (parP h)
    (su4AlphaRoot h) (KTabD.map_parP_hypTransport_eq_lineStab h hR he) ?_ ?_ ?_ fun c => ⟨?_, ?_⟩
  · rw [hU₀]
    exact KAdjE.su4_hypUnitriangular_le_parP h
  · intro P hP hU hnot
    exact KAdjE.su4_flagStabilizer_two_le_of_parabolic h hP (by rwa [hU₀] at hU) hnot
  · exact su4AlphaRoot_range_le_flagStabilizer h
  · rw [su4_sylow_normalizer_eq_hypBorel h U₀ hU₀]
    exact su4AlphaRoot_torusSL_mem_hypBorel h c
  · exact su4_hypTransport_torusSL_mulVec h hR he c

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr
