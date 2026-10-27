module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Model
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherParabolicData
public import CFSG.Open.StatedDefs

import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.RootTransfer
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KAdj.SpParabolic
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.CycNodesStab
import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherSylow
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
public import CFSG.LocalAnalysis.ComponentInitial.SymplecticFlagOrder
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
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.FixBar
import CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.Basic
import CFSG.LinearAlgebra.LinearGroups.ProjectiveSimple
import CFSG.LocalAnalysis.AGLEmbedding.D1GlobalU
import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanParabAutIrrCore
import CFSG.LocalAnalysis.AGLEmbedding.Reduction
import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
import CFSG.LocalAnalysis.ComponentInitial.SymplecticHigherBorel

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open CFSG.Open CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Matrix MatrixGroups

@[expose] noncomputable def spRootAlpha (m : ℕ) (K : Type) [Field K] :
    SL(2, K) →* ↥(StatedSp (m + 2) K) :=
  SymplecticTorusWeyl.rho (0 : Fin (m + 2)) 1 (Fin.zero_ne_one' (n := m + 1))

theorem range_spRootAlpha_le_flagStabilizer (m : ℕ) (K : Type) [Field K] :
    (spRootAlpha m K).range ≤ SymplecticHigher.flagStabilizer (m + 2) K (Set.Icc 2 (m + 2)) :=
  CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.range_rho_le_flagStabilizer
    (fun x hx => (Set.mem_Icc.mp hx).2) (i := (0 : Fin (m + 2))) (j := 1)
    (Fin.zero_ne_one' (n := m + 1)) (by
      intro x hx
      rw [Set.mem_Icc] at hx
      have h0 : ((0 : Fin (m + 2)) : ℕ) = 0 := rfl
      have h1 : ((1 : Fin (m + 2)) : ℕ) = 1 := rfl
      rw [h0, h1]
      constructor <;> intro _ <;> omega)

theorem spRootAlpha_torusSL (m : ℕ) {K : Type} [Field K] (c : Kˣ) :
    spRootAlpha m K (torusSL c) =
      SymplecticTorusWeyl.torusHom (Pi.mulSingle (0 : Fin (m + 2)) c * Pi.mulSingle 1 c⁻¹) := by
  change SymplecticTorusWeyl.rho (0 : Fin (m + 2)) 1 (Fin.zero_ne_one' (n := m + 1))
    (torusSL c) = _
  rw [show torusSL c = SymplecticTorusWeyl.sl2Diag c from rfl]
  exact CFSG.HardMathSupport.Curtis.NaturalModuleCensus.Symplectic.rho_sl2Diag
    (i := (0 : Fin (m + 2))) (j := 1) (Fin.zero_ne_one' (n := m + 1)) c

theorem spRootAlpha_torusSL_mem_normalizer (m : ℕ) {K : Type} [Field K] (c : Kˣ) :
    spRootAlpha m K (torusSL c) ∈
      Subgroup.normalizer (SymplecticFlag.unipotent (m + 2) K : Set ↥(StatedSp (m + 2) K)) := by
  rw [spRootAlpha_torusSL, SymplecticHigher.normalizer_unipotent]
  exact SymplecticFlag.torus_le_borelSubgroup
    (SymplecticTorusWeyl.torusHom_mem_torus
      (Pi.mulSingle (0 : Fin (m + 2)) c * Pi.mulSingle 1 c⁻¹))

theorem spRootAlpha_torusSL_mulVec (m : ℕ) {K : Type} [Field K] (c : Kˣ) :
    (((spRootAlpha m K (torusSL c) : ↥(StatedSp (m + 2) K)) :
        GL (Fin (m + 2) ⊕ Fin (m + 2)) K) :
      Matrix (Fin (m + 2) ⊕ Fin (m + 2)) (Fin (m + 2) ⊕ Fin (m + 2)) K) *ᵥ
        (Pi.single (Sum.inl 0) 1 : Fin (m + 2) ⊕ Fin (m + 2) → K) =
      (c : K) • Pi.single (Sum.inl 0) 1 := by
  rw [spRootAlpha_torusSL, SymplecticTorusWeyl.coe_torusHom]
  funext x
  rw [Matrix.mulVec_diagonal]
  rcases x with x | x
  · by_cases hx : x = 0
    · subst hx
      simp [Pi.mulSingle_apply, Pi.single_apply]
    · simp [Pi.single_apply, Pi.mulSingle_apply, hx]
  · simp [Pi.single_apply, Pi.mulSingle_apply]

theorem hasRootSL2_statedSp (m : ℕ) {K : Type} [Field K] [Finite K] [CharP K 2] :
    HasRootSL2 (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1) := by
  obtain ⟨U₀, hU⟩ := SymplecticFlag.exists_sylow_unipotent (K := K) 2 (m + 2)
  refine hasRootSL2_of_leastParabolic (G := ↥(StatedSp (m + 2) K))
    (MulEquiv.refl ↥(StatedSp (m + 2) K)) U₀
    (SymplecticHigher.flagStabilizer (m + 2) K (Set.Icc 2 (m + 2)))
    (KTabD.lineStab (StatedSp (m + 2) K) (Pi.single (Sum.inl 0) 1))
    (spRootAlpha m K) ?_ ?_ ?_ ?_ ?_
  · exact Subgroup.map_id _
  · rw [hU]
    exact KAdjE.unipotent_le_lineStab m K
  · intro P hP hUP hnot
    exact KAdjE.flagStabilizer_alpha_le_of_parabolic m hP (hU ▸ hUP) hnot
  · exact range_spRootAlpha_le_flagStabilizer m K
  · intro c
    refine ⟨?_, spRootAlpha_torusSL_mulVec m c⟩
    rw [congrArg SetLike.coe hU]
    exact spRootAlpha_torusSL_mem_normalizer m c

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr
