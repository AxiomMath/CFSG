module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.Model
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.OmegaMinusFour
public import CFSG.Open.StatedDefs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.OmegaMinusFourRoot
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KNatBorelIrr.OmegaMinusFourL2
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.KTab23c.SylowLine
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

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr

open CFSG.Open Matrix

section

variable {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}

theorem eq_top_of_normalizer_le_omegaMinusFour (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (U : Sylow 2 ↥(StatedOmega (StatedQuadMinus 2 K b c)))
    (hU : (U : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))) ≤
      KTabD.lineStab (StatedOmega (StatedQuadMinus 2 K b c)) (KTabC.e1M K))
    {P : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))}
    (hP : Subgroup.normalizer ((U : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))) :
      Set ↥(StatedOmega (StatedQuadMinus 2 K b c))) ≤ P)
    (hPl : ¬ P ≤ KTabD.lineStab (StatedOmega (StatedQuadMinus 2 K b c)) (KTabC.e1M K)) :
    P = ⊤ := by
  by_contra hne
  have hUP : (U : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))) ≤ P :=
    le_trans Subgroup.le_normalizer hP
  exact hPl (le_trans (le_normalizer_of_ne_top_omegaMinusFour hirr U hUP hne)
    (normalizer_le_lineStab_omegaMinusFour hirr U hU))

theorem exists_mem_normalizer_mulVec_e1M_omegaMinusFour
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (U : Sylow 2 ↥(StatedOmega (StatedQuadMinus 2 K b c)))
    (hU : (U : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))) ≤
      KTabD.lineStab (StatedOmega (StatedQuadMinus 2 K b c)) (KTabC.e1M K))
    {d : K} (hd : d ≠ 0) :
    ∃ t ∈ Subgroup.normalizer ((U : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))) :
        Set ↥(StatedOmega (StatedQuadMinus 2 K b c))),
      ((t : GL (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) :
          Matrix (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) (Fin (2 - 1) ⊕ Fin (2 - 1) ⊕ Fin 2) K) *ᵥ
        KTabC.e1M K = d • KTabC.e1M K := by
  obtain ⟨t, ht⟩ :=
    exists_mulVec_e1M_eq_smul_omegaMinusFour (b := b) (c := c) (Units.mk0 d hd)
  rw [Units.val_mk0] at ht
  exact ⟨t, lineStab_le_normalizer_omegaMinusFour hirr U hU
    (KTabD.mem_lineStab.mpr ⟨d, ht⟩), ht⟩

theorem borelScalars_omegaMinusFour (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0)
    (U : Sylow 2 ↥(StatedOmega (StatedQuadMinus 2 K b c)))
    (hU : (U : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))) ≤
      KTabD.lineStab (StatedOmega (StatedQuadMinus 2 K b c)) (KTabC.e1M K)) :
    BorelScalars (StatedOmega (StatedQuadMinus 2 K b c))
      (U : Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))) (KTabC.e1M K) := by
  refine borelScalars_of_roots ({⊤} : Set (Subgroup ↥(StatedOmega (StatedQuadMinus 2 K b c))))
    ?_ ?_ ?_
  · rintro X hX
    rw [Set.mem_singleton_iff] at hX
    subst hX
    exact commutator_top_statedOmega_quadMinus_two hirr
  · intro P hNP hnot
    exact ⟨⊤, Set.mem_singleton _,
      (eq_top_of_normalizer_le_omegaMinusFour hirr U hU hNP hnot).ge⟩
  · rintro X hX c hc
    rw [Set.mem_singleton_iff] at hX
    subst hX
    obtain ⟨t, ht, htval⟩ :=
      exists_mem_normalizer_mulVec_e1M_omegaMinusFour hirr U hU (d := c) hc
    exact ⟨t, Subgroup.mem_inf.mpr ⟨Subgroup.mem_top t, ht⟩, htval⟩

end

theorem hasBorelScalars_omegaMinusFour {K : Type} [Field K] [Finite K] [CharP K 2] {b c : K}
    (hirr : ∀ s : K, s ^ 2 + b * s + c ≠ 0) :
    HasBorelScalars (StatedOmega (StatedQuadMinus 2 K b c))
      (Pi.single (Sum.inl ⟨0, by omega⟩) 1) := by
  show HasBorelScalars (StatedOmega (StatedQuadMinus 2 K b c)) (KTabC.e1M K)
  obtain ⟨U, hU⟩ := exists_sylow_le_lineStab (KTabC.sylowFixedLine_minus K b c hirr)
  unfold HasBorelScalars
  exact ⟨U, hU, borelScalars_omegaMinusFour hirr U hU⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22.NatBorelIrr
