module

public import CFSG.Goldschmidt.Steps.G41
public import CFSG.Goldschmidt.Steps.G310Comp
import CFSG.Goldschmidt.Steps.Red1
import CFSG.Goldschmidt.Steps.G3aGlue
import CFSG.Goldschmidt.Steps.G3aFStar
public import CFSG.Adapters.GeneralizedFitting
public import CFSG.Goldschmidt.Statements
public import CFSG.Goldschmidt.StatementsH
public import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
public import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
public import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
public import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
public import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
public import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
public import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
public import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
public import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
public import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
public import CFSG.LocalAnalysis.RankTwoShapes.AlperinFusion
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_3_3
public import CFSG.Walter.Bender1970.S3.Setup
public import Certificates.Certificate1
public import Certificates.Certificate10
public import Certificates.Certificate100
public import Certificates.Certificate101
public import Certificates.Certificate102
public import Certificates.Certificate103
public import Certificates.Certificate104
public import Certificates.Certificate105
public import Certificates.Certificate106
public import Certificates.Certificate107
public import Certificates.Certificate108
public import Certificates.Certificate109
public import Certificates.Certificate11
public import Certificates.Certificate113
public import Certificates.Certificate12
public import Certificates.Certificate2
public import Certificates.Certificate3
public import Certificates.Certificate4
public import Certificates.Certificate42
public import Certificates.Certificate43
public import Certificates.Certificate44
public import Certificates.Certificate5
public import Certificates.Certificate6
public import Certificates.Certificate7
public import Certificates.Certificate8
public import Certificates.Certificate9
public import Certificates.Certificate96
public import Certificates.Certificate97
public import Certificates.Certificate98
public import Certificates.Certificate99

public section

namespace CFSG.StandardType.FrameRoute.FS81

open CFSG.Open CFSG.Goldschmidt

structure GoldLayerFacts (Y : Type) [Group Y] [Finite Y] (S : Sylow 2 Y) (B : Subgroup Y) :
    Prop where
  hyp : CoreHyp Y S B
  sstar : IsSStarIn (⊤ : Subgroup Y) B
  gen : CFSG.Open.pCore 2 Y ⊔ goldschmidtLayer Y = ⊤
  central : CFSG.Open.pCore 2 Y ≤ Subgroup.center Y
  pCore_le : CFSG.Open.pCore 2 Y ≤ B

theorem goldLayer_normalClosureIn_top {Y : Type} [Group Y] {B : Subgroup Y}
    (h : Subgroup.normalClosure (B : Set Y) = ⊤) : normalClosureIn (⊤ : Subgroup Y) B = ⊤ := by
  have hMeq : normalClosureIn (⊤ : Subgroup Y) B = Subgroup.normalClosure (B : Set Y) := by
    rw [normalClosureIn,
      Subgroup.map_normalClosure _ _ (fun y => ⟨⟨y, Subgroup.mem_top y⟩, rfl⟩)]
    congr 1
    ext y
    constructor
    · rintro ⟨x, hx, rfl⟩
      exact Subgroup.mem_subgroupOf.1 hx
    · intro hy
      exact ⟨⟨y, Subgroup.mem_top y⟩, Subgroup.mem_subgroupOf.2 hy, rfl⟩
  rw [hMeq, h]

theorem goldLayer_pCore_central {Y : Type} [Group Y] [Finite Y] {S : Sylow 2 Y} {B : Subgroup Y}
    (h : CoreHyp Y S B) (hC : CoreConclusion Y S B) :
    CFSG.Open.pCore 2 Y ≤ Subgroup.center Y := by
  have hle : CFSG.Open.pCore 2 Y ≤ B := by
    rw [hC.2.1]
    exact le_sup_left
  exact fun x hx => (N18 Y S B h.le h.comm h.closed h.gen).1 ⟨hle hx, hx⟩

theorem goldLayer_sylow_inf {Y : Type} [Group Y] [Finite Y] {L : Subgroup Y} (P : Sylow 2 Y)
    (hL : L.Normal) : fusionIsSylowIn 2 ((P : Subgroup Y) ⊓ L) L := by
  have : L.Normal := hL
  exact G3a.fusionIsSylowIn_inf ⟨le_top, P.isPGroup', fun Q _ hQ hPQ => P.is_maximal' hQ hPQ⟩
    le_top (inferInstance : (L.subgroupOf (⊤ : Subgroup Y)).Normal).isSubnormal

theorem goldLayer_comp_normal {Y : Type} [Group Y] [Finite Y] {S : Sylow 2 Y} {B L : Subgroup Y}
    (D : GoldLayerFacts Y S B) (hL : IsComponentOf L ⊤) : L.Normal :=
  G3a.component_normal_of_gen D.gen D.central hL

section Certificates


theorem goldLayer_isSStarIn (hcore : CoreStatement) {Y : Type} [Group Y] [Finite Y]
    {S : Sylow 2 Y} {B : Subgroup Y} (h : CoreHyp Y S B) : IsSStarIn (⊤ : Subgroup Y) B := by
  have hIH : IH (Nat.card Y + 1) := fun Z _ _ _ => hcore Z
  have hSyl : fusionIsSylowIn 2 (S : Subgroup Y) ⊤ :=
    ⟨le_top, S.isPGroup', fun P _ hP hSP => S.is_maximal' hP hSP⟩
  have hcl : CFSG.Goldschmidt.IsStronglyClosedIn B (S : Subgroup Y) ⊤ := fun a ha g _ hg =>
    h.closed a ha g hg
  exact G41.isSStarIn_of_lt hIH (by rw [Subgroup.card_top]; exact Nat.lt_succ_self _)
    hSyl h.le h.comm hcl

theorem goldLayer_facts (hcore : CoreStatement) {Y : Type} [Group Y] [Finite Y] {S : Sylow 2 Y}
    {B : Subgroup Y} (h : CoreHyp Y S B) (hC : CoreConclusion Y S B) : GoldLayerFacts Y S B where
  hyp := h
  sstar := goldLayer_isSStarIn hcore h
  gen := hC.1
  central := goldLayer_pCore_central h hC
  pCore_le := by
    rw [hC.2.1]
    exact le_sup_left

end Certificates

end CFSG.StandardType.FrameRoute.FS81

end
