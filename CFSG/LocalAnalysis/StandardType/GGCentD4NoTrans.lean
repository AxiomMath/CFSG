module

public import CFSG.HardMathSupport.Lang.D4Three.NormalForm
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitzD4
public import CFSG.LieType.Chevalley.TwistMap
public import CFSG.LieType.Chevalley.GraphFixedData
public import CFSG.LieType.Chevalley.ExactNormalFormE
public import CFSG.Certificates.CentralKernel
public import CFSG.Certificates.CosetTableWalkC
public import CFSG.Certificates.FusionF2
public import CFSG.Certificates.WordSubgroupHom
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.Coordinator.Cover
public import CFSG.HardMathSupport.Seitz.G2Anisotropic.ExceptionsTransport.FamilyProved
public import CFSG.HardMathSupport.Seitz.G2Noninner.Descent.OddNeThree
public import CFSG.HardMathSupport.Seitz.G2Noninner.SubfieldPair.Final
public import CFSG.LieType.SeitzGeneration.ExcOuterAssemblyV5
public import CFSG.LieType.SeitzGeneration.OmegaF2.Basic
public import CFSG.LieType.SeitzGeneration.OuterSpPair
public import CFSG.LieType.SeitzGeneration.RootPairOrthBlock
public import CFSG.LieType.SeitzGeneration.RootPairSp
public import CFSG.LocalAnalysis.AGLEmbedding.CaseThreeA3pSurvivor
public import CFSG.LocalAnalysis.AGLEmbedding.GapROneBS
public import CFSG.LocalAnalysis.AGLEmbedding.J3InSitu
public import CFSG.LocalAnalysis.AGLEmbedding.J3MSide
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3CoverGenAssembly
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSL3FourGenData
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSeitzCyc
public import CFSG.LocalAnalysis.AGLEmbedding.MonomialWeightsOne
public import CFSG.LocalAnalysis.AGLEmbedding.ReeData
public import CFSG.LocalAnalysis.AGLEmbedding.SurvivorTransfer
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X6G2
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1Frontier3
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotXiCaseLTorus
public import CFSG.Monster.GMS.Fi23Gen
public import CFSG.Monster.GMS.Fi23GenIso
public import CFSG.Monster.GMS.Fi23GenSix
public import CFSG.Monster.GMS.LeechCoh
public import CFSG.Monster.GMS.LeechCohGroup
public import CFSG.Monster.GMS.S365Center
public import CFSG.Monster.GMS.S37
public import CFSG.Monster.GMS.S4Assembly
public import CFSG.Monster.GMS.S4CohB
public import CFSG.Monster.GMS.S5Inputs
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsBorLie
public import CFSG.Quasithin.Vol2.GoldschmidtSec53FactsThree
public import CFSG.RankThree.PartOne.Census3.Assembly
public import CFSG.RankThree.PartOne.FOC.Cases
public import CFSG.RankThree.PartOne.FOC.CompEquiv
public import CFSG.RankThree.PartOne.FOC.PSLFamily
public import CFSG.RankThree.PartOne.FOC.PSLLie
public import CFSG.RankThree.PartOne.FOCD.G2OddQPlus
public import CFSG.RankThree.PartOne.FOCD.PRank
public import CFSG.RankThree.PartOne.KC.UnitaryDefining
public import CFSG.RankThree.PartOne.N143.LowTwoRankSplit
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionRankBound
public import CFSG.RankThree.PartOne.N143.SectionRankProof
public import CFSG.RankThree.PartOne.N143.SectionRankSplit
public import CFSG.RankThree.PartOne.SEITZ11.G2OddFinal
public import CFSG.RankThree.PartOne.SEITZ7.D4Wire
public import CFSG.RankThree.PartOne.SEITZ7.SlPair
public import CFSG.RankThree.PartOne.SEITZ7.SzPairK
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofExc
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec19
public import CFSG.RankThree.PartTwo.Sec19.SeitzScopeProofSec4
public import CFSG.RankThree.PartTwo.Sec19.Step1914Split
public import CFSG.RankThree.PartTwo.Sec4.E27.Core
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofL364
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzOther
public import CFSG.RankThree.PartTwo.Sec4.Item4Res6ProofSeitzRest
public import CFSG.RankThree.PartTwo.Sec4.T444.Item434RowsProofSeitzSz
public import CFSG.Sporadic.Co1.Module.Co2Stab
public import CFSG.Sporadic.Presentation.Co2Base
public import CFSG.Sporadic.Presentation.Co2Cover
public import CFSG.Sporadic.Presentation.Co2Fusion
public import CFSG.Sporadic.Presentation.Co2FusionInputs
public import CFSG.Sporadic.Presentation.McLExactData
public import CFSG.Sporadic.Presentation.McLExactInputs
public import CFSG.Sporadic.SuzOddCore.GraphData
public import CFSG.Sporadic.SuzOddCore.SmallActionData
public import Certificates.Certificate16041
public import Certificates.Certificate2098
public import Certificates.Certificate2103
public import Certificates.Certificate2108
public import Certificates.Certificate2109
public import Certificates.Certificate2136
public import Certificates.Certificate2139
public import Certificates.Certificate2140
public import Certificates.Certificate2145
public import Certificates.Certificate2323
public import Certificates.Certificate8160
public import Certificates.Certificate9124

public section

namespace CFSG.StandardType.NTPlane

open CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open CFSG.HardMathSupport.Lang.D4Three
open CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.OuterFourSeitz

theorem ntpD4_no_transposition
    {f : ℕ} (hf : 1 ≤ f) {L : Type} [Field L] [IsAlgClosed L] [CharP L 2]
    (Fr : L →+* L) (hFr : ∀ c, Fr c = c ^ ((2 : ℕ) ^ f))
    (hout : ∀ ε : ℕ, (ε = 1 ∨ ε = 2) → ∀ h : ↥(adjointGroup Tag.D4 L), MulAut.conj h ≠ d4Graph L ε)
    (r : ℕ) (c g : ↥(adjointGroup Tag.D4 L)) (ε : ℕ) (hε : ε = 1 ∨ ε = 2)
    (hcomm : ∀ x ∈ adjointGroup Tag.D4 L,
      (c : ModGL Tag.D4 L) * (d4P L ^ r * d4Q L * Units.map (entrywiseHom Fr)
          ((g : ModGL Tag.D4 L) * (d4P L ^ ε * x * (d4P L ^ ε)⁻¹) * (g : ModGL Tag.D4 L)⁻¹) *
          (d4Q L)⁻¹ * (d4P L ^ r)⁻¹) * (c : ModGL Tag.D4 L)⁻¹ =
        (g : ModGL Tag.D4 L) * (d4P L ^ ε * ((c : ModGL Tag.D4 L) * (d4P L ^ r * d4Q L *
          Units.map (entrywiseHom Fr) x * (d4Q L)⁻¹ * (d4P L ^ r)⁻¹) * (c : ModGL Tag.D4 L)⁻¹) *
          (d4P L ^ ε)⁻¹) * (g : ModGL Tag.D4 L)⁻¹) :
    False := by
  obtain ⟨c, hc⟩ := c
  obtain ⟨g, hg⟩ := g
  dsimp only at hcomm
  have hpos : 0 < (2 : ℕ) ^ f := pow_pos two_pos f
  have hPN : d4P L ∈ Subgroup.normalizer (adjointGroup Tag.D4 L : Set (ModGL Tag.D4 L)) :=
    Subgroup.mem_normalizer_iff_map_conj_eq.2 (map_conj_diagramMap TwistTag.D4 L (Or.inl rfl))
  have hQx : ∀ {x : ModGL Tag.D4 L}, x ∈ adjointGroup Tag.D4 L →
      d4Q L * x * (d4Q L)⁻¹ ∈ adjointGroup Tag.D4 L :=
    fun hx => labelMap_conj_mem L d4Swap_cartan hx
  have hQN : d4Q L ∈ Subgroup.normalizer (adjointGroup Tag.D4 L : Set (ModGL Tag.D4 L)) := by
    rw [Subgroup.mem_normalizer_iff]
    intro x
    refine ⟨hQx, fun hx => ?_⟩
    have h1 := hQx hx
    have e : d4Q L * (d4Q L * x * (d4Q L)⁻¹) * (d4Q L)⁻¹ = x := by
      rw [d4Q_inv]
      calc d4Q L * (d4Q L * x * d4Q L) * d4Q L = (d4Q L * d4Q L) * x * (d4Q L * d4Q L) := by
            group
        _ = x := by rw [d4Q_mul_self, one_mul, mul_one]
    rwa [e] at h1
  have hconjA : ∀ {n x : ModGL Tag.D4 L},
      n ∈ Subgroup.normalizer (adjointGroup Tag.D4 L : Set (ModGL Tag.D4 L)) →
      x ∈ adjointGroup Tag.D4 L → n * x * n⁻¹ ∈ adjointGroup Tag.D4 L :=
    fun hn hx => (Subgroup.mem_normalizer_iff.1 hn _).1 hx
  have hP3 : d4P L ^ 3 = 1 := diagramMap_pow_order TwistTag.D4 L
  have hQP : d4Q L * d4P L * (d4Q L)⁻¹ = (d4P L)⁻¹ := by
    have h := d4P_mul_swap_mul_d4P L
    change d4P L * d4Q L * d4P L = d4Q L at h
    calc d4Q L * d4P L * (d4Q L)⁻¹ = (d4P L)⁻¹ * (d4P L * d4Q L * d4P L) * (d4Q L)⁻¹ := by
          group
      _ = (d4P L)⁻¹ := by rw [h, mul_inv_cancel_right]
  have hQPe : d4Q L * d4P L ^ ε * (d4Q L)⁻¹ = (d4P L ^ ε)⁻¹ := by
    have h := map_pow (MulAut.conj (d4Q L)) (d4P L) ε
    simp only [MulAut.conj_apply] at h
    rw [h, hQP, inv_pow]
  have hFP : Units.map (entrywiseHom Fr) (d4P L) = d4P L :=
    units_map_entrywiseHom_diagramMap (t := TwistTag.D4) Fr
  have hFQ : Units.map (entrywiseHom Fr) (d4Q L) = d4Q L :=
    units_map_entrywiseHom_labelMap L d4Swap_cartan Fr
  have hFPe : Units.map (entrywiseHom Fr) (d4P L ^ ε) = d4P L ^ ε := by rw [map_pow, hFP]
  have hFrs : Function.Surjective Fr := fun d => by
    obtain ⟨z, hz⟩ := IsAlgClosed.exists_pow_nat_eq d hpos
    exact ⟨z, by rw [hFr, hz]⟩
  have hFA : ∀ {x : ModGL Tag.D4 L}, x ∈ adjointGroup Tag.D4 L →
      Units.map (entrywiseHom Fr) x ∈ adjointGroup Tag.D4 L := by
    intro x hx
    have h1 : d4P L * Units.map (entrywiseHom Fr) x * (d4P L)⁻¹ ∈ adjointGroup Tag.D4 L :=
      adjointGroup_le_comap_twistHom TwistTag.D4 L Fr hx
    have h2 := hconjA (inv_mem hPN) h1
    have e : (d4P L)⁻¹ * (d4P L * Units.map (entrywiseHom Fr) x * (d4P L)⁻¹) * (d4P L)⁻¹⁻¹ =
        Units.map (entrywiseHom Fr) x := by
      group
    rwa [e] at h2
  have hFonto : ∀ {y : ModGL Tag.D4 L}, y ∈ adjointGroup Tag.D4 L →
      ∃ x ∈ adjointGroup Tag.D4 L, Units.map (entrywiseHom Fr) x = y := by
    intro y hy
    have hmap := map_twistHom_adjointGroup TwistTag.D4 L Fr hFrs
    have h1 : d4P L * y * (d4P L)⁻¹ ∈
        (adjointGroup TwistTag.D4.tag L).map (twistHom TwistTag.D4 L Fr) := by
      rw [hmap]
      exact hconjA hPN hy
    obtain ⟨x, hx, hxy⟩ := h1
    let x' : ModGL Tag.D4 L := x
    refine ⟨x', hx, ?_⟩
    have hxy' : d4P L * Units.map (entrywiseHom Fr) x' * (d4P L)⁻¹ = d4P L * y * (d4P L)⁻¹ :=
      hxy
    exact mul_left_cancel (mul_right_cancel hxy')
  set Pr := d4P L ^ r with hPr
  set Pe := d4P L ^ ε with hPe
  set Q := d4Q L with hQ
  set F := Units.map (entrywiseHom Fr) with hF
  set G : ModGL Tag.D4 L := Pr * Q * F g * Q⁻¹ * Pr⁻¹ with hG
  have hPrN : Pr ∈ Subgroup.normalizer (adjointGroup Tag.D4 L : Set (ModGL Tag.D4 L)) :=
    pow_mem hPN r
  have hPeN : Pe ∈ Subgroup.normalizer (adjointGroup Tag.D4 L : Set (ModGL Tag.D4 L)) :=
    pow_mem hPN ε
  have key : ∀ y ∈ adjointGroup Tag.D4 L,
      (c * G * Pe⁻¹) * y * (c * G * Pe⁻¹)⁻¹ = (g * Pe * c) * y * (g * Pe * c)⁻¹ := by
    intro y hy
    have hy' : Q⁻¹ * Pr⁻¹ * y * Pr * Q ∈ adjointGroup Tag.D4 L := by
      have h1 := hconjA (inv_mem hQN) (hconjA (inv_mem hPrN) hy)
      have e : Q⁻¹ * (Pr⁻¹ * y * Pr⁻¹⁻¹) * Q⁻¹⁻¹ = Q⁻¹ * Pr⁻¹ * y * Pr * Q := by group
      rwa [e] at h1
    obtain ⟨x, hx, hFx⟩ := hFonto hy'
    have h1 := hcomm x hx
    have hF1 : F (↑g * (Pe * x * Pe⁻¹) * (↑g)⁻¹) = F g * (Pe * F x * Pe⁻¹) * (F g)⁻¹ := by
      simp only [map_mul, map_inv, hFPe]
    rw [hF1, hFx] at h1
    have eL : (c : ModGL Tag.D4 L) * (Pr * Q * (F g * (Pe * (Q⁻¹ * Pr⁻¹ * y * Pr * Q) * Pe⁻¹) *
        (F g)⁻¹) * Q⁻¹ * Pr⁻¹) * (c : ModGL Tag.D4 L)⁻¹ =
        c * G * (Pr * (Q * Pe * Q⁻¹) * Pr⁻¹ * y * Pr * (Q * Pe * Q⁻¹)⁻¹ * Pr⁻¹) * G⁻¹ * c⁻¹ := by
      rw [hG]
      group
    have eP : Pr * (Pe⁻¹) * Pr⁻¹ * y * Pr * (Pe⁻¹)⁻¹ * Pr⁻¹ = Pe⁻¹ * y * Pe := by
      rw [hPr, hPe]
      group
    have eR : (g : ModGL Tag.D4 L) * (Pe * ((c : ModGL Tag.D4 L) *
        (Pr * Q * (Q⁻¹ * Pr⁻¹ * y * Pr * Q) * Q⁻¹ * Pr⁻¹) * (c : ModGL Tag.D4 L)⁻¹) * Pe⁻¹) *
        (g : ModGL Tag.D4 L)⁻¹ = (g * Pe * c) * y * (g * Pe * c)⁻¹ := by
      group
    rw [eL, hQPe, eP, eR] at h1
    rw [← h1]
    group
  set k : ModGL Tag.D4 L := (c : ModGL Tag.D4 L)⁻¹ * (Pe⁻¹ * ((g : ModGL Tag.D4 L)⁻¹ * c * G) * Pe)
    with hk
  have hGA : G ∈ adjointGroup Tag.D4 L := by
    have h1 := hconjA hPrN (hconjA hQN (hFA hg))
    have e : Pr * (Q * F g * Q⁻¹) * Pr⁻¹ = G := by rw [hG]; group
    rwa [e] at h1
  have hkA : k ∈ adjointGroup Tag.D4 L := by
    have h1 : Pe⁻¹ * ((g : ModGL Tag.D4 L)⁻¹ * c * G) * Pe⁻¹⁻¹ ∈ adjointGroup Tag.D4 L :=
      hconjA (inv_mem hPeN) (mul_mem (mul_mem (inv_mem hg) hc) hGA)
    rw [inv_inv] at h1
    exact mul_mem (inv_mem hc) h1
  have hPe3 : Pe ^ 3 = 1 := by
    rw [hPe, ← pow_mul, mul_comm ε 3, pow_mul, hP3, one_pow]
  have hPe2 : Pe⁻¹ * Pe⁻¹ = Pe := by
    calc Pe⁻¹ * Pe⁻¹ = Pe⁻¹ * Pe⁻¹ * Pe ^ 3 := by rw [hPe3, mul_one]
      _ = Pe := by group
  have hgraph : ∀ y ∈ adjointGroup Tag.D4 L, Pe * y * Pe⁻¹ = k⁻¹ * y * k := by
    intro y hy
    have h1 := key y hy
    have e1 : (g * Pe * c : ModGL Tag.D4 L)⁻¹ * (c * G * Pe⁻¹) = k * Pe := by
      rw [hk]
      calc (g * Pe * c : ModGL Tag.D4 L)⁻¹ * (c * G * Pe⁻¹)
          = (c : ModGL Tag.D4 L)⁻¹ * (Pe⁻¹ * ((g : ModGL Tag.D4 L)⁻¹ * c * G) * Pe) *
              (Pe⁻¹ * Pe⁻¹) := by group
        _ = (c : ModGL Tag.D4 L)⁻¹ * (Pe⁻¹ * ((g : ModGL Tag.D4 L)⁻¹ * c * G) * Pe) * Pe := by
            rw [hPe2]
    have h2 : (k * Pe) * y * (k * Pe)⁻¹ = y := by
      rw [← e1]
      calc ((g * Pe * c : ModGL Tag.D4 L)⁻¹ * (c * G * Pe⁻¹)) * y *
          ((g * Pe * c : ModGL Tag.D4 L)⁻¹ * (c * G * Pe⁻¹))⁻¹
          = (g * Pe * c : ModGL Tag.D4 L)⁻¹ * ((c * G * Pe⁻¹) * y * (c * G * Pe⁻¹)⁻¹) *
              (g * Pe * c) := by group
        _ = y := by rw [h1]; group
    calc Pe * y * Pe⁻¹ = k⁻¹ * ((k * Pe) * y * (k * Pe)⁻¹) * k := by group
      _ = k⁻¹ * y * k := by rw [h2]
  apply hout ε hε ⟨k⁻¹, inv_mem hkA⟩
  refine MulEquiv.ext fun y => Subtype.ext ?_
  simp only [MulAut.conj_apply, Subgroup.coe_mul, Subgroup.coe_inv]
  rw [inv_inv, ← hgraph y y.2]
  rfl

end CFSG.StandardType.NTPlane
