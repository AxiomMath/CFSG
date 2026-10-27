module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsD
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyEight
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComponentTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.CharTwoTorus
public import CFSG.LocalAnalysis.OddStandard.SmallAltFiveAlt5
public import CFSG.LocalAnalysis.UniquenessCase.UC22P21k
public import CFSG.Quasithin.Background.A3Structure312Quotient
public import CFSG.GroupTheory.ABGLocalTools.PStabilityQDickson
public import CFSG.GH74.GLS.Stage2.Final.ModelOrd
public import CFSG.GroupTheory.NormalizerQuotientQuotient
public import CFSG.GroupTheory.SylowNormalizedByPGroup
public import CFSG.HardMathSupport.Solomon.Coordinator.I14_20Alt
public import CFSG.HardMathSupport.Solomon.Coordinator.I28_8Defs
public import CFSG.HardMathSupport.Solomon.Coordinator.ONCAutSix
public import CFSG.HardMathSupport.Solomon.Coordinator.ONNotIso
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop22
public import CFSG.HardMathSupport.Solomon.LocalBalance.Prop42CaseThreeProof
public import CFSG.HardMathSupport.Solomon.LocalBalance.Sec3Statements
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Inputs
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6D62
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6E66
public import CFSG.HardMathSupport.Solomon.UniquenessMaximal.Sec6Interface
public import CFSG.HardMathSupport.Timmesfeld.Balance.Alt.Setup
public import CFSG.HardMathSupport.Timmesfeld.LinearRank.GLValuation
public import CFSG.HardMathSupport.Timmesfeld.Tables.Census.SporadicHolds
public import CFSG.LieType.SteinbergBROddSylowCore
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanCaseTwoCMSection
public import CFSG.LocalAnalysis.GL83PartI.I_22_5.Setup
public import CFSG.LocalAnalysis.GLTheoremB.Connected
public import CFSG.LocalAnalysis.GLTheoremB.Lemma99Core
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Sec12b
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Block
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Delta5Fin
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.A5.Inputs
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesEmbed
public import CFSG.LocalAnalysis.SeitzReduction.F4PilotMainGraphOmegaMinusPiecesOrders
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotLeviFactPiece
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.LieBorelTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyTwo
public import CFSG.Quasithin.Background.E2Statements
public import CFSG.Quasithin.Vol2.Ch10SecD33
public import CFSG.Quasithin.Vol2.Ch10SecDClA
public import CFSG.Quasithin.Vol2.Ch10SecEE3Factor
public import CFSG.Quasithin.Vol2.Ch11SecA02NatFix
public import CFSG.Quasithin.Vol2.Ch11SecA11Main
public import CFSG.Quasithin.Vol2.Ch11SecA14Conj
public import CFSG.Quasithin.Vol2.Ch11SecAFactsDelta
public import CFSG.Quasithin.Vol2.Ch11SecAViN13
public import CFSG.Quasithin.Vol2.Ch11SecBK10E
public import CFSG.Quasithin.Vol2.Ch11SecBK10F
public import CFSG.Quasithin.Vol2.Ch11SecSMain
public import CFSG.Quasithin.Vol2.Ch11SecSShape2
public import CFSG.Quasithin.Vol2.Ch11SecSSym2
public import CFSG.Quasithin.Vol2.Ch11SecSSym4
public import CFSG.Quasithin.Vol2.Ch11SecSSym5
public import CFSG.Quasithin.Vol2.Ch12Sec6P31Lie
public import CFSG.RankThree.PartOne.CTP.StrongPBridgeRest
public import CFSG.RankThree.PartTwo.KFacts.KS14SzLie
public import CFSG.RankThree.PartTwo.KFacts.OutFixCentralThree46
public import CFSG.Sporadic.Schreier.J1QT
public import CFSG.Yardstones.M67c2c3e09a6b.Definitions
public import Certificates.Kernel.J4Count.Prim

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22 CFSG.QuasithinUnique
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_isSylowTwoOf_one_le_pRank_three_of_isAlt_five {Q : Type} [Group Q] [Finite Q]
    (hQ : IsAlt Q 5) :
    ∃ S : Subgroup Q, IsSylowTwoOf S ⊤ ∧
      1 ≤ CFSG.Open.pRank 3 (⊤ : Subgroup (TauCeti.Subgroup.normalizerQuotient S)) := by
  classical
  obtain ⟨e⟩ := hQ
  let K : Subgroup (alternatingGroup (Fin 5)) :=
    (CFSG.OddStandard.SymFive.kleinSylow : Subgroup (alternatingGroup (Fin 5)))
  let S : Subgroup Q := K.map e.symm.toMonoidHom
  have hKsyl : IsSylowTwoOf K ⊤ := by
    change IsSylowTwoOf (CFSG.OddStandard.SymFive.kleinSylow :
      Subgroup (alternatingGroup (Fin 5))) ⊤
    refine ⟨le_top, CFSG.OddStandard.SymFive.kleinSylow.isPGroup', ?_⟩
    have e1 : ((CFSG.OddStandard.SymFive.kleinSylow :
        Subgroup (alternatingGroup (Fin 5))).subgroupOf ⊤).index =
        (CFSG.OddStandard.SymFive.kleinSylow :
          Subgroup (alternatingGroup (Fin 5))).index :=
      Subgroup.relIndex_top_right _
    rw [e1]
    exact CFSG.OddStandard.SymFive.kleinSylow.not_dvd_index
  have hSsyl : IsSylowTwoOf S ⊤ :=
    CFSG.Quasithin.A312.isSylowTwoOf_top_map e.symm.toMonoidHom e.symm.surjective hKsyl
  refine ⟨S, hSsyl, ?_⟩
  let g : Q := e.symm CFSG.OddStandard.SymFive.threeCycle
  have hgN : g ∈ Subgroup.normalizer (S : Set Q) := by
    rw [show S = K.map e.symm.toMonoidHom from rfl,
      ← Subgroup.map_equiv_normalizer_eq K e.symm, Subgroup.mem_map_equiv]
    simpa [g, K] using CFSG.OddStandard.SymFive.threeCycle_mem_normalizer
  have hnot : CFSG.OddStandard.SymFive.threeCycle ∉ K := by
    simp only [K, CFSG.OddStandard.SymFive.coe_kleinSylow,
      CFSG.OddStandard.SymFive.mem_kleinAlt, CFSG.OddStandard.SymFive.mem_klein,
      CFSG.OddStandard.SymFive.coe_threeCycle]
    decide +kernel
  let x : TauCeti.Subgroup.normalizerQuotient S :=
    TauCeti.Subgroup.normalizerQuotientMk S ⟨g, hgN⟩
  have h3cyc : CFSG.OddStandard.SymFive.threeCycle ^ 3 = 1 := by decide +kernel
  have hg3 : g ^ 3 = 1 := by
    rw [show g = e.symm CFSG.OddStandard.SymFive.threeCycle from rfl, ← map_pow, h3cyc,
      map_one]
  have hx3 : x ^ 3 = 1 := by
    rw [show x = TauCeti.Subgroup.normalizerQuotientMk S ⟨g, hgN⟩ from rfl, ← map_pow]
    have harg : (⟨g, hgN⟩ : Subgroup.normalizer (S : Set Q)) ^ 3 = 1 := by
      ext
      simpa using hg3
    rw [harg, map_one]
  have hx1 : x ≠ 1 := by
    intro hx
    have hgS₀ := (TauCeti.Subgroup.normalizerQuotientMk_eq_one_iff S ⟨g, hgN⟩).mp hx
    have hgS : g ∈ S := by simpa using hgS₀
    have h3K : CFSG.OddStandard.SymFive.threeCycle ∈ K := by
      have hmem : g ∈ K.map e.symm.toMonoidHom := hgS
      have h := (Subgroup.mem_map_equiv (f := e.symm)).mp hmem
      simpa [g] using h
    exact hnot h3K
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hxcard : Nat.card (Subgroup.zpowers x) = 3 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime hx3 hx1
  have hEel : CFSG.Open.IsElemAbelian 3 (Subgroup.zpowers x) :=
    CFSG.Open.isElemAbelian_zpowers (p := 3) hx3
  exact CFSG.SectionRank.le_pRank (p := 3) (H := ⊤) (E := Subgroup.zpowers x)
    (by norm_num) le_top hEel (k := 1) (by simpa using hxcard)

theorem cIsChevOver_barInf_of_isAlt_five {M L : Subgroup G}
    (hL : L ∈ calC M) (hAlt : IsAlt (Bar2 L) 5) : CIsChevOver (BarInf L) 2 := by
  have hL2 : IsL2 (Bar2 L) 2 := isL2_PSL2_two_of_isAlt_five hAlt
  obtain ⟨e⟩ := hAlt
  have hZ : Subgroup.center (Bar2 L) = ⊥ :=
    CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e
      (alternatingGroup.center_eq_bot (by simp))
  obtain ⟨einf⟩ := uc22p21k_barInf_equiv_of_center_bot hL.2.2 hZ
  have hLie : LieModel (BarInf L) .PSL 2 2 2 := hL2.of_mulEquiv einf.symm
  exact ⟨.PSL, 2, hLie.admissible, hLie⟩

theorem k_eq_two_of_conj_pair {D : Data G} {V₀ V : Subgroup G}
    {hV : Hyp125 D V₀ V} (h1 : R17_1At D V₀ V hV)
    (hK3 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_BorelTorusAbelian)
    {L L' : Subgroup G} (hL : L ∈ calC D.M) (hL' : L' ∈ calC D.M)
    (hne : L' ≠ L) (hL'conj : L' ∈ conjSetOf D.M L)
    (hX : conjClosure D.M L = L ⊔ L') (hAlt : IsAlt (Bar2 L) 5) : D.k = 2 := by
  have hnn : ¬ (L.subgroupOf D.M).Normal := by
    obtain ⟨g, hgM, hL'eq⟩ := hL'conj
    intro hN
    have hNM : D.M ≤ Subgroup.normalizer (L : Set G) :=
      (Subgroup.normal_subgroupOf_iff_le_normalizer hL.1.le).1 hN
    have hmap : L.map (MulAut.conj g).toMonoidHom = L :=
      Subgroup.mem_normalizer_iff_map_conj_eq.mp (hNM hgM)
    exact hne (hL'eq.trans hmap)
  have hZ : ¬ 3 ∣ Nat.card (Subgroup.center (Bar2 L)) := by
    obtain ⟨e⟩ := hAlt
    have hcenter : Subgroup.center (Bar2 L) = ⊥ :=
      CFSG.ABGLocalTools.center_eq_bot_of_mulEquiv e
        (alternatingGroup.center_eq_bot (by simp))
    rw [hcenter]
    have hbot : Nat.card (⊥ : Subgroup (Bar2 L)) = 1 := by simp
    rw [hbot]
    norm_num
  have hchev : CIsChevOver (BarInf L) 2 := cIsChevOver_barInf_of_isAlt_five hL hAlt
  obtain ⟨S, hS, hrank⟩ := exists_isSylowTwoOf_one_le_pRank_three_of_isAlt_five hAlt
  obtain ⟨E, hEB, hEel, hperm, hErank⟩ :=
    exists_permuting_elemAbelian_noncyclic_of_calC (D := D) (L := L)
      (X := conjClosure D.M L) (n := 2) (r := 3) hL rfl hchev hK3 hnn hZ S hS hrank
      Nat.prime_three (by norm_num)
  have hEM : E ≤ D.M := by
    refine (hEB.trans inf_le_left).trans ?_
    rw [hX]
    exact sup_le hL.1.le hL'.1.le
  exact k_eq_two_of_permuting_e9 h1 hEM hEel hperm hErank

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
