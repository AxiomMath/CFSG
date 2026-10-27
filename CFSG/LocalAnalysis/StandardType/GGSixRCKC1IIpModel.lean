module

public import CFSG.LocalAnalysis.StandardType.GGSixRCKRPrimeStepA
public import CFSG.LocalAnalysis.StandardType.GGSixRCKK1IIpIso
public import CFSG.LocalAnalysis.StandardType.AlternatingEightNormalizerAction
public import CFSG.LocalAnalysis.StandardType.GGSecFiveOrthKSLBase
public import CFSG.LocalAnalysis.StandardType.GGSixRCKC1IIIField
public import CFSG.LocalAnalysis.StandardType.GGResE6DepOrders
public import CFSG.LocalAnalysis.StandardType.GGOutTwoCommInnerHolds
public import CFSG.LocalAnalysis.StandardType.GGTCJDatum
public import CFSG.LocalAnalysis.StandardType.ChevTwoLieModel
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017ClsInn
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017ClsLin
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017ClsUni
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017ClsSymp
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017ClsD4
import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017ClsExc
public import CFSG.LocalAnalysis.GLTheoremA.CatA.I2017Image
public import CFSG.LocalAnalysis.GLTheoremA.PComp
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Inputs1415
public import CFSG.RankThree.PartTwo.Sec4.Ronan148LComp
public import CFSG.LocalAnalysis.ComponentClassification.AssemblyBPredicates
public import CFSG.Adapters.TauCetiLieModels
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.AltFacts4
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Input319
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma123
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314b
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Lemma1314c
public import CFSG.LocalAnalysis.GLTheoremB.MovingAround.Proofs.Prop1310a5b
public import CFSG.LocalAnalysis.RankThreeTheoremC.GL83Generic4_1P3M11Defs
public import Certificates.Certificate41501

public section

namespace CFSG.StandardType.RCKC1

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.StandardType
  CFSG.StandardType.RCKRP
open CFSG.Yardstones.Md0ec50421ce4 (catalogIs onLie)
open CFSG.LocalAnalysis.GLTheoremA (I2017LieA8Shape gfEightPP gfTwoPP)
open CFSG.HardMathSupport.Solomon.Coordinator (fixSubgroup)
open CFSG.Open (StatedLieTag)

private theorem rckIIp_not_lieA8Shape_A_one (q : TauCeti.PrimePower) :
    ¬ I2017LieA8Shape (.A 1 q) := by
  rintro (h | ⟨N, hN, -, h⟩ | h | ⟨k, -, h⟩)
  · injection h with h1 h2
    omega
  · injection h with h1 h2
    omega
  · cases h
  · rcases h with h | h <;> cases h

private theorem rckIIp_not_lieA8Shape_twistedA_two (q : TauCeti.PrimePower) :
    ¬ I2017LieA8Shape (.twistedA 2 q) := by
  rintro (h | ⟨N, -, -, h⟩ | h | ⟨k, -, h⟩)
  · cases h
  · cases h
  · cases h
  · rcases h with h | h <;> cases h

section Certificates


theorem rckIIp_config_classical_model
    {X : Type} [Group X] [Finite X] {t : StatedLieTag} {n f : ℕ}
    {ψ : (ggU t n f).K →* X} {p : ℕ}
    {G₀ A B₁ D J L K : Subgroup X} {e : X}
    (hrow : GGSixRCKJRow .IIp J)
    (hcfg : RCKCompConfig t n f ψ p G₀ A B₁ D J L K e) :
    K = J ∨ ∃ (s : StatedLieTag) (m g : ℕ), RCKClassicalTag s ∧
      CFSG.Blueprint.LieModel (↥K ⧸ Subgroup.center ↥K) s m 2 g ∧
      ((s = .PSL ∧ ((m = 4 ∧ g = 3) ∨ (6 ≤ m ∧ Even m ∧ g = 1))) ∨
       (s = .POmegaMinus ∧ 4 ≤ m ∧ g = 1) ∨
       (s = .POmegaPlus ∧ 5 ≤ m ∧ g = 1)) := by
  classical
  obtain ⟨-, -, hp, hp2, hAel, hB1A, hDB1, hDc, hAnorm, hMarkG, hB1J, hB1inf,
    hp4, -, -, -, -, -, hJcomp, hoddJ, -, -, -, -, -, heD, hene, hKcomp, hJK, hoddK⟩ := hcfg
  have hJperfect : commutator ↥J = ⊤ := hJcomp.2.2.1
  have hB1elem : IsElemAbelian p B₁ := hAel.mono hB1A
  have hB1p : IsPGroup p B₁ := CFSG.Open.IsElemAbelian.isPGroup hB1elem
  have hC : Nat.card ↥(B₁ ⊓ Subgroup.centralizer (J : Set X)) ≤ p ^ 2 := by
    rw [hB1inf]
    exact le_of_eq hDc
  obtain ⟨eA8⟩ := CFSG.StandardType.RCKK1IIp.rckIIp_iso hrow
  have hp3 : p = 3 :=
    CFSG.StandardType.AlternatingEightAction.prime_eq_three_of_large_action
      (G := X) (J := J) (P := B₁) hp hp2 hJperfect eA8 hB1J hB1p hp4 hC
  obtain ⟨hB1K, d, hdD, hdnot, hJd⟩ :=
    le_normalizer_and_exists_isComponentOf_of_plane
      (p := p) (G₀ := G₀) (A := A) (B₁ := B₁) (D := D) (J := J) (K := K) (e := e)
      hp hAel hB1A hDB1 hDc hAnorm hB1J hJcomp heD hene hKcomp hJK
  have heA : e ∈ A := hB1A (hDB1 heD)
  have hdA : d ∈ A := hB1A (hDB1 hdD)
  have hd3 : d ^ 3 = 1 := by
    simpa [hp3] using hAel.2 d hdA
  have hd1 : d ≠ 1 := by
    intro h
    refine hdnot ?_
    rw [h]
    exact Subgroup.one_mem _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have horder_d : orderOf d = 3 := orderOf_eq_prime hd3 hd1
  have hdN : d ∈ Subgroup.normalizer (K : Set X) := hB1K (hDB1 hdD)
  have hJd' : CFSG.Assembly.IsComponentOf J
      (Subgroup.centralizer ({d} : Set X) ⊓ K) := by
    rw [inf_comm]
    exact hJd
  obtain ⟨α, hα3, -, hJfix, -⟩ :=
    CFSG.StandardType.ggKSL_transport (G := X) (K := K) (J := J) (x := d)
      horder_d hdN hJd'
  by_cases hα1 : α = 1
  ·
    refine Or.inl ?_
    have hfix : ggFixSub α = ⊤ := by
      rw [hα1]
      ext l
      simp [mem_ggFixSub]
    have hJfixTop : CFSG.Assembly.IsComponentOf (J.subgroupOf K) ⊤ := by
      rwa [hfix] at hJfix
    have hJfixOpenTop : CFSG.Open.IsComponentOf (J.subgroupOf K) ⊤ :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open
        (J.subgroupOf K) ⊤).mp hJfixTop
    have hKqs : CFSG.Open.IsQuasisimple ↥K :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥K).mp
        hKcomp.2.2
    have htop : J.subgroupOf K = ⊤ :=
      CFSG.LocalAnalysis.GLTheoremA.eq_top_of_isComponentOf_of_isQuasisimple
        (Q := ↥K) hKqs hJfixOpenTop
    have hKleJ : K ≤ J := Subgroup.subgroupOf_eq_top.mp htop
    exact le_antisymm hKleJ hJK
  ·
    have hαne : α ≠ 1 := hα1
    have hJqs : CFSG.Open.IsQuasisimple ↥J :=
      (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥J).mp
        hJcomp.2.2
    obtain ⟨eJ⟩ :=
      CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1415.alt_of_center_odd
        hJqs (by norm_num : 8 ≤ 8) eA8 hoddJ
    have eJ0 : ↥(J.subgroupOf K) ≃* alternatingGroup (Fin 8) :=
      (Subgroup.subgroupOfEquivOfLe hJK).trans eJ
    have hJfixOpen : CFSG.Open.IsComponentOf (J.subgroupOf K) (fixSubgroup α) := by
      refine (CFSG.ComponentClassification.AssemblyBPredicates.isComponentOf_iff_open
        (J.subgroupOf K) (fixSubgroup α)).mp ?_
      rw [← CFSG.StandardType.TCJ.tcj_ggFixSub_eq_fixSubgroup]
      exact hJfix
    have hthree : 3 ∣ Nat.card ↥(J.subgroupOf K) := by
      rw [Nat.card_congr eJ0.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
      decide
    have hGLA : CFSG.Open.GLAPComponent 3 (fixSubgroup α) (J.subgroupOf K) :=
      CFSG.RankThree.PartTwo.Sec4.Ronan148L.glaPComponent_three_of_isComponentOf
        hJfixOpen hthree
    have hIsAlt : CFSG.LocalAnalysis.GLTheoremA.IsAltPType 3 (J.subgroupOf K) 8 :=
      CFSG.LocalAnalysis.GLTheoremA.I2017.isAltPType_of_mulEquiv_alt8 eJ0
    have hclass : ∀ (dd : TauCeti.ValidLieTypeIndex),
        catalogIs (↥K ⧸ Subgroup.center ↥K) (onLie fun d' => d' = dd.1) →
        I2017LieA8Shape dd.1 := by
      intro dd hcat
      exact CFSG.LocalAnalysis.GLTheoremA.I2017Cls.i2017LieClassification_of_residuals
        CFSG.LocalAnalysis.GLTheoremA.I2017Cls.linTwoA8_holds
        CFSG.LocalAnalysis.GLTheoremA.I2017Cls.uniTwoNoA8_holds
        CFSG.LocalAnalysis.GLTheoremA.I2017Cls.sympTwoNoA8_holds
        CFSG.LocalAnalysis.GLTheoremA.I2017Cls.d4TwoNoA8_holds
        CFSG.LocalAnalysis.GLTheoremA.I2017Cls.excTwoNoA8_holds
        ↥K
        ((CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥K).mp
          hKcomp.2.2)
        α (J.subgroupOf K) hα3 hαne hGLA hIsAlt dd.1 hcat
    have hKperf : commutator ↥K = ⊤ := hKcomp.2.2.1
    haveI : IsSimpleGroup (↥K ⧸ Subgroup.center ↥K) := hKcomp.2.2.2
    have hntK : Nontrivial (↥K ⧸ Subgroup.center ↥K) := inferInstance
    obtain ⟨-, labK, -, hlabK, hhasK, -, -⟩ :=
      exists_labels_dvd_of_innerDiag_component
        (X := X) (p := p) (B := A) (L := G₀) (J := K) (d := e)
        hp hp2 heA (hAel.2 e heA) hAnorm hMarkG hKcomp
    have hmarkK : MarkedModel labK (↥K ⧸ Subgroup.center ↥K) :=
      CFSG.StandardType.l05nL4h_markedModel hKperf hntK hlabK hhasK
    have hchev : CFSG.AGLEmbeddingD2.McLaughlin.WeakBlockModuleData.IsChevTwo
        (↥K ⧸ Subgroup.center ↥K) :=
      CFSG.StandardType.isChevTwo_of_markedModel hmarkK
    rcases hchev with ⟨di, -, ⟨eY⟩⟩ | ⟨na, hna, ⟨eY⟩⟩ | ⟨di, hd, ⟨eY⟩⟩
    ·
      obtain ⟨idx, hv⟩ := di
      have hcat : catalogIs (↥K ⧸ Subgroup.center ↥K) (onLie fun d' => d' = idx) :=
        ⟨.lie ⟨idx, hv⟩, rfl, ⟨eY⟩⟩
      have hshape : I2017LieA8Shape idx := hclass ⟨idx, hv⟩ hcat
      rcases hshape with h | ⟨N, hN6, hNeven, h⟩ | h | ⟨k, hk5, hrest⟩
      ·
        subst h
        have hmodels : CFSG.Models.LieModel (↥K ⧸ Subgroup.center ↥K) .PSL 4 2 3 :=
          CFSG.Models.lieModel_A 3 CFSG.LocalAnalysis.GLTheoremA.gfEightPP hv eY
        have hblue : CFSG.Blueprint.LieModel (↥K ⧸ Subgroup.center ↥K) .PSL 4 2 3 :=
          CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
            (by simp [CFSG.Blueprint.classicalTags]) hmodels
        refine Or.inr ⟨.PSL, 4, 3, ?_, ?_, ?_⟩
        · simp [RCKClassicalTag]
        · exact hblue
        · exact Or.inl ⟨rfl, Or.inl ⟨rfl, rfl⟩⟩
      ·
        subst h
        have hmodels : CFSG.Models.LieModel (↥K ⧸ Subgroup.center ↥K) .PSL N 2 1 := by
          have h := CFSG.Models.lieModel_A (N - 1)
            CFSG.LocalAnalysis.GLTheoremA.gfTwoPP hv eY
          rw [show (N - 1) + 1 = N by omega] at h
          exact h
        have hblue : CFSG.Blueprint.LieModel (↥K ⧸ Subgroup.center ↥K) .PSL N 2 1 :=
          CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
            (by simp [CFSG.Blueprint.classicalTags]) hmodels
        refine Or.inr ⟨.PSL, N, 1, ?_, ?_, ?_⟩
        · simp [RCKClassicalTag]
        · exact hblue
        · exact Or.inl ⟨rfl, Or.inr ⟨hN6, hNeven, rfl⟩⟩
      ·
        subst h
        have hmodels : CFSG.Models.LieModel (↥K ⧸ Subgroup.center ↥K) .POmegaMinus 4 2 1 :=
          CFSG.Models.lieModel_twistedD 4 CFSG.LocalAnalysis.GLTheoremA.gfTwoPP hv eY
        have hblue : CFSG.Blueprint.LieModel (↥K ⧸ Subgroup.center ↥K) .POmegaMinus 4 2 1 :=
          CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
            (by simp [CFSG.Blueprint.classicalTags]) hmodels
        refine Or.inr ⟨.POmegaMinus, 4, 1, ?_, ?_, ?_⟩
        · simp [RCKClassicalTag]
        · exact hblue
        · exact Or.inr (Or.inl ⟨rfl, le_rfl, rfl⟩)
      · rcases hrest with hD | hTD
        ·
          subst hD
          have hmodels : CFSG.Models.LieModel (↥K ⧸ Subgroup.center ↥K) .POmegaPlus k 2 1 :=
            CFSG.Models.lieModel_D k CFSG.LocalAnalysis.GLTheoremA.gfTwoPP hv eY
          have hblue : CFSG.Blueprint.LieModel (↥K ⧸ Subgroup.center ↥K) .POmegaPlus k 2 1 :=
            CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
              (by simp [CFSG.Blueprint.classicalTags]) hmodels
          refine Or.inr ⟨.POmegaPlus, k, 1, ?_, ?_, ?_⟩
          · simp [RCKClassicalTag]
          · exact hblue
          · exact Or.inr (Or.inr ⟨rfl, by omega, rfl⟩)
        ·
          subst hTD
          have hmodels : CFSG.Models.LieModel (↥K ⧸ Subgroup.center ↥K) .POmegaMinus k 2 1 :=
            CFSG.Models.lieModel_twistedD k CFSG.LocalAnalysis.GLTheoremA.gfTwoPP hv eY
          have hblue : CFSG.Blueprint.LieModel (↥K ⧸ Subgroup.center ↥K) .POmegaMinus k 2 1 :=
            CFSG.StandardType.ChevTwo.blueprintLieModel_of_modelsLieModel
              (by simp [CFSG.Blueprint.classicalTags]) hmodels
          refine Or.inr ⟨.POmegaMinus, k, 1, ?_, ?_, ?_⟩
          · simp [RCKClassicalTag]
          · exact hblue
          · exact Or.inr (Or.inl ⟨rfl, by omega, rfl⟩)
    ·
      have hsmall := not_small_card_centerQuot_of_small_field_row (Or.inr hrow) hJK
      rcases hna with h5 | h6 | h8
      · subst h5
        have hc : Nat.card (↥K ⧸ Subgroup.center ↥K) = 60 := by
          rw [Nat.card_congr eY.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
          decide
        exact (hsmall.1 hc).elim
      · subst h6
        have hc : Nat.card (↥K ⧸ Subgroup.center ↥K) = 360 := by
          rw [Nat.card_congr eY.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
          decide
        exact (hsmall.2.1 hc).elim
      · subst h8
        have hKqs : CFSG.Open.IsQuasisimple ↥K :=
          (CFSG.ComponentClassification.AssemblyBPredicates.isQuasisimple_iff_open ↥K).mp
            hKcomp.2.2
        obtain ⟨eK⟩ :=
          CFSG.LocalAnalysis.GLTheoremB.MovingAround.Inputs1415.alt_of_center_odd
            hKqs (by norm_num : 8 ≤ 8) eY hoddK
        have hcardK : Nat.card ↥K = 20160 := by
          rw [Nat.card_congr eK.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
          decide
        have hcardJ : Nat.card ↥J = 20160 := by
          rw [Nat.card_congr eJ.toEquiv, nat_card_alternatingGroup, Nat.card_fin]
          decide
        refine Or.inl ?_
        have hJK' : J = K :=
          Subgroup.eq_of_le_of_card_ge hJK (by omega)
        exact hJK'.symm
    ·
      have hcat : catalogIs (↥K ⧸ Subgroup.center ↥K) (onLie fun d' => d' = di.1) :=
        ⟨.lie di, rfl, ⟨eY⟩⟩
      have hshape : I2017LieA8Shape di.1 := hclass di hcat
      rcases hd with ⟨q, -, hidx⟩ | ⟨q, -, hidx⟩
      · rw [hidx] at hshape
        exact absurd hshape (rckIIp_not_lieA8Shape_A_one q)
      · rw [hidx] at hshape
        exact absurd hshape (rckIIp_not_lieA8Shape_twistedA_two q)

end Certificates

end CFSG.StandardType.RCKC1
