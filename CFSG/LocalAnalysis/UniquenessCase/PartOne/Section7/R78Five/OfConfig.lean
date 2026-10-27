module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R78Five.Quotient
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R78Five.SzTwo
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Config
public import CFSG.LocalAnalysis.UniquenessCase.UC6R
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
import CFSG.Adapters.TauCetiLieModels
import CFSG.Assembly.OrderReductions.ThompsonQuotient
import CFSG.GH74.Uniqueness.Section4Basic
import CFSG.GroupTheory.PGroupPowTransfer
import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R72.Fstar
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.SEFive.Unitary
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.UnitaryRow
import CFSG.LocalAnalysis.UniquenessCase.UC7P3Rows3
import CFSG.Models.Blueprint
import CFSG.RankThree.PartOne.CTP.StrongPInspection
public import CFSG.Goldschmidt.StatementsG3
public import CFSG.GroupTheory.RegularModuleThree
public import CFSG.HardMathSupport.Cooperstein.Coordinator.Parts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.ONanSmallShape
public import CFSG.LocalAnalysis.AGLEmbedding.OneLieUniqueJCompetitor
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIaBlock
public import CFSG.LocalAnalysis.AGLEmbedding.OneSmallGEVIbThreeMSide
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81CZeroLeaves
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81ElevenSevenCfgOf
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAlt
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TenThreeThreeAtProof
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseOne3ACentralBaseXQ
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseThree3LinTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3CentralU
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1CaseTwo3InnerNotQRankTwo
public import CFSG.LocalAnalysis.RankThreeTheoremC.D1KlingenSp4Main
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionCyclic
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionShadow
public import CFSG.Quasithin.Background.A3Structure319
public import CFSG.Quasithin.Background.G2A5Setting
public import CFSG.Quasithin.Background.InternalSecData
public import CFSG.Quasithin.Background.InternalSecIso
public import CFSG.Quasithin.H13.Sp62D3
public import CFSG.Quasithin.Vol2.Ch10StatementsE
public import CFSG.Quasithin.Vol2.Ch11SecA02Setup
public import CFSG.Quasithin.Vol2.Ch11SecA03Basic
public import CFSG.Quasithin.Vol2.Ch11SecA04Glue
public import CFSG.Quasithin.Vol2.Ch11SecA11Exists
public import CFSG.Quasithin.Vol2.Ch11SecAFacts03
public import CFSG.Quasithin.Vol2.Ch11SecAFacts04
public import CFSG.Quasithin.Vol2.Ch11SecAVi2
public import CFSG.Quasithin.Vol2.Ch11SecSFacts
public import CFSG.Quasithin.Vol2.Ch11SecSSetup
public import Certificates.Certificate2265
public import Certificates.Certificate2266
import CFSG.Blueprint.LieModelAPI
import CFSG.GH74.Uniqueness.Lemma311
import CFSG.GH74.Uniqueness.Prop38
import CFSG.LocalAnalysis.GLTheoremB.ComponentTools
import CFSG.LocalAnalysis.GLTheoremB.QuotientTools
import CFSG.Models.Transport

public section

open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne (IrrOnMod)

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R78Five

variable {G : Type} [Group G] [Finite G]

theorem irrOnMod_of_normIrredFrattini {p : ℕ} [Fact p.Prime] {H P : Subgroup G}
    {F : Subgroup (↥H ⧸ CFSG.pPrimeCore p ↥H)} (S : Sylow p F)
    (hS : CFSG.LocalAnalysis.RankThreeTheoremC.NormIrredFrattini (S : Subgroup F))
    (hPH : P ≤ H) (hPp : IsPGroup p P)
    (hSP : (S : Subgroup F).map F.subtype =
      (P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore p ↥H))) :
    IrrOnMod (H ⊓ normalizer (P : Set G)) P (CFSG.inSubgroup frattini P) := by
  intro W hFW hWP hWN
  by_cases hW : W ≤ (frattini ↥P).map P.subtype
  · exact Or.inl (le_antisymm hW hFW)
  · exact Or.inr (CFSG.LocalAnalysis.RankThreeTheoremC.eq_of_le_of_normIrredFrattini_H
      S hS hPH hPp hSP hWP hW hWN)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.R78Five

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Sec7Core4

variable {G : Type} [Group G] [Finite G]

theorem fieldExponent_eq_one_of_r6_3 (D : UC22.Data G) (h63 : UC6.R6_3 D) (k : Sec7Core4 G)
    (hkM : k.M = D.M) {H : Subgroup G} (h7 : UC22.F07.Sec7Hyp D k.p H)
    {d : TauCeti.ValidLieTypeIndex} (hd : CFSG.AGLEmbedding.IsUnitaryIndex k.p d)
    (e : ↥(CFSG.generalizedFitting (UC22.F07.QuotK7 k.p H)) ≃* CFSG.AGLEmbedding.CatGroup d) :
    d.1.fieldExponent = 1 := by
  have : Fact k.p.Prime := ⟨k.prime⟩
  classical
  have hH : Config k H := R72.config_of_sec7Hyp k h7 hkM
  have hF := (SEFive.pElements_unitary (X := UC22.F07.QuotK7 k.p H) hd
    (CFSG.pPrimeCore_quotient_eq_bot k.prime)
    (k.isStronglyPEmbedded_map_quotient_pPrimeCore hH) e).2
  have hL : UC22.F07.ImageModK k.p H (UC22.Opp k.p H) =
      CFSG.generalizedFitting (UC22.F07.QuotK7 k.p H) :=
    R72.imageModK_opp_eq_generalizedFitting k hH (R72.forall_pow_mem_of_forall_mem_N k hH hF)
  obtain ⟨q, hqp, hq⟩ := hd
  obtain ⟨d₀, hv⟩ := d
  obtain rfl : d₀ = .twistedA 2 q := hq
  have h := (CFSG.Models.lieModel_twistedA 2 q hv
    ((MulEquiv.subgroupCongr hL).trans e)).toBlueprint (by decide)
  have hf : TauCeti.ValidLieTypeIndex.fieldExponent ⟨.twistedA 2 q, hv⟩ = q.exponent :=
    TauCeti.LieTypeIndex.fieldExponent_twistedA 2 q
  rw [show TauCeti.ValidLieTypeIndex.characteristic ⟨.twistedA 2 q, hv⟩ = q.p from
    TauCeti.LieTypeIndex.characteristic_twistedA 2 q, hqp, hf] at h
  exact hf.trans (eq_one_of_lieModel_psu D h63 h7 h)

private theorem exists_isCyclic_sylow_two_of_isoLie_sz32
    (hSz : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
      CFSG.AGLEmbeddingD2.D2TransLocalAt (.lie d) fun q => q = 5)
    (k : Sec7Core4 G) (hp5 : k.p = 5) {H : Subgroup G} (hH : k.Config H)
    (hsz : CFSG.RankThree.PartOne.Census3.IsoLie
      ↥(CFSG.generalizedFitting (UC22.F07.QuotK7 k.p H)) (.suzuki 2)) :
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ k.M) ∧ IsCyclic S := by
  obtain ⟨S, hS⟩ := CFSG.ABGLocalTools.exists_isSylowOf 2 (H ⊓ k.M)
  have hSH : S ≤ H := hS.le.trans inf_le_left
  let T : Subgroup (UC22.F07.QuotK7 k.p H) :=
    (S.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))
  have hTN : T ≤ ((H ⊓ k.M).subgroupOf H).map
      (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono H hS.le)
  have hT2 : IsPGroup 2 T :=
    (hS.isPGroup.comap_subtype (K := H)).map
      (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H))
  have hTcyc : IsCyclic T :=
    R78Five.isCyclic_of_le_of_isoLie_sz32 hSz hp5
      (CFSG.pPrimeCore_quotient_eq_bot k.prime)
      (k.two_le_pRank_quotient_pPrimeCore hH)
      (k.isStronglyPEmbedded_map_quotient_pPrimeCore hH) hsz hTN hT2
  have hker : (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)).ker = CFSG.pPrimeCore k.p ↥H :=
    QuotientGroup.ker_mk' _
  have hcop : ¬ 2 ∣ Nat.card (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)).ker := by
    rw [hker]
    exact (k.odd_card_pPrimeCore_of_not_le hH.not_le hH.two_le_pRank).not_two_dvd_nat
  have hinj : Function.Injective
      ((QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)).subgroupMap (S.subgroupOf H)) :=
    CFSG.OrderReductions.ThompsonQuotient.prime_subgroup_injective_of_coprime_kernel
      2 (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) hcop
      (S.subgroupOf H) (hS.isPGroup.comap_subtype (K := H))
  have hSubCyc : IsCyclic ↥(S.subgroupOf H) :=
    letI : IsCyclic T := hTcyc
    isCyclic_of_injective
      ((QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)).subgroupMap (S.subgroupOf H)) hinj
  exact ⟨S, hS, (Subgroup.subgroupOfEquivOfLe hSH).isCyclic.mp hSubCyc⟩

theorem r7_8At5_of_config (hId : CFSG.AGLEmbedding.KFactSmallIdent)
    (hLie : CFSG.AGLEmbedding.KFactOneLieIdent)
    (hCyc : CFSG.LocalAnalysis.RankThreeTheoremC.StronglyEmbeddedCyclicOuterKFact)
    (hIrr : CFSG.LocalAnalysis.RankThreeTheoremC.RankOneCent.KFactStepThreeIrred)
    (hSz : ∀ d : TauCeti.ValidLieTypeIndex, d.1 = .suzuki 2 →
      CFSG.AGLEmbeddingD2.D2TransLocalAt (.lie d) fun q => q = 5)
    (hT : CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.TitsFacts)
    (hM : CFSG.LocalAnalysis.RankThreeTheoremC.Generic41Spor.McLFacts)
    (k : Sec7Core4 G) (hp5 : k.p = 5) {H : Subgroup G} (hH : k.Config H)
    (hFi : ¬ CFSG.AGLEmbedding.IsFi22 ↥(CFSG.generalizedFitting (UC22.F07.QuotK7 k.p H)))
    (hU1 : ∀ d : TauCeti.ValidLieTypeIndex, CFSG.AGLEmbedding.IsUnitaryIndex k.p d →
      Nonempty (↥(CFSG.generalizedFitting (UC22.F07.QuotK7 k.p H)) ≃*
        CFSG.AGLEmbedding.CatGroup d) → d.1.fieldExponent = 1)
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf k.p P (H ⊓ k.M)) :
    (IrrOnMod (H ⊓ normalizer (P : Set G)) (CFSG.RankThree.PartOne.omegaOne k.p P)
        (CFSG.inSubgroup frattini (CFSG.RankThree.PartOne.omegaOne k.p P)) ∧
      P = CFSG.RankThree.PartOne.omegaOne k.p P) ∨
    ∃ S : Subgroup G, CFSG.ABGLocalTools.IsSylowOf 2 S (H ⊓ k.M) ∧ IsCyclic S := by
  have : Fact k.p.Prime := ⟨k.prime⟩
  classical
  obtain ⟨hPHM, hPp, -⟩ := CFSG.ABGLocalTools.isSylowOf_iff.1 hP
  have hPH : P ≤ H := hPHM.trans inf_le_left
  obtain ⟨P', hP'eq, -⟩ := k.exists_sylow_map_of_isSylowOf hH hP
  have hX : CFSG.Open.IsKGroup (UC22.F07.QuotK7 k.p H) :=
    CFSG.LocalAnalysis.GLTheoremB.isKGroup_quotient'
      (CFSG.LocalAnalysis.GLTheoremB.isKGroup_of_isKProper k.standing.kProper hH.ne_top)
      (CFSG.pPrimeCore k.p ↥H)
  rcases R78Five.quotient_rows hId hLie hCyc hIrr hT hM hp5 hX
      (CFSG.pPrimeCore_quotient_eq_bot k.prime) (k.two_le_pRank_quotient_pPrimeCore hH)
      (k.isStronglyPEmbedded_map_quotient_pPrimeCore hH) with
    ⟨hsyl, hirr⟩ | hsz | hfi | ⟨d, hd, hd2, ⟨e⟩⟩
  ·
    have hexp : ∀ y ∈ (P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)),
        y ^ k.p = 1 := by
      rw [← hP'eq]
      exact (hsyl P').2
    have hpow : ∀ x ∈ P, x ^ k.p = 1 := fun x hx => by
      simpa using congrArg Subtype.val (CFSG.GroupTheory.forall_pow_eq_one_of_map_mk'
        ((k.prime.coprime_iff_not_dvd).mp (CFSG.pPrimeCore_coprime_card (p := k.p) (G := ↥H)))
        (P := P.subgroupOf H) hPp.comap_subtype hexp ⟨x, hPH hx⟩ (mem_subgroupOf.mpr hx))
    have hΩ : CFSG.RankThree.PartOne.omegaOne k.p P = P :=
      CFSG.RankThree.PartOne.CTP.omegaOne_eq_of_pow_eq_one hpow
    have hPF : (P' : Subgroup (UC22.F07.QuotK7 k.p H)) ≤
        CFSG.generalizedFitting (UC22.F07.QuotK7 k.p H) := (hsyl P').1
    let S : Sylow k.p ↥(CFSG.generalizedFitting (UC22.F07.QuotK7 k.p H)) := P'.subtype hPF
    have hSP : ((S : Subgroup ↥(CFSG.generalizedFitting (UC22.F07.QuotK7 k.p H))).map
        (CFSG.generalizedFitting (UC22.F07.QuotK7 k.p H)).subtype) =
        (P.subgroupOf H).map (QuotientGroup.mk' (CFSG.pPrimeCore k.p ↥H)) := by
      rw [CFSG.GH74.Uniqueness.map_subtype_sylow_subtype P' hPF, hP'eq]
    have hirrP : IrrOnMod (H ⊓ normalizer (P : Set G)) P (CFSG.inSubgroup frattini P) :=
      R78Five.irrOnMod_of_normIrredFrattini S (hirr S) hPH hPp hSP
    exact Or.inl ⟨by simpa [hΩ] using hirrP, hΩ.symm⟩
  · exact Or.inr (exists_isCyclic_sylow_two_of_isoLie_sz32 hSz k hp5 hH hsz)
  · exact absurd hfi hFi
  ·
    have h1 := hU1 d hd ⟨e⟩
    omega

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Sec7Core4
