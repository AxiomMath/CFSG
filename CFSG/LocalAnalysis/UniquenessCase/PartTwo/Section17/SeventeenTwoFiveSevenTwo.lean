module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
public import CFSG.Blueprint.LieModelAPI
public import CFSG.LocalAnalysis.RankThreeTheoremC.LayerNormal
public import CFSG.RankThree.GF2n.Basic
public import CFSG.GH74.QTGen4.DSGen4.Leaf.DSBA5Vertex
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22H
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.PCore.PPrimeCore
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.CardSupOfDisjointNormalizer
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248Glue4
public import CFSG.GroupTheory.PElementSubgroup
public import CFSG.GroupTheory.ElementaryAbelianTransport
public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.Frattini.Core
public import CFSG.GH74.KGroups.PSL2
public import CFSG.LocalAnalysis.AGLEmbedding.LinTwoFacts
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.UnitaryModel
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.KFactCaseTwoSylowAutProof
public import CFSG.LocalAnalysis.ShultStronglyClosedTI.SuzukiModelPointStructureTransport
public import CFSG.StronglyEmbedded.Catalog.Suzuki
public import CFSG.RankThree.PartOne.S12K.Rigidity
public import CFSG.RankThree.PartOne.K128.TitsShape
public import CFSG.Sporadic.McL.Simple
public import Mathlib
public import CFSG.GH74.QTGen4.DSGen4.Statements
public import CFSG.LieType.Ree.LargeReeEightTorus
public import CFSG.LocalAnalysis.GL83PartI.I_7_13
public import CFSG.LocalAnalysis.GLTheoremA.CatA.H248Glue3
public import CFSG.LocalAnalysis.GLTheoremA.P55.Inputs
public import CFSG.LocalAnalysis.GLTheoremA.Pump
public import CFSG.LocalAnalysis.GLTheoremA.S6.Inputs6364
public import CFSG.LocalAnalysis.GLTheoremB.Lemma911Defs
public import CFSG.LocalAnalysis.GLTheoremB.SchreierTools
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.AppCCases
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.A3A3Perm
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Basic
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.L2_4_27
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.DoubleA3.Statements
public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.SL2ModulesBorel
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DefsE
public import CFSG.Quasithin.Background.B5FinOut
public import CFSG.Quasithin.Background.E3
public import CFSG.Quasithin.Background.E3Nprime
public import CFSG.Quasithin.Background.E3OffenderB
public import CFSG.Quasithin.Background.E3Uniq
public import CFSG.Quasithin.Background.E4Solv
public import CFSG.Quasithin.Background.F9FiveStruct
public import CFSG.Quasithin.Background.FFC4Real
public import CFSG.Quasithin.Background.GoldschmidtRankOneFacts
public import CFSG.Quasithin.EmptyFaithful.GoldschmidtF112ListC
public import CFSG.Quasithin.H13.A5S1326
public import CFSG.Quasithin.H13.A5Top
public import CFSG.Quasithin.Vol2.Ch10StatementsInputsAS2
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem20
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem20Pick
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22D
public import CFSG.Quasithin.Vol2.Ch12Sec2Lem22E
public import CFSG.RankThree.PartOne.K128.D4Arith
public import CFSG.RankThree.PartOne.KD4T.Certs
public import CFSG.RankThree.PartOne.KE.A1SL2
public import CFSG.RankThree.PartOne.KE.A1Torus
public import CFSG.RankThree.PartOne.KE.A2Family
public import CFSG.RankThree.PartOne.KE.A2Shape
public import CFSG.RankThree.PartOne.KE.SigmaUntwisted
public import CFSG.RankThree.PartOne.KLR.Master
public import CFSG.RankThree.PartOne.KLR.SectorAssembly
public import CFSG.Timmesfeld.Moufang.Three
public import CFSG.Timmesfeld.RankOne
public import CFSG.Timmesfeld.Special.TwoCore

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC22.F07
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.PartOne
open CFSG.Blueprint (LieModel)
open TauCeti
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

@[expose] def R72UnitaryFiveOne (D : Data G) : Prop :=
  ∀ H : Subgroup G, F07.Sec7Hyp D 5 H →
    ∀ n : ℕ, LieModel (LKQuot7 5 H) .PSU 3 5 n → n = 1


theorem isElemAbelian_or_card_le_of_r72_five {X : Type} [Group X] [Finite X]
    (hX : (∃ n, LieModel X .PSL 2 5 n) ∨ LieModel X .PSU 3 5 1 ∨ IsAutSz X 5 ∨
      LieModel X .Tits 0 2 1 ∨ IsSpor X .McL ∨ IsAlt X 10)
    {Q : Subgroup X} (hQ : IsPGroup 5 ↥Q) :
    IsElemAbelian 5 Q ∨ Nat.card ↥Q ≤ 5 ^ 3 := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  rcases hX with hPSL | hPSU | hSz | hTits | hMcL | hAlt
  ·
    obtain ⟨n, hL⟩ := hPSL
    have hn : 1 ≤ n := hL.admissible.2.1
    have hn0 : 0 < n := by omega
    obtain ⟨e⟩ := CFSG.GH74.KGroups.PSL2.psl2_equiv_of_lieModel (F := GaloisField 5 n) 5 n
      hn0 (GaloisField.card 5 n hn0.ne') hL
    left
    obtain ⟨S, hQS⟩ := (IsPGroup.map hQ e.toMonoidHom).exists_le_sylow
    have hSel : IsElemAbelian 5 (S : Subgroup (CFSG.AGLEmbedding.PSL2GF 5 n)) :=
      (CFSG.AGLEmbedding.psl2GF_sylow 5 n hn S).1
    have hQel : IsElemAbelian 5 (Q.map e.toMonoidHom) := hSel.mono hQS
    have hQel' : CFSG.IsElementaryAbelian 5 ↥(Q.map e.toMonoidHom) :=
      CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hQel
    have hQelP : CFSG.IsElementaryAbelian 5 ↥Q :=
      CFSG.IsElementaryAbelian.of_mulEquiv
        (Subgroup.equivMapOfInjective Q e.toMonoidHom e.injective).symm hQel'
    exact CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mpr hQelP
  ·
    have hst : CFSG.Open.StatedClassicalModel X .PSU 3 5 1 :=
      hPSU.statedClassicalModel (by decide)
    obtain ⟨-, hf1, -, K, _, _, J, hJ, hK, hfix, ⟨e⟩⟩ :=
      CFSG.AGLEmbedding.UnitaryModel.exists_equiv_psu hst
    have hchar : CharP K 5 :=
      CFSG.AGLEmbedding.UnitaryModel.charP_of_card Nat.prime_five hK
    obtain ⟨S, hS⟩ :=
      CFSG.AGLEmbedding.UnitaryModel.exists_sylow_eq_rootGroup J hJ hK hfix hf1
    obtain ⟨U, hQU⟩ := hQ.exists_le_sylow
    obtain ⟨e', he'⟩ := CFSG.AGLEmbedding.UnitaryModel.exists_equiv_map_eq e U S
    right
    have hcardU : Nat.card ↥(U : Subgroup X) = 5 ^ 3 := by
      rw [← Subgroup.card_map_of_injective (K := (U : Subgroup X))
          (f := e'.toMonoidHom) e'.injective, he', hS,
        CFSG.AGLEmbedding.UnitaryModel.card_rootGroup_eq J hJ hK hfix]
    have hQle := Subgroup.card_le_of_le hQU
    rwa [hcardU] at hQle
  ·
    obtain ⟨S, _, hSzS, ⟨e⟩⟩ := hSz
    have hSuz : CFSG.Blueprint.SuzukiModel S 2 5 :=
      (CFSG.Blueprint.LieModel.suzukiModel hSzS).2
    obtain ⟨-, a, ha, K, hKf, hKfin, hf, hK, ⟨eK⟩⟩ := hSuz
    letI : Field K := hKf
    letI : Finite K := hKfin
    haveI : Finite S :=
      Finite.of_equiv (CFSG.Blueprint.suzukiGroup (K := K) a) eK.symm.toEquiv
    right
    let A : Subgroup (MulAut S) := Q.map e.toMonoidHom
    have hA : IsPGroup 5 A := IsPGroup.map hQ e.toMonoidHom
    have hcase : CFSG.AGLEmbedding.IsCaseTwoGroup 5 S := by
      have ha2 : a = 2 := by omega
      subst ha2
      have hK' : Nat.card K = 2 ^ (2 * 2 + 1) := by simpa using hK
      have hv : (TauCeti.LieTypeIndex.suzuki 2).Valid := by
        rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
          TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        exact ⟨by norm_num, not_false⟩
      refine ⟨⟨TauCeti.LieTypeIndex.suzuki 2, hv⟩, Or.inr ⟨rfl, rfl⟩, ?_⟩
      let eSM := CFSG.ShultStronglyClosedTI.SuzukiModel.suzukiGroupEquivSuzukiMatrixGroup hK'
      exact ⟨eK.trans (eSM.trans (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv).symm)⟩
    have hbound : Nat.card ↥A ≤ 5 ^ 3 :=
      CFSG.LocalAnalysis.RankThreeTheoremC.card_le_of_isPGroup_mulAut_five hcase hA
    have hcard : Nat.card ↥A = Nat.card ↥Q := by
      dsimp only [A]
      exact Subgroup.card_map_of_injective e.injective
    rwa [hcard] at hbound
  ·
    obtain ⟨-, hTits⟩ := CFSG.Blueprint.LieModel.reeTitsModel hTits (by decide)
    right
    have hcard : Nat.card X = CFSG.Open.ordTits :=
      CFSG.RankThree.PartOne.S12K.card_of_reeTitsModel_Tits hTits
    have hfac : (Nat.card X).factorization 5 ≤ 3 := by
      rw [hcard, CFSG.RankThree.PartOne.K128.factorization_ordTits_five]
      norm_num
    have hle : Nat.card ↥Q ≤ 5 ^ (Nat.card X).factorization 5 := by
      simpa using CFSG.LocalAnalysis.GLTheoremA.H248.card_le_pow_factorization
        Nat.prime_five (le_top : Q ≤ ⊤) hQ
    exact hle.trans (Nat.pow_le_pow_right (by norm_num) hfac)
  ·
    obtain ⟨e⟩ := hMcL
    right
    have hcard : Nat.card X = 898128000 := by
      rw [Nat.card_congr e.toEquiv]
      dsimp [CFSG.Blueprint.NativeSporadic.Carrier]
      exact CFSG.Sporadic.McL.card_McL
    have hfac : (Nat.card X).factorization 5 ≤ 3 := by
      rw [hcard, show (898128000 : ℕ) = 5 ^ 3 * 7185024 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5), Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
    have hle : Nat.card ↥Q ≤ 5 ^ (Nat.card X).factorization 5 := by
      simpa using CFSG.LocalAnalysis.GLTheoremA.H248.card_le_pow_factorization
        Nat.prime_five (le_top : Q ≤ ⊤) hQ
    exact hle.trans (Nat.pow_le_pow_right (by norm_num) hfac)
  ·
    obtain ⟨e⟩ := hAlt
    right
    have hcard : Nat.card X = 1814400 := by
      rw [Nat.card_congr e.toEquiv, nat_card_alternatingGroup]
      norm_num
    have hfac : (Nat.card X).factorization 5 ≤ 3 := by
      rw [hcard, show (1814400 : ℕ) = 5 ^ 2 * 72576 by norm_num,
        Nat.factorization_mul (by norm_num) (by norm_num), Finsupp.add_apply,
        Nat.Prime.factorization_pow (by norm_num : Nat.Prime 5), Finsupp.single_eq_same,
        Nat.factorization_eq_zero_of_not_dvd (by norm_num)]
      norm_num
    have hle : Nat.card ↥Q ≤ 5 ^ (Nat.card X).factorization 5 := by
      simpa using CFSG.LocalAnalysis.GLTheoremA.H248.card_le_pow_factorization
        Nat.prime_five (le_top : Q ≤ ⊤) hQ
    exact hle.trans (Nat.pow_le_pow_right (by norm_num) hfac)

theorem eq_of_r7_8_one (D : Data G) (h72 : F07.R72 D) (h72u : R72UnitaryFiveOne D)
    {H P D' : Subgroup G} (h7 : F07.Sec7Hyp D 5 H)
    (hP : CFSG.ABGLocalTools.IsSylowOf 5 P (H ⊓ D.M))
    (hD'P : D' ≤ P) (hD'nc : ¬ IsCyclic ↥D')
    (hD'n : ((D' ⊔ CFSG.Open.pCoreOf 2 D.M).subgroupOf D.M).Normal)
    (hirr : IrrOnMod (H ⊓ Subgroup.normalizer (P : Set G)) P
      (inSubgroup frattini P)) :
    P = D' := by
  classical
  haveI : Fact (Nat.Prime 5) := ⟨Nat.prime_five⟩
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hP5 : IsPGroup 5 ↥P := hP.isPGroup
  have hD'5 : IsPGroup 5 ↥D' := hP5.to_le hD'P
  have hD'M : D' ≤ D.M := (hD'P.trans hP.le).trans inf_le_right
  let O : Subgroup G := CFSG.Open.pCoreOf 2 D.M
  let V : Subgroup G := D' ⊔ O
  have hOM : O ≤ D.M := CFSG.LieType.BorelTits.pCoreOf_le 2 D.M
  have hVle : V ≤ D.M := sup_le hD'M hOM
  have hD'O : D' ≤ Subgroup.normalizer (O : Set G) :=
    hD'M.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 D.M)
  have hO2 : IsPGroup 2 O := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 D.M
  have hdisj : Disjoint O D' :=
    IsPGroup.disjoint_of_coprime hO2 hD'5 (by norm_num : Nat.Coprime 2 5)
  have hO5 : ¬ 5 ∣ Nat.card ↥O := by
    obtain ⟨m, hm⟩ := hO2.exists_card_eq
    rw [hm]
    exact fun h => by
      have h52 : 5 ∣ 2 := Nat.prime_five.dvd_of_dvd_pow h
      norm_num at h52
  have hVcard : Nat.card ↥V = Nat.card ↥D' * Nat.card ↥O := by
    dsimp only [V]
    rw [sup_comm,
      CFSG.GorensteinWalter.card_sup_eq_mul_of_disjoint_of_le_normalizer O D' hD'O hdisj,
      mul_comm]
  have hVfac : (Nat.card ↥V).factorization 5 = (Nat.card ↥D').factorization 5 := by
    rw [hVcard, Nat.factorization_mul (Nat.card_pos.ne') (Nat.card_pos.ne'), Finsupp.add_apply,
      Nat.factorization_eq_zero_of_not_dvd hO5, add_zero]
  have hD'fac : Nat.card ↥D' = 5 ^ (Nat.card ↥D').factorization 5 := by
    obtain ⟨k, hk⟩ := hD'5.exists_card_eq
    rw [hk, Nat.factorization_pow_self Nat.prime_five]
  have hPV5 : IsPGroup 5 ↥(P ⊓ V) := hP5.to_le inf_le_left
  have hcardPV : Nat.card ↥(P ⊓ V) ≤ 5 ^ (Nat.card ↥V).factorization 5 :=
    CFSG.LocalAnalysis.GLTheoremA.H248.card_le_pow_factorization Nat.prime_five
      inf_le_right hPV5
  have hcardle : Nat.card ↥(P ⊓ V) ≤ Nat.card ↥D' := by
    calc Nat.card ↥(P ⊓ V) ≤ 5 ^ (Nat.card ↥V).factorization 5 := hcardPV
      _ = 5 ^ (Nat.card ↥D').factorization 5 := by rw [hVfac]
      _ = Nat.card ↥D' := hD'fac.symm
  have hPVD' : P ⊓ V = D' :=
    (Subgroup.eq_of_le_of_card_ge (le_inf hD'P le_sup_left) hcardle).symm
  let N : Subgroup G := H ⊓ Subgroup.normalizer (P : Set G)
  have hN_P : N ≤ Subgroup.normalizer (P : Set G) := inf_le_right
  have hP1 : P ≠ ⊥ := by
    intro hbot
    apply hD'nc
    have hD'bot : D' = ⊥ := le_bot_iff.mp (by rw [← hbot]; exact hD'P)
    rw [hD'bot]
    exact Bot.isCyclic
  have hN_M : N ≤ D.M :=
    hN_P.trans (h7.2.2.1.normalizer_le hP1 hP5 (hP.le.trans inf_le_right))
  have hM_V : D.M ≤ Subgroup.normalizer (V : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hVle).1 hD'n
  have hN_V : N ≤ Subgroup.normalizer (V : Set G) := hN_M.trans hM_V
  have hN_D' : N ≤ Subgroup.normalizer (D' : Set G) := by
    have h : N ≤ Subgroup.normalizer ((P ⊓ V : Subgroup G) : Set G) :=
      fun n hn => CFSG.RankThree.GF2n.mem_normalizer_inf (hN_P hn) (hN_V hn)
    rwa [hPVD'] at h
  let W : Subgroup G := D' ⊔ inSubgroup frattini P
  have hPhiW : inSubgroup frattini P ≤ W := le_sup_right
  have hPhiP : inSubgroup frattini P ≤ P := by
    rw [CFSG.inSubgroup]
    exact Subgroup.map_subtype_le _
  have hWP : W ≤ P := sup_le hD'P hPhiP
  have hN_Phi : N ≤ Subgroup.normalizer ((inSubgroup frattini P : Subgroup G) : Set G) :=
    fun n hn => CFSG.RankThree.GF2n.mem_normalizer_inSubgroup_frattini (hN_P hn)
  have hN_W : N ≤ Subgroup.normalizer (W : Set G) :=
    fun n hn => CFSG.RankThree.GF2n.mem_normalizer_sup (hN_D' hn) (hN_Phi hn)
  have hWcases := hirr W hPhiW hWP hN_W
  rcases hWcases with hWPhi | hWP'
  ·
    exfalso
    have hD'Phi : D' ≤ inSubgroup frattini P := by
      rw [← hWPhi]
      exact le_sup_left
    have hD'25 : 25 ≤ Nat.card ↥D' := by
      obtain ⟨k, hk⟩ := hD'5.exists_card_eq
      have hk2 : 2 ≤ k := by
        rcases Nat.lt_or_ge k 2 with hklt | hkge
        · interval_cases k
          · have h1 : Nat.card ↥D' = 1 := by rw [hk]; norm_num
            haveI : Subsingleton ↥D' := (Nat.card_eq_one_iff_unique.mp h1).1
            exact absurd isCyclic_of_subsingleton hD'nc
          · have h1 : Nat.card ↥D' = 5 := by rw [hk]; norm_num
            exact absurd (isCyclic_of_prime_card h1) hD'nc
        · exact hkge
      rw [hk]
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ 5 ^ k := Nat.pow_le_pow_right (by norm_num) hk2
    have hPnc : ¬ IsCyclic ↥P := by
      intro hcyc
      letI : IsCyclic ↥P := hcyc
      exact hD'nc (Subgroup.isCyclic_of_le hD'P)
    have hPhi25 : 25 ≤ Nat.card ↥(inSubgroup frattini P) :=
      hD'25.trans (Subgroup.card_le_of_le hD'Phi)
    have hq5 : IsPGroup 5 (↥P ⧸ frattini ↥P) := hP5.to_quotient (frattini ↥P)
    have hqgt : 5 < Nat.card (↥P ⧸ frattini ↥P) := by
      by_contra hle
      have hle' : Nat.card (↥P ⧸ frattini ↥P) ≤ 5 := by omega
      exact hPnc (CFSG.Quasithin.H13.Lem22.isCyclic_of_card_frattini_le
        Nat.prime_five hP5 hle')
    obtain ⟨j, hj⟩ := hq5.exists_card_eq
    have hj2 : 2 ≤ j := by
      rcases Nat.lt_or_ge j 2 with hjlt | hjge
      · interval_cases j <;> (rw [hj] at hqgt; norm_num at hqgt)
      · exact hjge
    have hquot25 : 25 ≤ Nat.card (↥P ⧸ frattini ↥P) := by
      rw [hj]
      calc 25 = 5 ^ 2 := by norm_num
        _ ≤ 5 ^ j := Nat.pow_le_pow_right (by norm_num) hj2
    have hPhiCard : Nat.card ↥(inSubgroup frattini P) = Nat.card ↥(frattini ↥P) := by
      rw [CFSG.inSubgroup]
      exact Subgroup.card_map_of_injective P.subtype_injective
    have hPcard : Nat.card ↥P =
        Nat.card (↥P ⧸ frattini ↥P) * Nat.card ↥(frattini ↥P) :=
      Subgroup.card_eq_card_quotient_mul_card_subgroup (frattini ↥P)
    have hP4 : 5 ^ 4 ≤ Nat.card ↥P := by
      rw [hPcard, ← hPhiCard]
      calc 5 ^ 4 = 25 * 25 := by norm_num
        _ ≤ Nat.card (↥P ⧸ frattini ↥P) * Nat.card ↥(inSubgroup frattini P) :=
            Nat.mul_le_mul hquot25 hPhi25
    have hP_H : P ≤ H := hP.le.trans inf_le_left
    let K : Subgroup G := PPrimeCoreIn 5 H
    let L : Subgroup G := Opp 5 H
    have hP_L : P ≤ L := by
      simpa only [L, Opp] using
        CFSG.le_pElementSubgroup_of_isPGroup Nat.prime_five hP5 hP_H
    have hKcop : Nat.Coprime 5 (Nat.card ↥K) := by
      have h := CFSG.pPrimeCore_coprime_card (p := 5) (G := ↥H)
      dsimp only [K, PPrimeCoreIn]
      rwa [Subgroup.card_map_of_injective H.subtype_injective]
    have hP_disj_K : Disjoint P K := by
      refine Subgroup.disjoint_of_coprime_natCard ?_
      obtain ⟨k, hk⟩ := hP5.exists_card_eq
      rw [hk]
      exact hKcop.pow_left k
    let π : ↥H →* QuotK7 5 H := QuotientGroup.mk' (CFSG.pPrimeCore 5 ↥H)
    let g : ↥P →* QuotK7 5 H := π.comp (Subgroup.inclusion hP_H)
    have hg : ∀ x : ↥P, g x ∈ ImageModK 5 H (Opp 5 H) := by
      intro x
      rw [ImageModK, Subgroup.mem_map]
      exact ⟨⟨x.1, hP_H x.2⟩, Subgroup.mem_subgroupOf.mpr (hP_L x.2), rfl⟩
    let f : ↥P →* LKQuot7 5 H := g.codRestrict (ImageModK 5 H (Opp 5 H)) hg
    have hinj : Function.Injective f := by
      have hf_one : ∀ x : ↥P, f x = 1 → x = 1 := by
        intro x hx
        have hx1 : g x = 1 := by
          have h := congrArg Subtype.val hx
          simpa [f] using h
        have hx1' : π (⟨x.1, hP_H x.2⟩ : ↥H) = 1 := hx1
        have hxK : x.1 ∈ K := by
          dsimp only [K, PPrimeCoreIn]
          rw [Subgroup.mem_map]
          exact ⟨⟨x.1, hP_H x.2⟩, (QuotientGroup.eq_one_iff _).mp hx1', rfl⟩
        have hxbot : x.1 ∈ (⊥ : Subgroup G) := by
          have hxPK : x.1 ∈ P ⊓ K := ⟨x.2, hxK⟩
          rwa [hP_disj_K.eq_bot] at hxPK
        exact Subtype.ext (Subgroup.mem_bot.mp hxbot)
      intro x y hxy
      have h1 : f (x * y⁻¹) = 1 := by rw [map_mul, map_inv, hxy, mul_inv_cancel]
      exact mul_inv_eq_one.mp (hf_one (x * y⁻¹) h1)
    let Q : Subgroup (LKQuot7 5 H) := f.range
    have ePQ : ↥P ≃* ↥Q := MonoidHom.ofInjective hinj
    have hQ5 : IsPGroup 5 Q := hP5.of_equiv ePQ
    have hQcard : Nat.card ↥Q = Nat.card ↥P := (Nat.card_congr ePQ.toEquiv).symm
    have hQbound : IsElemAbelian 5 Q ∨ Nat.card ↥Q ≤ 5 ^ 3 := by
      refine isElemAbelian_or_card_le_of_r72_five (X := LKQuot7 5 H) ?_ hQ5
      rcases (h72 5 H h7).2 with hPSL | ⟨n, hPSU⟩ | hP3 | hP5list | hP11
      · exact Or.inl hPSL
      · obtain rfl := h72u H h7 n hPSU
        exact Or.inr (Or.inl hPSU)
      · obtain ⟨h3, -⟩ := hP3
        omega
      · obtain ⟨-, hlist⟩ := hP5list
        rcases hlist with hSz | hTits | hMcL | hAlt
        · exact Or.inr (Or.inr (Or.inl hSz))
        · exact Or.inr (Or.inr (Or.inr (Or.inl hTits)))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hMcL))))
        · exact Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hAlt))))
      · obtain ⟨h11, -⟩ := hP11
        omega
    have hD'ne : D' ≠ ⊥ := by
      intro hbot
      apply hD'nc
      rw [hbot]
      exact Bot.isCyclic
    rcases hQbound with hQel | hQle
    ·
      have hQelClass : CFSG.IsElementaryAbelian 5 ↥Q :=
        CFSG.Open.isElemAbelian_iff_isElementaryAbelian.mp hQel
      have hPelClass : CFSG.IsElementaryAbelian 5 ↥P :=
        CFSG.IsElementaryAbelian.of_mulEquiv ePQ.symm hQelClass
      letI : IsElementaryAbelian 5 ↥P := hPelClass
      letI : Fact (IsPGroup 5 ↥P) := ⟨hP5⟩
      have hPhiBot : CFSG.inSubgroup frattini P = ⊥ := by
        rw [CFSG.inSubgroup, CFSG.frattini_eq_bot_of_isElementaryAbelian (R := ↥P) (p := 5),
          Subgroup.map_bot]
      have hD'bot : D' ≤ (⊥ : Subgroup G) := by
        rw [← hPhiBot]
        exact hD'Phi
      exact hD'ne (le_bot_iff.mp hD'bot)
    ·
      have hPle3 : Nat.card ↥P ≤ 5 ^ 3 := by
        rw [← hQcard]
        exact hQle
      have h53 : (5 : ℕ) ^ 3 < 5 ^ 4 := by norm_num
      omega
  ·
    refine le_antisymm ?_ hD'P
    refine CFSG.GH74.QTGen4.DSGen4.DSBA5.le_of_sup_dsFrattini_eq
      (Q := P) (M := D') hD'P ?_
    simpa [W, CFSG.inSubgroup, CFSG.GH74.QTGen4.DSGen4.dsFrattini] using hWP'

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
