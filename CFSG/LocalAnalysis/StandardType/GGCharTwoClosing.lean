module

public import CFSG.LocalAnalysis.StandardType.GGStdSubIOneDefs
public import CFSG.LocalAnalysis.GLTheoremA.CatA.CentQChar2Index
public import CFSG.RankThree.PartTwo.Sec21.HoltCatalog
public import CFSG.Assembly.StandardTypeRecognitionDefs
import CFSG.Holt.General.CaseIReduced
import CFSG.RankThree.PartOne.N143.AltRank
import CFSG.RankThree.PartTwo.Census.Alternating
import CFSG.RankThree.PartTwo.Census.Criteria
import CFSG.RankThree.PartOne.Census3.Interface
import CFSG.RankThree.OddKernel.ThreeComplementQuotient
import CFSG.Adapters.LinearCatalog
import CFSG.StronglyEmbedded.Catalog.Suzuki
import CFSG.StronglyEmbedded.Catalog.Unitary
import CFSG.StronglyEmbedded.MatrixGroups.SzModel
import CFSG.ThirdParty.QiuzhenCFSG.Theory.Comparator.Defs
import CFSG.Models.BenderSuzuki
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_6_14
public import CFSG.Assembly.LargeEvenGLABridge
public import CFSG.Assembly.OpenBridges
import CFSG.Assembly.OrderReductions.InvertedSubgroup
import CFSG.Assembly.OrderReductions.OddInversion
import CFSG.CharacterTheory.Wreathed.NonabelianCentralizer
import CFSG.Goldschmidt.Final
import CFSG.Goldschmidt.Statements
import CFSG.Goldschmidt.StatementsG4
import CFSG.Goldschmidt.StatementsH
import CFSG.Holt.Centralizer
import CFSG.Holt.General.Defs
import CFSG.Holt.MaximalFixer
import CFSG.Holt.OddCoreTwoGroupBasic
import CFSG.Holt.Witt
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3GoldschmidtFacts
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixCaseOne
import CFSG.LocalAnalysis.ComponentClassification.AschbacherTheorem3SixProper
import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderExtensionData
import CFSG.LocalAnalysis.ComponentClassification.QuasisimpleNormalizerCommutator
import CFSG.LocalAnalysis.ComponentInitial.SuzukiModelSchreier
import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupExhaustion
import CFSG.LocalAnalysis.LargeEvenClassification.C8FourSubgroupRanks
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicCongruenceCut
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicFourLarge
import CFSG.LocalAnalysis.LargeEvenClassification.CyclicTwoFourGenerators
import CFSG.LocalAnalysis.LargeEvenClassification.MacWilliamsReduction
import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourFullObstruction
import CFSG.LocalAnalysis.LargeEvenClassification.SmallCfourProperSubgroups
import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
import CFSG.RankThree.Theta.ThreeComponentOrbitCover
import CFSG.StronglyEmbedded
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.IV.theorem_5_4
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.IG1114
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Proposition82Orbit
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.SE.Section11Lemma115Torus
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremB
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.TheoremC
import CFSG.ThirdParty.QiuzhenCFSG.Glauberman.ZJTheorem
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.DihedralUniqueCentralInvolution
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.GW1965RemarkDGroup
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.MinimalCounterexample
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section1
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.Bender1970_18
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section2.PreambleHSU
import CFSG.Walter.JRFacts
import Certificates.Certificate1
import Certificates.Certificate10
import Certificates.Certificate100
import Certificates.Certificate101
import Certificates.Certificate102
import Certificates.Certificate103
import Certificates.Certificate104
import Certificates.Certificate105
import Certificates.Certificate106
import Certificates.Certificate107
import Certificates.Certificate108
import Certificates.Certificate109
import Certificates.Certificate11
import Certificates.Certificate12
import Certificates.Certificate2
import Certificates.Certificate3
import Certificates.Certificate4
import Certificates.Certificate42
import Certificates.Certificate44
import Certificates.Certificate5
import Certificates.Certificate6
import Certificates.Certificate7
import Certificates.Certificate7000
import Certificates.Certificate7001
import Certificates.Certificate7002
import Certificates.Certificate7003
import Certificates.Certificate7004
import Certificates.Certificate7005
import Certificates.Certificate7006
import Certificates.Certificate7007
import Certificates.Certificate7008
import Certificates.Certificate7009
import Certificates.Certificate7010
import Certificates.Certificate7011
import Certificates.Certificate8
import Certificates.Certificate8046
import Certificates.Certificate8049
import Certificates.Certificate8052
import Certificates.Certificate9
import Certificates.Certificate96
import Certificates.Certificate97
import Certificates.Certificate98
import Certificates.Certificate99

public section

namespace CFSG.StandardType

open CFSG.Assembly CFSG.Blueprint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.Assembly.LowTwoRank CFSG.RankThree.PartTwo.Sec21

open scoped MatrixGroups

section Rank

theorem evenRank_le_three_of_card_dvd {R : Type} [Group R] [Finite R]
    (h : Nat.card R ∣ 60480) : evenRank R ≤ 3 := by
  refine CFSG.RankThree.OddKernel.evenRank_le_of_localRank_le fun r hr hr2 => ?_
  refine (CFSG.RankThree.PartOne.N143.localRank_le_factorization hr).trans ?_
  by_contra hlt
  push Not at hlt
  have h4 : r ^ 4 ∣ Nat.card R :=
    (hr.pow_dvd_iff_le_factorization Nat.card_pos.ne').2 (by omega)
  have h5 : r ^ 4 ∣ 60480 := h4.trans h
  have hle : r ^ 4 ≤ 60480 := Nat.le_of_dvd (by norm_num) h5
  have hr16 : r < 16 := by
    by_contra h16
    have : 16 ^ 4 ≤ r ^ 4 := Nat.pow_le_pow_left (by omega) 4
    omega
  have key : ∀ r < 16, r.Prime → r ≠ 2 → ¬ r ^ 4 ∣ 60480 := by decide
  exact key r hr16 hr hr2 h5

theorem false_of_mulEquiv_alternating_rank_four {G : Type} [Group G] [Finite G]
    (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G) {n : ℕ}
    (e : G ≃* alternatingGroup (Fin n)) : False := by
  rcases le_or_gt n 11 with h11 | h12
  · have h3 := CFSG.RankThree.PartOne.N143.evenRank_alternating_le_three h11
    have h4 := CFSG.RankThree.PartOne.Census3.evenRank_le_of_mulEquiv e
    omega
  · exact CFSG.RankThree.PartTwo.Census.not_isCharTwoType_alternating (by omega)
      (CFSG.RankThree.PartTwo.Census.isCharTwoType_of_mulEquiv e hchar)

end Rank

section LieModelTwo


theorem centQIndexCases_of_lieModel_two {R : Type} [Group R] {t : StatedLieTag} {n f : ℕ}
    (h : LieModel R t n 2 f) : CFSG.LocalAnalysis.GLTheoremA.CentQIndexCases R := by
  rcases h with ⟨-, hm⟩ | ⟨-, ht, hm⟩ | ⟨-, ht, hm⟩ | ⟨-, -, hS⟩
  · exact CFSG.LocalAnalysis.GLTheoremA.centQIndexCases_of_classical_two hm
  · exact Or.inl (CFSG.LocalAnalysis.GLTheoremA.index_of_chevalleyExceptional ht hm)
  · have hadm := hm.1
    have hT : t = .twistedF4 ∨ t = .Tits := by
      revert ht hadm
      cases t <;> simp [reeTitsTags, StatedLieAdmissible]
    exact Or.inl (CFSG.LocalAnalysis.GLTheoremA.index_of_reeTits_two hT hm)
  · exact Or.inl (CFSG.LocalAnalysis.GLTheoremA.index_of_suzuki hS)

end LieModelTwo

theorem inLieTypeCharTwoCatalog_of_centQIndexCases {R : Type} [Group R] [Finite R]
    (he : 4 ≤ evenRank R) (h : CFSG.LocalAnalysis.GLTheoremA.CentQIndexCases R) :
    InLieTypeCharTwoCatalog R := by
  rcases h with hd | h5 | h6 | h8 | hc | ⟨-, hc⟩
  · exact hd
  · obtain ⟨e⟩ := h5
    have h3 := CFSG.RankThree.PartOne.N143.evenRank_alternating_le_three (n := 5) (by norm_num)
    have h4 := CFSG.RankThree.PartOne.Census3.evenRank_le_of_mulEquiv e
    omega
  · obtain ⟨e⟩ := h6
    have h3 := CFSG.RankThree.PartOne.N143.evenRank_alternating_le_three (n := 6) (by norm_num)
    have h4 := CFSG.RankThree.PartOne.Census3.evenRank_le_of_mulEquiv e
    omega
  · obtain ⟨e⟩ := h8
    have h3 := CFSG.RankThree.PartOne.N143.evenRank_alternating_le_three (n := 8) (by norm_num)
    have h4 := CFSG.RankThree.PartOne.Census3.evenRank_le_of_mulEquiv e
    omega
  · have := evenRank_le_three_of_card_dvd (R := R) (by rw [hc]; norm_num)
    omega
  · have := evenRank_le_three_of_card_dvd (R := R) (by rw [hc]; norm_num)
    omega

section Bender

private theorem card_psl_two_galoisField_two' : Nat.card PSL(2, GaloisField 2 2) = 60 := by
  have hK : Nat.card (GaloisField 2 2) = 4 := by
    rw [GaloisField.card 2 2 (by norm_num)]
    norm_num
  have : CharP (GaloisField 2 2) 2 := inferInstance
  have hcenter := CFSG.BenderSuzuki.External.huppert614_card_center_of_neg_one_eq_one
    (K := GaloisField 2 2) (CharTwo.neg_eq 1)
  have hcard := CFSG.BenderSuzuki.External.huppert614_card_psl_mul_center
    (K := GaloisField 2 2)
  rw [hK, hcenter] at hcard
  norm_num at hcard
  exact hcard

private theorem not_isMulCommutative_of_mulEquiv_aux' {G H : Type*} [Group G] [Group H]
    (e : G ≃* H) (h : ∃ a b : G, a * b ≠ b * a) : ¬ IsMulCommutative H := by
  rintro ⟨hc⟩
  obtain ⟨a, b, hab⟩ := h
  exact hab (e.injective (by rw [map_mul, map_mul]; exact hc.comm _ _))

theorem inLieTypeCharTwoCatalog_of_fusionIsBenderGroup {X : Type} [Group X] [Finite X]
    [IsSimpleGroup X] (hnonab : ∃ a b : X, a * b ≠ b * a) (he : 4 ≤ evenRank X)
    (h : CFSG.Open.fusionIsBenderGroup X) : InLieTypeCharTwoCatalog X := by
  rcases h with ⟨f, hf, ⟨e⟩⟩ | ⟨f, hf, ⟨e⟩⟩ | ⟨a, ha, ⟨e⟩⟩
  · rcases (show f = 2 ∨ 3 ≤ f by omega) with rfl | hf3
    · exfalso
      have hcard : Nat.card X = 60 := by
        rw [Nat.card_congr e.toEquiv]
        exact card_psl_two_galoisField_two'
      have := evenRank_le_three_of_card_dvd (R := X) (by rw [hcard]; norm_num)
      omega
    · let q : TauCeti.PrimePower := ⟨2, f, Nat.prime_two, by omega⟩
      have h8 : 8 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf3)
      have h9 : 2 ^ f ≠ 9 := fun h => by
        obtain ⟨k, rfl⟩ : ∃ k, f = k + 1 := ⟨f - 1, by omega⟩
        rw [pow_succ] at h
        omega
      have hv : (TauCeti.LieTypeIndex.A 1 q).Valid := by
        rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
          TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
        simp only [q, TauCeti.PrimePower.card_def]
        generalize 2 ^ f = N at *
        omega
      exact ⟨⟨TauCeti.LieTypeIndex.A 1 q, hv⟩, by simp [q],
        ⟨e.trans (CFSG.ClassicalModels.linearCatalogCandidateEquivPSL 1 q hv).symm⟩⟩
  · have hmodel : CFSG.Theory.Comparator.PSU3Model f = CFSG.Open.PSU3 2 f :=
      CFSG.Models.benderPSU3Model_eq_psu3 f
    let e' : X ≃* CFSG.Theory.Comparator.PSU3Model f := e.trans (MulEquiv.subgroupCongr hmodel.symm)
    have := e'.symm.isSimpleGroup
    have hP := not_isMulCommutative_of_mulEquiv_aux' e' hnonab
    have h4 : 4 ≤ 2 ^ f := le_trans (by norm_num) (Nat.pow_le_pow_right (by norm_num) hf)
    have hv : (TauCeti.LieTypeIndex.twistedA 2 ⟨2, f, Nat.prime_two, by omega⟩).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      simp only [TauCeti.PrimePower.card_def]
      generalize 2 ^ f = N at *
      simp
      omega
    exact ⟨⟨TauCeti.LieTypeIndex.twistedA 2 ⟨2, f, Nat.prime_two, by omega⟩, hv⟩, by simp,
      ⟨e'.trans (CFSG.BenderSuzuki.Catalog.groupEquivPSU3Model (by omega) hv hP).symm⟩⟩
  · have hv : (TauCeti.LieTypeIndex.suzuki a).Valid := by
      rw [TauCeti.LieTypeIndex.valid_iff, TauCeti.LieTypeIndex.inStandardRange_iff,
        TauCeti.LieTypeIndex.isDuplicateRepresentative_iff]
      simpa using ha
    have hmodel : CFSG.Theory.Comparator.SzModel a = CFSG.Open.Sz a :=
      CFSG.Models.benderSzModel_eq_sz a
    exact ⟨⟨TauCeti.LieTypeIndex.suzuki a, hv⟩, by simp,
      ⟨(e.trans (MulEquiv.subgroupCongr (hmodel.symm.trans
        (CFSG.BenderSuzuki.szModel_eq_suzukiMatrixGroup a)))).trans
        (CFSG.BenderSuzuki.Catalog.groupEquivSuzukiMatrixGroup hv).symm⟩⟩

end Bender

section Holt


theorem inLieTypeCharTwoCatalog_of_unique_fixed (hHolt : HoltUniqueFixedPointSimple) {G : Type}
    [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G) {N : Subgroup G} (hN : N ≠ ⊤) {z : G}
    (hz : orderOf z = 2) (hfix : ∀ q : G ⧸ N, z • q = q ↔ q = ((1 : G) : G ⧸ N))
    (hT : ∃ T : Sylow 2 N, z ∈ (T : Subgroup N).map N.subtype ∧
      (T : Subgroup N).map N.subtype ≤ Subgroup.centralizer {z}) :
    InLieTypeCharTwoCatalog G := by
  obtain ⟨S, hzS, hSc⟩ := exists_sylow_two_two_central hz hfix hT
  rcases hHolt G hnonab N hN z hz ⟨S, hzS, hSc⟩
      ⟨((1 : G) : G ⧸ N), (hfix _).mpr rfl, fun q hq => (hfix q).mp hq⟩ with
    ⟨M, hM⟩ | ⟨n, hn, ⟨e⟩⟩
  · exact inLieTypeCharTwoCatalog_of_fusionIsBenderGroup hnonab he
      (CFSG.Holt.General.fusionIsBenderGroup_of_isStronglyEmbedded hM)
  · exact (false_of_mulEquiv_alternating_rank_four hchar he e).elim

end Holt

section Skeleton


theorem inLieTypeCharTwoCatalog_of_ggSixV2Core (hHolt : HoltUniqueFixedPointSimple) {G : Type}
    [Group G] [Finite G] [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a)
    (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G) {p : ℕ} {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} {U : Type} [Group U] {Δ : UniversalRootDatum U} {t : StatedLieTag}
    {n f : ℕ} {ψ : U →* G} (hL : L ≠ ⊥) (h6 : GGSixHypV2Core p B Bs x L D J Δ t n f ψ)
    (hM : Subgroup.normalizer (ggG0 p B x L D J : Set G) = ⊤ ∨
      GGHoltAt (Subgroup.normalizer (ggG0 p B x L D J : Set G))) :
    InLieTypeCharTwoCatalog G := by
  rcases hM with hM | ⟨hne, r, hr, hfix, hT⟩
  · obtain ⟨-, -, -, -, ⟨-, hmodel⟩, -⟩ := h6
    have hN : (ggG0 p B x L D J).Normal := Subgroup.normalizer_eq_top_iff.mp hM
    have htop : ggG0 p B x L D J = ⊤ := by
      rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (ggG0 p B x L D J) with h | h
      · exact absurd (le_bot_iff.mp (h ▸ (le_sup_left : L ≤ ggG0 p B x L D J))) hL
      · exact h
    have hZ : Subgroup.center ↥(ggG0 p B x L D J) = ⊥ := by
      rw [eq_bot_iff]
      intro z hz
      have hzG : (z : G) ∈ Subgroup.center G := by
        rw [Subgroup.mem_center_iff]
        intro g
        have hg : g ∈ ggG0 p B x L D J := htop ▸ Subgroup.mem_top g
        exact congrArg Subtype.val (Subgroup.mem_center_iff.mp hz ⟨g, hg⟩)
      rw [center_eq_bot_of_simple hnonab, Subgroup.mem_bot] at hzG
      exact Subgroup.mem_bot.mpr (Subtype.ext hzG)
    have e1 : G ≃* ↥(ggG0 p B x L D J) :=
      Subgroup.topEquiv.symm.trans (MulEquiv.subgroupCongr htop.symm)
    have e2 : ↥(ggG0 p B x L D J) ≃*
        ↥(ggG0 p B x L D J) ⧸ Subgroup.center ↥(ggG0 p B x L D J) :=
      QuotientGroup.quotientBot.symm.trans (QuotientGroup.quotientMulEquivOfEq hZ.symm)
    have e := e1.trans e2
    have he' : 4 ≤ evenRank (↥(ggG0 p B x L D J) ⧸ Subgroup.center ↥(ggG0 p B x L D J)) :=
      he.trans (CFSG.RankThree.PartOne.Census3.evenRank_le_of_mulEquiv e)
    obtain ⟨d, hd, ⟨e'⟩⟩ := inLieTypeCharTwoCatalog_of_centQIndexCases he'
      (centQIndexCases_of_lieModel_two hmodel)
    exact ⟨d, hd, ⟨e.trans e'⟩⟩
  · exact inLieTypeCharTwoCatalog_of_unique_fixed hHolt hnonab hchar he hne hr hfix hT

theorem lc_gl_std_charTwo_of_v2I1_inputs (hHolt : HoltUniqueFixedPointSimple)
    (h15 : GGSecOneFiveV2I1Input) (h6 : GGSecSixV2I1Input) (G : Type) [Group G] [Finite G]
    [IsSimpleGroup G] (hnonab : ∃ a b : G, a * b ≠ b * a) (hK : KProper InCatalog G)
    (hchar : IsCharTwoType G) (he : 4 ≤ evenRank G) (p : ℕ) (hp : p ∈ LargeEvenBeta 4 G)
    (B : Subgroup G) (x : G) (L : Subgroup G) (hS : LargeEvenSStar p B x L)
    (hst : LargeEvenStandardType p B x L) : InLieTypeCharTwoCatalog G := by
  obtain ⟨Bs, D, J, ⟨t, n, f, ψ, hsix⟩, hI1⟩ := h15 G hnonab hK hchar he p hp B x L hS hst
  exact inLieTypeCharTwoCatalog_of_ggSixV2Core hHolt hnonab hchar he
    (ne_bot_of_isComponentOf' hS.2.2.2.1) hsix
    (h6 G hnonab hK hchar he p hp B x L hS hst Bs D J t n f ψ hsix hI1)

end Skeleton

end CFSG.StandardType
