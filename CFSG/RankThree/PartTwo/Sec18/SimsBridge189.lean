module

public import CFSG.RankThree.PartTwo.Sec18.SimsBridge189Tools
public import CFSG.RankThree.PartTwo.Sec18.SimsBridge189L16
public import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411Statements
public import CFSG.RankThree.PartTwo.Sec18.SimsItem186HStatement
import CFSG.RankThree.PartTwo.Sec18.Item189StepProofO3
import CFSG.RankThree.PartTwo.Sec18.Item189StepsProof
import CFSG.RankThree.PartTwo.Sec18.Item189StepProofOddL2
import CFSG.RankThree.PartTwo.Sec18.Transport
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L2
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411L3
import CFSG.RankThree.PartTwo.Sec20.SimsAsc1411U3
public import Certificates.Certificate43
import CFSG.CharacterTheory.Semidihedral.OddFieldLift
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProper
import CFSG.LocalAnalysis.ComponentClassification.CatalogueKProperGroups
import CFSG.LocalAnalysis.ComponentClassification.DisjointSolvableKernels
import CFSG.LocalAnalysis.ComponentClassification.LayerMultiplication
import CFSG.LocalAnalysis.ComponentClassification.MinimalBCenter
import CFSG.LocalAnalysis.ComponentClassification.OrdinaryComponentJoins
import CFSG.LocalAnalysis.ComponentClassification.TwoLayer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpSuzukiCentralizer
import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpWedge
import CFSG.LocalAnalysis.ComponentClassification.UniversalOrbitBlock
import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasFive
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalFamilyLemmasSix
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalReflectionSplitting
import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7bPairs
import CFSG.LocalAnalysis.SectionRank.PRank
import CFSG.LocalAnalysis.SectionRank.SQT
import CFSG.StronglyEmbedded.BenderUnitaryCenter
import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Huppert.II.theorem_1_12
import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.RankThree.PartTwo.Sec18

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
open CFSG.RankThree.PartTwo.Late
open CFSG.Assembly.RankThreeEven (projSL projSU)

variable {G : Type} [Group G] [Finite G] {A M H : Subgroup G} {c : G}

theorem cSK189_mem_kSK189 (M H : Subgroup G) (c : G) : cSK189 M H c ∈ kSK189 M H c :=
  Subgroup.mem_subgroupOf.mpr (Sec20.self_mem_normalClosureIn M c)

theorem orderOf_cSK189 (hset : Setting189 G A M H c) : orderOf (cSK189 M H c) = 3 := by
  rw [Subgroup.orderOf_mk]
  exact orderOf_eq_prime (pow_three_of_sec18H189 hset.toSec18H)
    (ne_one_of_pRank_eq_one189 hset.pRank_eq)

theorem cSK189_mem_normalizer_sSK189 (hset : Setting189 G A M H c) :
    cSK189 M H c ∈ Subgroup.normalizer (sSK189 M H c : Set ↥(sk189 M H c)) :=
  mem_normalizer_subgroupOf189 (le_normalizer_s189 hset.toSec18H (mem_of_sec18H189 hset.toSec18H))

theorem pCoreOf_map_kSK189_inf_centralizer_le
    (hmax : s189 M H ∈ maxInvariantPiSubgroups ⊤ A (piOf 2)) (hset : Setting189 G A M H c)
    (hSK : CFSG.pPrimeCore 3 ↥(sk189 M H c) = CFSG.pCore 2 ↥(sk189 M H c))
    (hθS : theta189 M H c ≤ s189 M H)
    (hSN : (sSK189 M H c).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(sk189 M H c))) ≤
      Subgroup.normalizer (Subgroup.zpowers
        (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(sk189 M H c)) (cSK189 M H c)) :
          Set (↥(sk189 M H c) ⧸ CFSG.pPrimeCore 3 ↥(sk189 M H c)))) :
    CFSG.Open.pCoreOf 2
        ((kSK189 M H c).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(sk189 M H c))) ⊓
          Subgroup.centralizer
            ({QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(sk189 M H c)) (cSK189 M H c)} :
              Set (↥(sk189 M H c) ⧸ CFSG.pPrimeCore 3 ↥(sk189 M H c)))) ≤
      (sSK189 M H c).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(sk189 M H c))) := by
  set π := QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(sk189 M H c)) with hπ
  set e := quotEquivSKAlpha189 hSK with he
  have hinj : Function.Injective e.toMonoidHom := e.injective
  have hc : e (π (cSK189 M H c)) = alpha189 M H c (cSK189 M H c) :=
    quotEquivSKAlpha189_mk hSK _
  have hK : ((kSK189 M H c).map π).map e.toMonoidHom = kAlpha189 M H c :=
    map_quotEquivSKAlpha189 hSK (kSK189 M H c)
  have hS : ((sSK189 M H c).map π).map e.toMonoidHom = sAlpha189 M H c :=
    map_quotEquivSKAlpha189 hSK (sSK189 M H c)
  have hC : (Subgroup.centralizer ({π (cSK189 M H c)} :
        Set (↥(sk189 M H c) ⧸ CFSG.pPrimeCore 3 ↥(sk189 M H c)))).map e.toMonoidHom =
      Subgroup.centralizer ({alpha189 M H c (cSK189 M H c)} : Set (SKAlpha189 M H c)) := by
    ext y
    rw [Subgroup.mem_map]
    constructor
    · rintro ⟨x, hx, rfl⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hx ⊢
      rw [← hc]
      change e x * e (π (cSK189 M H c)) = e (π (cSK189 M H c)) * e x
      rw [← map_mul, ← map_mul, hx]
    · intro hy
      refine ⟨e.symm y, ?_, by simp⟩
      rw [Subgroup.mem_centralizer_singleton_iff] at hy ⊢
      apply e.injective
      rw [map_mul, map_mul, MulEquiv.apply_symm_apply, hc, hy]
  have hN : (Subgroup.normalizer (Subgroup.zpowers (π (cSK189 M H c)) :
        Set (↥(sk189 M H c) ⧸ CFSG.pPrimeCore 3 ↥(sk189 M H c)))).map e.toMonoidHom =
      Subgroup.normalizer (Subgroup.zpowers (alpha189 M H c (cSK189 M H c)) :
        Set (SKAlpha189 M H c)) := by
    rw [Subgroup.map_equiv_normalizer_eq, MonoidHom.map_zpowers]
    exact congrArg (fun z => Subgroup.normalizer (Subgroup.zpowers z : Set (SKAlpha189 M H c))) hc
  have hSN' : sAlpha189 M H c ≤ Subgroup.normalizer
      (Subgroup.zpowers (alpha189 M H c (cSK189 M H c)) : Set (SKAlpha189 M H c)) := by
    rw [← hN, ← hS]
    exact Subgroup.map_mono hSN
  have hT := pCoreOf_kAlpha_inf_centralizer_le189 hmax hset hθS hSN'
  rw [← Subgroup.map_le_map_iff_of_injective hinj, ← pCoreOf_map e.toMonoidHom hinj,
    Subgroup.map_inf _ _ _ hinj, hK, hC, hS]
  exact hT

section Certified


theorem asc82Item1411And1412_of (h1812 : Item181_2) (hAlt : Item182Alt1C) (h184 : Item184_1)
    (h1842 : Item184_2) (h186 : Item186H) (h187 : Item187) (hL2 : Sec20.Asc82Item1412L2)
    (hL3 : Sec20.Asc82Item1412L3) : Asc82Item1411And1412 := by
  intro G _ _ A M H c hset hcase
  have h := hset.toSec18H
  have h7 := hset.hyp187
  have hmax : s189 M H ∈ maxInvariantPiSubgroups ⊤ A (piOf 2) := (h186 G A M H c h h7).2.1.1
  have hK3 := inSubgroup_pPrimeCore_normalClosureIn_eq_pCoreOf h1812 h184 h187 h h7
  have hSK : CFSG.pPrimeCore 3 ↥(sk189 M H c) = CFSG.pCore 2 ↥(sk189 M H c) :=
    pPrimeCore_sk189_eq_of hK3
  have hθS := theta189_le_s189 hmax h hSK
  have hcN := normalizer_zpowers_le_n189_of_sec18 h1812 hAlt h184 h1842 hset
  have hhyp := hyp1411_sk189 hmax hset hK3 hSK
  have hcL := cSK189_mem_kSK189 M H c
  have hco := orderOf_cSK189 hset
  rcases hcase with ⟨⟨n, e, m, he, hm, rfl, hin, ⟨hL, -⟩ | ⟨hU, -⟩⟩, hnot⟩ | hv | hvi
  ·
    by_cases hn4 : 2 ^ e * m = 4
    · exfalso
      rw [hn4] at hL
      exact false_of_l2Sixteen189 hmax h187 hset hL.some hcN
    have hn2 : 2 ^ e * m ≠ 2 := by
      intro hn2
      rw [hn2] at hL
      exact hnot hL
    obtain ⟨i₁, i₂, h12, -, -, hn₁, hn₂⟩ := Sec20.asc82Item1411_L2even ↥(sk189 M H c)
      (kSK189 M H c) (sSK189 M H c) hhyp (nonempty_mulEquiv_map_kSK189 hSK hL)
      (map_sSK189_inf_map_kSK189_eq_bot hSK
        (sAlpha189_inf_kAlpha189_eq_bot_of_innerFree hset hK3 hin)) hn2 hn4
    exact Or.inl ⟨i₁, i₂, h12, coveredMod189_of_normal i₁ hn₁, coveredMod189_of_normal i₂ hn₂⟩
  ·
    have hn2 : 2 ≤ 2 ^ e * m := by
      have h1 : 2 ≤ 2 ^ e := by
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ e := Nat.pow_le_pow_right (by norm_num) he
      have h2 : 1 ≤ m := hm.pos
      nlinarith
    obtain ⟨i₁, i₂, h12, -, -, hn₁, hn₂⟩ := Sec20.asc82Item1411_projSU3 ↥(sk189 M H c)
      (kSK189 M H c) (sSK189 M H c) hhyp hn2 (nonempty_mulEquiv_map_kSK189 hSK hU)
      (map_sSK189_inf_map_kSK189_eq_bot hSK
        (sAlpha189_inf_kAlpha189_eq_bot_of_innerFree hset hK3 hin))
    exact Or.inl ⟨i₁, i₂, h12, coveredMod189_of_normal i₁ hn₁, coveredMod189_of_normal i₂ hn₂⟩
  ·
    obtain ⟨⟨n, hn, hL⟩, hcard, hinf⟩ := hv
    have hSL : sAlpha189 M H c ⊓ kAlpha189 M H c = ⊥ :=
      eq_bot_iff.mpr (le_trans (inf_le_inf_left _ le_sup_left) hinf.le)
    obtain ⟨i₁, i₂, h12, -, -, hn₁, hn₂⟩ := Sec20.asc82Item1411_L3graph ↥(sk189 M H c)
      (kSK189 M H c) (sSK189 M H c) hhyp hn (Or.inr (nonempty_mulEquiv_map_kSK189 hSK hL))
      ((card_map_sSK189 hSK).trans hcard) (map_sSK189_inf_map_kSK189_eq_bot hSK hSL)
    exact Or.inl ⟨i₁, i₂, h12, coveredMod189_of_normal i₁ hn₁, coveredMod189_of_normal i₂ hn₂⟩
  ·
    exfalso
    rcases hvi with ⟨p, f, hp, hp2, hq, hL⟩ | ⟨p, hp, hp3, hL⟩
    ·
      by_cases hp3 : p = 3
      · subst hp3
        exact false_of_kAlpha_projSL_two_three189 hset hq hL.some
      obtain ⟨i₁, i₂, h12, hg₁, hg₂⟩ := hL2 ↥(sk189 M H c) (kSK189 M H c) (sSK189 M H c)
        (cSK189 M H c) hhyp hSK ⟨p, f, hp, hp2, hp3, hq, nonempty_mulEquiv_map_kSK189 hSK hL⟩
        hcL hco (cSK189_mem_normalizer_sSK189 hset)
        (pCoreOf_map_kSK189_inf_centralizer_le hmax hset hSK hθS)
      exact false_of_sup_normalizer_eq_top189 hset hcN h12 hg₁ hg₂
    ·
      have hL' : (p % 3 = 2 ∧ Nonempty (↥((kSK189 M H c).map
            (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(sk189 M H c)))) ≃*
            projSL 3 (GaloisField p 1))) ∨
          (p % 3 = 1 ∧ Nonempty (↥((kSK189 M H c).map
            (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥(sk189 M H c)))) ≃* projSU 3 p 1)) := by
        rcases hL with ⟨hp2, hL⟩ | ⟨hp1, hL⟩
        · exact Or.inl ⟨hp2, nonempty_mulEquiv_map_kSK189 hSK hL⟩
        · exact Or.inr ⟨hp1, nonempty_mulEquiv_map_kSK189 hSK hL⟩
      obtain ⟨i₁, i₂, h12, hg₁, hg₂⟩ := hL3 ↥(sk189 M H c) (kSK189 M H c) (sSK189 M H c)
        (cSK189 M H c) hhyp hSK ⟨p, hp, hp3, hL'⟩ hcL hco
      exact false_of_sup_normalizer_eq_top189 hset hcN h12 hg₁ hg₂

end Certified

end CFSG.RankThree.PartTwo.Sec18
