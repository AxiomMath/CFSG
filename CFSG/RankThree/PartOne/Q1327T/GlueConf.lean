module

public import CFSG.RankThree.PartOne.Q1327T.GlueN
public import CFSG.RankThree.PartOne.Q1327T.Transfer
public import CFSG.RankThree.PartOne.Q1327T.Weyl
public import CFSG.RankThree.PartOne.N143.SectionListBound
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBDerivedNormalSectionBound
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHeldSmallCorePrimeCore
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalDescentEndpoint
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFiveStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalFixedTransfer
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointActionModels
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalPointPlusBorelModel
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalScalarSquareStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixComponentsCover
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalSixModelGeometry
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBOrthogonalTraceZeroCoordinates
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBProjectiveInvolutionStructure
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBField
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticBLinear
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBSymplecticRepresentationOdd
public import CFSG.LocalAnalysis.ComponentClassification.PSL3FourInvolutions
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSpExclusion
public import CFSG.LocalAnalysis.ComponentInitial.OrthogonalStandardFormsRegular
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartOne.K1320.L4CentT8
public import CFSG.RankThree.PartOne.K1320.L4Sl3
public import CFSG.RankThree.PartOne.KF.ClsPSLBig
public import CFSG.RankThree.PartOne.KF.F132Row7
public import CFSG.RankThree.PartOne.KFOUT3.Cocycle
public import CFSG.RankThree.PartOne.N143X.KF64WSimple
public import CFSG.RankThree.PartOne.Q1327T.Pair
public import CFSG.RankThree.PartOne.S12.InputsSec15
public import CFSG.RankThree.PartOne.S12.Sec136Pair
public import CFSG.RankThree.PartOne.S12.Sec136Setup
public import CFSG.RankThree.PartOne.S12.Sec15FA
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.RankThree.PartOne.U4F.Main
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.RankThree.PartOne.Q1327T

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.Q1327
  CFSG.RankThree.PartOne.K1320 CFSG.RankThree.PartOne.K1327
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)
open CFSG.LocalAnalysis.ComponentInitial (SchreierFor)

variable {G : Type} [Group G] [Finite G]

structure PairN (p f : ℕ) (E R : Subgroup G) (s t : MulAut E) (a : G)
    (N P : Subgroup G) : Prop where
  a_mem : a ∈ E
  a_ne : a ≠ 1
  a_pow : a ^ p = 1
  N_le : N ≤ Subgroup.centralizer (({a} : Set G) ∪ (R : Set G))
  N_mem : N.subgroupOf (Subgroup.centralizer (({a} : Set G) ∪ (R : Set G))) ∈
    thetaComponents p ↥(Subgroup.centralizer (({a} : Set G) ∪ (R : Set G)))
  a_cent : ∀ n ∈ N, a * n = n * a
  Ks_le : kZero p E s ≤ N
  s_mem : s ∈ torusImage E N
  t_mem : t ∈ torusImage E N
  P_le : P ≤ N
  P_le_E : P ≤ E
  P_elem : IsElementaryAbelian p ↥P
  P_card : Nat.card P = p ^ 2
  E_eq : E = Subgroup.zpowers a ⊔ P
  a_not_P : a ∉ P
  conf : Row8Conf p f (↥N ⧸ aschbacherSolvableCore p ↥N)
    ((P.subgroupOf N).map (QuotientGroup.mk' (aschbacherSolvableCore p ↥N)))

variable {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G} {f r : ℕ} {R : Subgroup G}
  {s s' zs : MulAut E}

theorem exists_pairN (hS : SchreierFor InCatalog) (hSLB : N143.SectionListBound)
    (H : Hyp G p A c L E f r R s s' zs) {t : MulAut E} (ht : t ∈ clsOf p E s) {v : E}
    (hv1 : v ≠ 1) (hsv : s v = v) (htv : t v = v) (hnc : s * t ≠ t * s)
    (hcardP : Nat.card ↥(autMoved E s ⊔ autMoved E t) = p ^ 2)
    (hvP : v ∉ autMoved E s ⊔ autMoved E t) :
    ∃ N P : Subgroup G, PairN p f E R s t (v : G) N P := by
  classical
  have h := H.h12
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hcard : Nat.card E = p ^ 3 := by rw [H.hEA]; exact h.A_card
  have hd := RefFacts.ElemData.of_isElementaryAbelian hp hp2 h.E_elem
  have hcls : s ∈ clsOf p E s := mem_clsOf_self p E s
  obtain ⟨hsR, hKs, -, -⟩ := class_facts H (Or.inl rfl) hcls
  obtain ⟨htR, hKt, -, -⟩ := class_facts H (Or.inl rfl) ht
  have hsr : IsAutReflection p E s := hsR.1
  obtain ⟨c₀', x', hc₀1, hc₀P, hc₀fix, hx, hx1, hPgen, hFixgen, hEtop⟩ :=
    pair_geometry hd hcard hsr hv1 hsv hcardP hvP
  obtain ⟨N, hNle, hNmem, hKsN, hKtN⟩ := exists_N hS H ht hsv htv hnc
  set a : G := (v : G) with ha
  have haE : a ∈ E := v.2
  set P : Subgroup G := (autMoved E s ⊔ autMoved E t).map E.subtype with hP
  have hPE : P ≤ E := Subgroup.map_subtype_le _
  have hPel : IsElementaryAbelian p ↥P := isElementaryAbelian_of_le' h.E_elem hPE
  have hPcard : Nat.card P = p ^ 2 := by
    rw [hP, Subgroup.card_map_of_injective E.subtype_injective, hcardP]
  have hPeq : P = autMovedInG E s ⊔ autMovedInG E t := by
    rw [hP, Subgroup.map_sup]
    rfl
  have hPN : P ≤ N := by
    rw [hPeq]
    exact sup_le (hKs.2.2.2.1.trans hKsN) (hKt.2.2.2.1.trans hKtN)
  have hEeq : E = Subgroup.zpowers a ⊔ P := by
    have h2 := congrArg (Subgroup.map E.subtype) hEtop
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h2
    exact h2.symm
  have haNot : a ∉ P := by
    rintro ⟨y, hy, hya⟩
    exact hvP (by rwa [show y = v from Subtype.ext hya] at hy)
  have hao : a ^ p = 1 := Sec12Three.pow_eq_one_of_mem_E h haE
  have haN : ∀ n ∈ N, a * n = n * a := fun n hn =>
    Subgroup.mem_centralizer_iff.1 (hNle hn) a (Or.inl rfl)
  have ha1 : a ≠ 1 := fun h1 => hv1 (Subtype.ext h1)
  set c₀ : G := (c₀' : G) with hc₀def
  set x : G := (x' : G) with hxdef
  have hc₀P' : c₀ ∈ P := ⟨c₀', hc₀P, rfl⟩
  have hc₀1' : c₀ ≠ 1 := fun h1 => hc₀1 (Subtype.ext h1)
  have hxL : x ∈ autMovedInG E s := ⟨x', hx, rfl⟩
  have hxK : x ∈ kZero p E s := hKs.2.2.2.1 hxL
  have hxP : x ∈ P := by
    rw [hPeq]
    exact Subgroup.mem_sup_left hxL
  have hxo : orderOf x = p := by
    rw [hxdef, Subgroup.orderOf_coe]
    exact orderOf_eq_of_ne_one hd hx1
  have hPgen' : P = Subgroup.zpowers c₀ ⊔ Subgroup.zpowers x := by
    rw [hP, hPgen, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hc₀fixG : c₀ ∈ autFixedInG E s := ⟨c₀', hc₀fix, rfl⟩
  have hKc : kZero p E s ≤ Subgroup.centralizer ({c₀} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    rintro y rfl
    exact Subgroup.mem_centralizer_iff.1 (kZero_le_centralizer_fixed p E s hk) c₀ hc₀fixG
  have hKnorm : ((kZero p E s).subgroupOf (N ⊓ Subgroup.centralizer ({c₀} : Set G))).Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    have hgN : (g : G) ∈ N := (Subgroup.mem_inf.1 g.2).1
    have hgc : (g : G) ∈ Subgroup.centralizer ({c₀} : Set G) := (Subgroup.mem_inf.1 g.2).2
    have hfix : autFixedInG E s ≤ Subgroup.centralizer ({(g : G)} : Set G) := by
      have h1 : autFixedInG E s = Subgroup.zpowers a ⊔ Subgroup.zpowers c₀ := by
        rw [autFixedInG, hFixgen, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
        rfl
      rw [h1]
      refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact haN _ hgN
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_singleton_iff.1 hgc).symm
    have hgC : (g : G) ∈ Subgroup.centralizer (autFixedInG E s : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.1 (hfix hy)
    exact kZero_conj_mem hgC hk
  have hEmax : ∀ F : Subgroup G, IsElementaryAbelian p ↥F → F ≤ Subgroup.centralizer (E : Set G) →
      E ≤ F → F = E := fun F hF hFC hEF => by
    rw [H.hEA] at hFC
    exact h.E_max F hF hFC hEF
  set M' : Subgroup G := Subgroup.centralizer (({a} : Set G) ∪ (R : Set G)) with hM'
  have hMne : M' ≠ ⊤ := by
    have hMM : M' ≤ Subgroup.centralizer (R : Set G) := by
      rw [hM', centralizer_union_eq]
      exact inf_le_left
    exact ne_top_of_le_ne_top (centralizer_R_ne_top H) hMM
  let e1 := Subgroup.subgroupOfEquivOfLe hNle
  have hQ : CFSG.IsQuasisimple (↥N ⧸ aschbacherSolvableCore p ↥N) :=
    LocalCores.isQuasisimple_of_mulEquiv
      (QuotientGroup.congr _ _ e1 (aschbacherSolvableCore_map_mulEquiv hp e1)) hNmem.2.2
  have hK : CFSG.IsKGroup ↥M' := h.setup.2.2.1 M' hMne
  have he : CFSG.Assembly.evenRank ↥M' ≤ 3 :=
    (CFSG.RankThree.PartOne.Sec9A.evenRank_subgroup_le _).trans h.evenRank_eq.le
  have hList : Census3.TheoremThreeList
      ((↥N ⧸ aschbacherSolvableCore p ↥N) ⧸ Subgroup.center (↥N ⧸ aschbacherSolvableCore p ↥N)) :=
    (hSLB.listHyp hK he (N.subgroupOf M') hQ
      ((QuotientGroup.mk' (aschbacherSolvableCore p ↥N)).comp e1.toMonoidHom)
      ((QuotientGroup.mk'_surjective _).comp e1.surjective)).onList
  have hconf := row8Conf_of_data hp hp5 H.hf2 H.hpf hQ hList haN hao hPN hPel hPcard hEeq hEmax
    hc₀P' hc₀1' hKsN hKc hKnorm hKs.2.1 hxK hxP hxo hPgen'
  refine ⟨N, P, ⟨haE, ha1, hao, hNle, hNmem, haN, hKsN, ?_, ?_, hPN, hPE, hPel, hPcard, hEeq,
    haNot, hconf⟩⟩
  · obtain ⟨-, -, -, -, k, hk, hkK, hks⟩ := hKs
    exact Sec12Three.mem_torusImage_iff.2 ⟨k, hKsN hkK, hk, hks⟩
  · obtain ⟨-, -, -, -, k, hk, hkK, hkt⟩ := hKt
    exact Sec12Three.mem_torusImage_iff.2 ⟨k, hKtN hkK, hk, hkt⟩

end CFSG.RankThree.PartOne.Q1327T
