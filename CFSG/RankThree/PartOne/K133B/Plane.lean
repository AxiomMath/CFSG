module

public import CFSG.RankThree.PartOne.K133B.Pair
public import CFSG.RankThree.PartOne.K133B.Defs
public import CFSG.RankThree.PartOne.Q1327T.Transfer
public import CFSG.RankThree.PartOne.Q1327T.Weyl
public import CFSG.RankThree.PartOne.K1320.Pair
public import CFSG.RankThree.PartOne.K1320X.CommDistinctX
public import CFSG.RankThree.PartOne.S13K.ThetaFixed
public import CFSG.RankThree.PartOne.S12.Facts13
public import CFSG.RankThree.PartOne.N143.SectionListConsumers
import CFSG.GroupTheory.ElementaryAbelianTransport
public import Certificates.Kernel.ThCent.Leaves
public import CFSG.LieType.Chevalley.OddF4CosetDescent
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
public import CFSG.LocalAnalysis.SectionRank.KGroupSectionClosure
public import CFSG.LocalAnalysis.ZStar.BrauerSylowFusion
public import CFSG.LocalAnalysis.ZStar.PrincipalBlockTraceApplication
public import CFSG.RankThree.PartOne.CTP.StrongPSylow
public import CFSG.RankThree.PartOne.K1320.L4CentT8
public import CFSG.RankThree.PartOne.K1320.L4Sl3
public import CFSG.RankThree.PartOne.KF.ClsPSLBig
public import CFSG.RankThree.PartOne.KF.F132Row7
public import CFSG.RankThree.PartOne.KFOUT3.Cocycle
public import CFSG.RankThree.PartOne.N143.SectionCenter
public import CFSG.RankThree.PartOne.N143.SectionReduce
public import CFSG.RankThree.PartOne.S12.Sec136Pair
public import CFSG.RankThree.PartOne.S12.Sec136Setup
public import CFSG.RankThree.PartOne.S12.Sec1511Y2
public import CFSG.RankThree.PartOne.S12.Sec159Defs
public import CFSG.RankThree.PartOne.S12.Sec159FiveDefs
public import CFSG.RankThree.PartOne.S12.Sec15Items
public import CFSG.RankThree.PartOne.U4F.Main
public import CFSG.Sporadic.ThSchreier.AutCore
public import CFSG.ThirdParty.QiuzhenCFSG.BenderSuzuki.External.Isaacs.VII.lemma_7_7
public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.FiniteFieldFixedSubfieldCard
public import TauCeti.LinearAlgebra.Dimension.IsQuadraticExtension
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalBasis
public import TauCeti.LinearAlgebra.QuadraticForm.OrthogonalGroup.LowRank

public section

namespace CFSG.RankThree.PartOne.K133B

open CFSG CFSG.Assembly CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.GroupTheory
  CFSG.RankThree.PartOne CFSG.RankThree.PartOne.S13K CFSG.RankThree.PartOne.K1320X
  CFSG.RankThree.PartOne.Q1327T
open CFSG.Assembly.LowTwoRank (StatedClassicalModel)

theorem isElementaryAbelian_of_le_of {G : Type} [Group G] {p : ℕ} {A K : Subgroup G}
    (hA : IsElementaryAbelian p ↥A) (hKA : K ≤ A) : IsElementaryAbelian p ↥K :=
  CFSG.IsElementaryAbelian.of_le hA hKA

variable {G : Type} [Group G]

theorem kZero_eq_of_beta {p : ℕ} (hp5 : 5 ≤ p) {E : Subgroup G} {t : MulAut E} {K : Subgroup G}
    (hK : IsKt p E t K) {g : ℕ} (hmod : StatedClassicalModel ↥K .PSL 2 2 g)
    (hpg : p ∣ 2 ^ g + 1) : K = kZero p E t := by
  by_cases hex : ∃ f, kExceptional p (kZero p E t) f
  · exfalso
    obtain ⟨f', hf'⟩ := hex
    have hmod' : StatedClassicalModel ↥K .PSL 2 2 f' := (hK.1 f' hf').2.1
    have hfg : f' = g := K1320.psl_two_degree_eq hmod' hmod
    have hpf : p ∣ 2 ^ g - 1 := hfg ▸ hf'.2.1
    have h1 : 1 ≤ 2 ^ g := Nat.one_le_two_pow
    have h2 : p ∣ (2 ^ g - 1) + 2 := by
      have : (2 ^ g - 1) + 2 = 2 ^ g + 1 := by omega
      rw [this]
      exact hpg
    have h3 : p ∣ 2 := (Nat.dvd_add_right hpf).1 h2
    have := Nat.le_of_dvd (by norm_num) h3
    omega
  · exact hK.2 hex

variable [Finite G]

structure PlaneData (p g : ℕ) (E : Subgroup G) (e : G) (I P : Subgroup G) : Prop where
  e_mem : e ∈ E
  e_ne : e ≠ 1
  e_pow : e ^ p = 1
  e_cent : ∀ n ∈ I, e * n = n * e
  P_le_I : P ≤ I
  P_le_E : P ≤ E
  P_elem : IsElementaryAbelian p ↥P
  P_card : Nat.card P = p ^ 2
  E_eq : E = Subgroup.zpowers e ⊔ P
  e_not_P : e ∉ P
  E_plane : ∃ (PE : Subgroup E) (v : E), (v : G) = e ∧ PE.map E.subtype = P ∧
    Nat.card PE = p ^ 2 ∧ v ∉ PE ∧ Subgroup.zpowers v ⊔ PE = ⊤
  conf : Row8Conf p g (↥I ⧸ aschbacherSolvableCore p ↥I)
    ((P.subgroupOf I).map (QuotientGroup.mk' (aschbacherSolvableCore p ↥I)))

variable {p : ℕ} {A : Subgroup G} {c : G} {L E : Subgroup G}

theorem planeData_of_geometry (hSLB : N143.SectionListBound) (h : Sec12Hyp G p A c L E)
    (hEA : E = A) {t : MulAut E} {K : Subgroup G} (hK : KtLift p E t K) {g : ℕ}
    (hmod : StatedClassicalModel ↥K .PSL 2 2 g) (hpg : p ∣ 2 ^ g + 1) {e : G} (he1 : e ≠ 1)
    {I : Subgroup G} (hI : I ∈ thetaComponentsAt p e) (hKI : K ≤ I) {v : E}
    (hveE : (v : G) = e) {Pe : Subgroup E} {c₀' x' : E} (hc₀1 : c₀' ≠ 1) (hc₀fix : t c₀' = c₀')
    (hx : x' ∈ autMoved E t) (hx1 : x' ≠ 1) (hcardP : Nat.card Pe = p ^ 2)
    (hPgen : Pe = Subgroup.zpowers c₀' ⊔ Subgroup.zpowers x')
    (hFixgen : autFixed E t = Subgroup.zpowers v ⊔ Subgroup.zpowers c₀') (hvP : v ∉ Pe)
    (hEtop : Subgroup.zpowers v ⊔ Pe = ⊤) (hPI : Pe.map E.subtype ≤ I) :
    ∃ P : Subgroup G, PlaneData p g E e I P := by
  classical
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have hg2 : 2 ≤ g := by
    by_contra hg
    have hg' : g = 0 ∨ g = 1 := by omega
    rcases hg' with rfl | rfl
    · have := Nat.le_of_dvd (by norm_num) hpg
      omega
    · have := Nat.le_of_dvd (by norm_num) hpg
      omega
  have hKz : K = kZero p E t := kZero_eq_of_beta hp5 hK.1 hmod hpg
  have hv1 : v ≠ 1 := fun h1 => he1 (by rw [← hveE, h1]; rfl)
  have heE : e ∈ E := hveE ▸ v.2
  set P : Subgroup G := Pe.map E.subtype with hP
  have hPE : P ≤ E := Subgroup.map_subtype_le _
  have hPel : IsElementaryAbelian p ↥P := isElementaryAbelian_of_le_of h.E_elem hPE
  have hPcard : Nat.card P = p ^ 2 := by
    rw [hP, Subgroup.card_map_of_injective E.subtype_injective, hcardP]
  have hEeq : E = Subgroup.zpowers e ⊔ P := by
    have h2 := congrArg (Subgroup.map E.subtype) hEtop
    rw [Subgroup.map_sup, MonoidHom.map_zpowers, ← MonoidHom.range_eq_map,
      Subgroup.range_subtype] at h2
    rw [← hveE]
    exact h2.symm
  have hePnot : e ∉ P := by
    intro hmem
    obtain ⟨y, hy, hye⟩ := Subgroup.mem_map.1 hmem
    have : y = v := Subtype.ext (hye.trans hveE.symm)
    exact hvP (this ▸ hy)
  have hao : e ^ p = 1 := Sec12Three.pow_eq_one_of_mem_E h heE
  obtain ⟨hIC, -⟩ := mem_thetaComponentsAt_iff.1 hI
  have heI : ∀ n ∈ I, e * n = n * e := fun n hn =>
    Subgroup.mem_centralizer_iff.1 (hIC hn) e rfl
  have hd := RefFacts.ElemData.of_isElementaryAbelian hp (by omega) h.E_elem
  set c₀ : G := (c₀' : G) with hc₀def
  set x : G := (x' : G) with hxdef
  have hc₀P : c₀' ∈ Pe := by
    rw [hPgen]
    exact Subgroup.mem_sup_left (Subgroup.mem_zpowers c₀')
  have hc₀P' : c₀ ∈ P := ⟨c₀', hc₀P, rfl⟩
  have hc₀1' : c₀ ≠ 1 := fun h1 => hc₀1 (Subtype.ext h1)
  have hxL : x ∈ autMovedInG E t := ⟨x', hx, rfl⟩
  have hxK : x ∈ K := hK.2.2.2.1 hxL
  have hxP : x ∈ P := by
    refine ⟨x', ?_, rfl⟩
    rw [hPgen]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers x')
  have hxo : orderOf x = p := by
    rw [hxdef, Subgroup.orderOf_coe]
    exact Q1327T.orderOf_eq_of_ne_one hd hx1
  have hPgen' : P = Subgroup.zpowers c₀ ⊔ Subgroup.zpowers x := by
    rw [hP, hPgen, Subgroup.map_sup, MonoidHom.map_zpowers, MonoidHom.map_zpowers]
    rfl
  have hc₀fixG : c₀ ∈ autFixedInG E t := ⟨c₀', hc₀fix, rfl⟩
  have hKc : K ≤ Subgroup.centralizer ({c₀} : Set G) := by
    intro k hk
    rw [Subgroup.mem_centralizer_iff]
    rintro y rfl
    have hk' : k ∈ kZero p E t := hKz ▸ hk
    exact Subgroup.mem_centralizer_iff.1 (kZero_le_centralizer_fixed p E t hk') c₀ hc₀fixG
  have hKnorm0 :
      ((kZero p E t).subgroupOf (I ⊓ Subgroup.centralizer ({c₀} : Set G))).Normal := by
    refine ⟨fun k hk g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hk ⊢
    have hgN : (g : G) ∈ I := (Subgroup.mem_inf.1 g.2).1
    have hgc : (g : G) ∈ Subgroup.centralizer ({c₀} : Set G) := (Subgroup.mem_inf.1 g.2).2
    have hfix : autFixedInG E t ≤ Subgroup.centralizer ({(g : G)} : Set G) := by
      have h1 : autFixedInG E t = Subgroup.zpowers (v : G) ⊔ Subgroup.zpowers c₀ := by
        rw [autFixedInG, hFixgen, Subgroup.map_sup, MonoidHom.map_zpowers,
          MonoidHom.map_zpowers]
        rfl
      rw [h1, hveE]
      refine sup_le (Subgroup.zpowers_le.2 ?_) (Subgroup.zpowers_le.2 ?_)
      · rw [Subgroup.mem_centralizer_singleton_iff]
        exact heI _ hgN
      · exact Subgroup.mem_centralizer_singleton_iff.2
          (Subgroup.mem_centralizer_singleton_iff.1 hgc).symm
    have hgC : (g : G) ∈ Subgroup.centralizer (autFixedInG E t : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro y hy
      exact Subgroup.mem_centralizer_singleton_iff.1 (hfix hy)
    exact kZero_conj_mem hgC hk
  have hKnorm : (K.subgroupOf (I ⊓ Subgroup.centralizer ({c₀} : Set G))).Normal :=
    hKz ▸ hKnorm0
  have hEmax : ∀ F : Subgroup G, IsElementaryAbelian p ↥F → F ≤ Subgroup.centralizer (E : Set G) →
      E ≤ F → F = E := fun F hF hFC hEF => by
    rw [hEA] at hFC
    exact h.E_max F hF hFC hEF
  obtain ⟨hsimp, hnonab, hKP, -, he3, -⟩ := h.setup
  have := hsimp
  have hItop : I ≠ ⊤ := by
    intro htop
    exact EmbeddingFixedResidual.centralizer_ne_top_of_simple hnonab he1
      (eq_top_iff.2 (htop ▸ hIC))
  have hQ : CFSG.IsQuasisimple (↥I ⧸ aschbacherSolvableCore p ↥I) :=
    isQuasisimple_thetaQuotient_of_mem_thetaComponentsAt hp hI
  have hList : Census3.TheoremThreeList
      ((↥I ⧸ aschbacherSolvableCore p ↥I) ⧸ Subgroup.center (↥I ⧸ aschbacherSolvableCore p ↥I)) :=
    (N143.theoremThreeListHyp_simpleQuot_of_mem_thetaComponentsAt hSLB hKP he3.le hp hI
      hItop).onList
  have hconf := row8Conf_of_data hp hp5 hg2 hpg hQ hList heI hao hPI hPel hPcard hEeq hEmax
    hc₀P' hc₀1' hKI hKc hKnorm hmod hxK hxP hxo hPgen'
  exact ⟨P, ⟨heE, he1, hao, heI, hPI, hPE, hPel, hPcard, hEeq, hePnot,
    ⟨Pe, v, hveE, rfl, hcardP, hvP, hEtop⟩, hconf⟩⟩

theorem exists_planeData (hSLB : N143.SectionListBound) (h : Sec12Hyp G p A c L E)
    (hEA : E = A) (hnt : ¬ torusHasTransvection p E) {t s : MulAut E}
    (htr : IsAutReflection p E t) (hsr : IsAutReflection p E s) (htw : t ∈ torusWeyl E)
    (hsw : s ∈ torusWeyl E) (hts : t * s ≠ s * t) {K Ks : Subgroup G} (hK : KtLift p E t K)
    (hKs : KtLift p E s Ks) {g : ℕ} (hmod : StatedClassicalModel ↥K .PSL 2 2 g)
    (hpg : p ∣ 2 ^ g + 1) {e : G} (he1 : e ≠ 1) (hetE : e ∈ autFixedInG E t)
    {I : Subgroup G} (hI : I ∈ thetaComponentsAt p e)
    (hKI : K ≤ I) (hKsI : Ks ≤ I) (heP : e ∉ autMovedInG E t ⊔ autMovedInG E s) :
    ∃ P : Subgroup G, PlaneData p g E e I P := by
  classical
  have hp := h.prime
  have hp5 := Sec12Three.five_le h
  have hp2 : p ≠ 2 := by omega
  have hcard : Nat.card E = p ^ 3 := by rw [hEA]; exact h.A_card
  have hd := RefFacts.ElemData.of_isElementaryAbelian hp hp2 h.E_elem
  have hnt' : ¬ IsAutTransvection p E (t * s) := fun hT => hnt ⟨t * s, mul_mem htw hsw, hT⟩
  have hne : autMoved E t ≠ autMoved E s := autMoved_ne_of_noncomm hd htr hsr hts hnt'
  have hcardP : Nat.card ↥(autMoved E t ⊔ autMoved E s) = p ^ 2 :=
    card_sup_autMoved_eq hd htr hsr hne
  obtain ⟨v, hv, hve⟩ := Subgroup.mem_map.1 hetE
  have hvt : t v = v := hv
  have hveE : (v : G) = e := hve
  have hv1 : v ≠ 1 := fun h1 => he1 (by rw [← hveE, h1]; rfl)
  have hvP : v ∉ autMoved E t ⊔ autMoved E s := by
    intro hvP
    apply heP
    rw [← hveE]
    have : (v : G) ∈ (autMoved E t ⊔ autMoved E s).map E.subtype := ⟨v, hvP, rfl⟩
    rwa [Subgroup.map_sup] at this
  obtain ⟨c₀', x', hc₀1, -, hc₀fix, hx, hx1, hPgen, hFixgen, hEtop⟩ :=
    Q1327T.pair_geometry hd hcard htr hv1 hvt hcardP hvP
  have hPeq : (autMoved E t ⊔ autMoved E s).map E.subtype = autMovedInG E t ⊔ autMovedInG E s := by
    rw [Subgroup.map_sup]
    rfl
  have hPI : (autMoved E t ⊔ autMoved E s).map E.subtype ≤ I := by
    rw [hPeq]
    exact sup_le (hK.2.2.2.1.trans hKI) (hKs.2.2.2.1.trans hKsI)
  exact planeData_of_geometry hSLB h hEA hK hmod hpg he1 hI hKI hveE hc₀1 hc₀fix hx hx1 hcardP
    hPgen hFixgen hvP hEtop hPI

end CFSG.RankThree.PartOne.K133B
