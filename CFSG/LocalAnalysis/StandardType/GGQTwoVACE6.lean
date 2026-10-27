module

public import CFSG.LocalAnalysis.StandardType.GGQTwoVACSplit
public import CFSG.LocalAnalysis.StandardType.GGQTwoVACLinClass
public import CFSG.LocalAnalysis.StandardType.GGR4Forced
public import CFSG.LocalAnalysis.StandardType.GGHalfRowData
public import CFSG.LocalAnalysis.StandardType.GGTwistedLabelModels
public import CFSG.HardMathSupport.Foote.E27.LieTwo.OrthModel
public import CFSG.LocalAnalysis.StandardType.GGQTwoFullExclusions
public import CFSG.LocalAnalysis.StandardType.GGE6TwoCenter
public import CFSG.LocalAnalysis.StandardType.GGE6TwoLocalRank
public import CFSG.LocalAnalysis.StandardType.GGSecFiveSplitNbrSmallRank
public import CFSG.LocalAnalysis.StandardType.GGTableBTransport
public import CFSG.Blueprint.ChevalleyRootArtifact
public import CFSG.LocalAnalysis.StandardType.GGTableBExcE6ThreeTwoTorus
public import CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.D44
public import CFSG.LocalAnalysis.StandardType.GGTableBE6TwoPilotToral
public import CFSG.LocalAnalysis.StandardType.GGE6OppConjDatum
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetTransport
public import CFSG.LocalAnalysis.StandardType.GGTableBNbrInnerMoreCore
public import CFSG.GroupTheory.SupCommute
public import CFSG.LocalAnalysis.StandardType.GGR4JMeetNoL34
public import CFSG.LocalAnalysis.StandardType.GGE6OppOrderThreeLayer
public import CFSG.LocalAnalysis.StandardType.GGTorDNsFrame
public import CFSG.LocalAnalysis.RankThreeTheoremC.AGL81TwelveNotLeGraphSymCore
public import Certificates.Certificate1953
public import Certificates.Certificate1954

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly CFSG.LieType.Chevalley CFSG.Blueprint.Chevalley TableBExc.E6Three

theorem ggQTwoE6_center_bot :
    GGE6TwoCenterBot :=
  ggE6TwoCenterBot_holds

theorem ggQTwoE6_localRank_ge_five_of_witness {G : Type} [Group G] [Finite G] {x : G}
    {L : Subgroup G} {P E : Subgroup ↥L}
    (hPne : P ≠ ⊥) (hP2 : IsPGroup 2 P)
    (hEN : E ≤ Subgroup.normalizer (P : Set ↥L)) (hEelem : IsElemAbelian 3 E)
    (hEcard : Nat.card E = 3 ^ CFSG.Open.pRank 3 (Subgroup.normalizer (P : Set ↥L)))
    (hPrank : 4 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (P : Set ↥L)))
    (hxL : x ∉ L) (hx3 : x ^ 3 = 1) (hxc : ∀ l ∈ L, x * l = l * x) :
    5 ≤ LargeEvenTwoLocalRank 3 G := by
  classical
  let E' : Subgroup G := E.map L.subtype
  let P' : Subgroup G := P.map L.subtype
  have hE'elem : IsElemAbelian 3 E' := hEelem.map L.subtype
  have hE'card : Nat.card E' = 3 ^ CFSG.Open.pRank 3 (Subgroup.normalizer (P : Set ↥L)) := by
    rw [Subgroup.card_map_of_injective L.subtype_injective, hEcard]
  have hP'ne : P' ≠ ⊥ := by
    intro h
    exact hPne ((Subgroup.map_eq_bot_iff_of_injective (f := L.subtype) P
      L.subtype_injective).mp h)
  have hP'2 : IsPGroup 2 P' := hP2.map L.subtype
  have hE'N : E' ≤ Subgroup.normalizer (P' : Set G) := by
    calc E' = E.map L.subtype := rfl
      _ ≤ (Subgroup.normalizer (P : Set ↥L)).map L.subtype := Subgroup.map_mono hEN
      _ ≤ Subgroup.normalizer (P.map L.subtype) := Subgroup.le_normalizer_map L.subtype
  by_cases hk : 5 ≤ CFSG.Open.pRank 3 (Subgroup.normalizer (P : Set ↥L))
  · exact hk.trans (le_twoLocalRank_of_normalizes Nat.prime_three hP'ne hP'2 hE'elem hE'N
      hE'card)
  · have hk4 : CFSG.Open.pRank 3 (Subgroup.normalizer (P : Set ↥L)) = 4 := by omega
    have hxE' : x ∉ E' := fun h => hxL (Subgroup.map_subtype_le E h)
    have hcommx : ∀ e ∈ E', e * x = x * e :=
      fun e he => (hxc e (Subgroup.map_subtype_le E he)).symm
    have hE'x_elem : IsElemAbelian 3 (E' ⊔ Subgroup.zpowers x) :=
      (isElemAbelian_sup_zpowers_of_card Nat.prime_three hE'elem hE'card hx3 hxE' hcommx).1
    have hE'x_card : Nat.card ↥(E' ⊔ Subgroup.zpowers x) = 3 ^ 5 := by
      rw [(isElemAbelian_sup_zpowers_of_card Nat.prime_three hE'elem hE'card hx3 hxE'
        hcommx).2, hk4]
    have hE'xN : E' ⊔ Subgroup.zpowers x ≤ Subgroup.normalizer (P' : Set G) := by
      apply sup_le hE'N
      rw [Subgroup.zpowers_le]
      exact Subgroup.centralizer_le_normalizer _ (fun p hp =>
        (hxc p (Subgroup.map_subtype_le P hp)).symm)
    exact le_twoLocalRank_of_normalizes Nat.prime_three hP'ne hP'2 hE'x_elem hE'xN hE'x_card

theorem ggQTwoE6_localRank_ge_five_of_has
    {G : Type} [Group G] [Finite G] {x : G} {L : Subgroup G}
    (hperf : commutator L = ⊤)
    (hHas : GGHasLabel ⟨.E6, 0, 1⟩ (L ⧸ Subgroup.center L))
    (hxL : x ∉ L) (hx3 : x ^ 3 = 1) (hxc : ∀ l ∈ L, x * l = l * x) :
    5 ≤ LargeEvenTwoLocalRank 3 G := by
  have h4 : 4 ≤ LargeEvenTwoLocalRank 3 ↥L := ggE6TwoLocalRankThree_holds L hperf hHas
  have h4' : 4 ≤ CFSG.Open.GLATwoLocalRank 3 ↥L := h4
  obtain ⟨P, hPne, hP2, hPrank⟩ :=
    CFSG.HardMathSupport.Solomon.Coordinator.ChevQ.exists_twoLocal_of_le
      (p := 3) (by norm_num) (n := 4) (by norm_num) h4'
  obtain ⟨E, hEN, hEelem, hEcard⟩ :=
    CFSG.SectionRank.exists_pRank (p := 3) (by norm_num)
      (Subgroup.normalizer (P : Set ↥L))
  exact ggQTwoE6_localRank_ge_five_of_witness hPne hP2 hEN hEelem hEcard hPrank hxL hx3 hxc

theorem ggQTwoE6_localRank_ge_five
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    5 ≤ LargeEvenTwoLocalRank 3 G := by
  obtain ⟨labM, hlabM, hHasM, R, hR, I, F, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hmark
  have hperf : commutator L = ⊤ := hmark.1
  have hlabEq : labM = lab := hP.1
  have htagM : labM.tag = .E6 := by rw [hlabEq]; exact htag
  have hn1 : labM.n = 1 := by
    have hlt : labM.n < 2 := by rw [hlabEq]; exact hq2
    have hn : 1 ≤ labM.n := hlabM.1
    omega
  have hrank0 : labM.rank = 0 := by
    have h := hlabM.2
    rw [htagM] at h
    simpa using h
  have hlabE6 : labM = ⟨.E6, 0, 1⟩ := by
    cases labM
    simp_all
  have hHas : GGHasLabel ⟨.E6, 0, 1⟩ (L ⧸ Subgroup.center L) := by
    rwa [hlabE6] at hHasM
  have hx1 : x ≠ 1 := hS.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hBmax : LargeEvenIsBmax 3 B := hS.1.1.1.2.2.2.2.2.2.1.1
  have hxB : x ∈ B := hS.1.1.1.2.2.2.2.2.2.1.2.1
  have hx3 : x ^ 3 = 1 := hBmax.1.2 x hxB
  have hcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    hS.1.1.1.2.2.2.2.2.2.1.2.2.2.1
  have hxc : ∀ l ∈ L, x * l = l * x := by
    intro l hl
    have h : l ∈ Subgroup.centralizer ({x} : Set G) := hcomp.1 hl
    rw [Subgroup.mem_centralizer_singleton_iff] at h; exact h.symm
  have hxL : x ∉ L := by
    have hZ : Subgroup.center ↥L = ⊥ := ggQTwoE6_center_bot L hperf hHas
    intro hxLmem
    have hxZ : (⟨x, hxLmem⟩ : ↥L) ∈ Subgroup.center ↥L := by
      rw [Subgroup.mem_center_iff]
      intro l
      exact Subtype.ext (hxc l l.property).symm
    rw [hZ] at hxZ; exact hx1 (congrArg Subtype.val (Subgroup.mem_bot.mp hxZ))
  exact ggQTwoE6_localRank_ge_five_of_has hperf hHas hxL hx3 hxc

theorem ggQTwoE6_beta_image_lift
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    ∃ (K : Type) (_ : Field K) (_ : Finite K) (_ : Nat.card K = 2)
      (_I : Set (MulAut (TableBExc.RecipeGroup .E6 K)))
      (θ : L ⧸ Subgroup.center L ≃* TableBExc.RecipeGroup .E6 K)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G)),
      IsElemAbelian 3 (ggBeta L θ hN).range ∧
        ∃ A : Subgroup (TableBExc.RecipeGroup .E6 K), IsElemAbelian 3 A ∧
          Nat.card A = Nat.card (ggBeta L θ hN).range := by
  classical
  obtain ⟨-, labM, hlabM, hrawM⟩ := hmark
  obtain ⟨-, -, -, -, -, -, -, hlabEq, -, -⟩ := largeEvenRawDatum_exists hrawM
  have hn1 : labM.n = 1 := by
    have hlt : labM.n < 2 := by rw [hlabEq]; exact hq2
    have hn : 1 ≤ labM.n := hlabM.1
    omega
  have htagM : labM.tag = .E6 := by rw [hlabEq]; exact htag
  rw [LargeEvenRawDatumLegacy, htagM] at hrawM
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hrawM
  let : Field K := hfield
  let : Finite K := hfinite
  have hK2 : Nat.card K = 2 := by rw [hK, hn1]; norm_num
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK2, pow_one])
  obtain ⟨-, -, θ, -, hN, hI⟩ := hQ
  let θ' : L ⧸ Subgroup.center L ≃* TableBExc.RecipeGroup .E6 K := θ
  let E : Subgroup (MulAut (TableBExc.RecipeGroup .E6 K)) := (ggBeta L θ' hN).range
  have hBs : IsElemAbelian 3 Bs := hcfg.2.1.2.1
  have hE : IsElemAbelian 3 E :=
    isElemAbelian_range (fun a b => hBs.1.is_comm.comm a b)
      (fun b => Subtype.ext (hBs.2 b b.property)) (ggBeta L θ' hN)
  have hEI : (E : Set (MulAut (TableBExc.RecipeGroup .E6 K))) ⊆
      Set.range (MulAut.conj : TableBExc.RecipeGroup .E6 K →* _) := by
    intro φ hφ
    obtain ⟨b, -, rfl⟩ := hφ
    exact TableBExc.E6Three.recipeID_subset_inn_E6_two hK2 (ggBeta_mem L θ' hN hI b)
  have : Finite (TableBExc.RecipeGroup .E6 K) := TableBExc.finite_recipeGroup .E6 K
  obtain ⟨A, hA, hAcard⟩ := TableBSymp.exists_of_subset_inn
    (TableBExc.center_recipeGroup_eq_bot .E6 K) hEI hE
  exact ⟨K, hfield, hfinite, hK2,
    LargeEvenChevIDImage (LargeEvenCartanE 6) K
      (LargeEvenChevH (LargeEvenCartanE 6) K false), θ', hN, hE, A, hA, hAcard⟩

theorem ggQTwoE6_beta_image_transport
    {K : Type} [Field K] [Finite K]
    (A : Subgroup (TableBExc.RecipeGroup .E6 K)) (hA : IsElemAbelian 3 A) :
    ∃ A' : Subgroup ↥(adjointGroup .E6 K), IsElemAbelian 3 A' ∧ Nat.card A' = Nat.card A := by
  let eR : TableBExc.RecipeGroup .E6 K ≃* ↥(adjointGroup .E6 K) := TableBExc.recipeEquiv .E6 K
  exact ⟨A.map eR.toMonoidHom, hA.map eR.toMonoidHom,
    Subgroup.card_map_of_injective eR.injective⟩

theorem ggQTwoE6_beta_image_card_le_torus
    {K : Type} [Field K] [Finite K]
    (hK2 : Nat.card K = 2) {A' : Subgroup ↥(adjointGroup .E6 K)}
    (hA' : IsElemAbelian 3 A') : Nat.card A' ≤ 3 ^ 4 := by
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK2, pow_one])
  have h2 : (2 : K) = 0 := CharTwo.two_eq_zero
  have htorus : Nat.card (torusE6Two (K := K) h2).range = 3 ^ 4 := by
    rw [MonoidHom.range_eq_map,
      Subgroup.card_map_of_injective (TableBExc.E6Three.torusE6Two_injective h2),
      Subgroup.card_top]
    have hcardM : Nat.card (Multiplicative (Fin 4 → ZMod 3)) =
        Nat.card (Fin 4 → ZMod 3) :=
      Nat.card_congr (MulEquiv.funMultiplicative (Fin 4) (ZMod 3)).toEquiv
    rw [hcardM, Nat.card_fun, Nat.card_zmod, Nat.card_fin]
  by_cases h4 : 3 ^ 4 ≤ Nat.card A'
  · obtain ⟨c, hc⟩ := E6TwoPilot.exists_conj_eq_range_torusE6Two h2 hK2 hA' h4
    have hcard : Nat.card A' = 3 ^ 4 := by
      rw [← htorus, ← hc]
      exact (Subgroup.card_map_of_injective (MulAut.conj c).injective).symm
    exact le_of_eq hcard
  · omega

theorem ggQTwoE6_image_card_le_three_pow_four
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    ∃ (R : Type) (_ : Group R) (_I : Set (MulAut R)) (θ : L ⧸ Subgroup.center L ≃* R)
      (hN : Bs ≤ Subgroup.normalizer (L : Set G)),
      Nat.card (ggBeta L θ hN).range ≤ 3 ^ 4 := by
  obtain ⟨K, hfield, hfinite, hK2, _I, θ', hN, hE, A, hA, hAcard⟩ :=
    ggQTwoE6_beta_image_lift hcfg hq2 htag hmark
  let : Field K := hfield
  let : Finite K := hfinite
  obtain ⟨A', hA', hA'card⟩ := ggQTwoE6_beta_image_transport A hA
  have hA'le := ggQTwoE6_beta_image_card_le_torus hK2 hA'
  exact ⟨TableBExc.RecipeGroup .E6 K, inferInstance, _I, θ', hN, by
    rw [← hAcard, ← hA'card]
    exact hA'le⟩

theorem ggQTwoE6_card_Bs_le_three_pow_five
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hcfg : GGConfig 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    Nat.card Bs ≤ 3 ^ 5 := by
  classical
  obtain ⟨R, hR, I, θ, hN, himage⟩ :=
    ggQTwoE6_image_card_le_three_pow_four hcfg hq2 htag hmark
  have hperf : commutator L = ⊤ := hmark.1
  have hSStar : LargeEvenSStar 3 B x L := hcfg.1.2.2.2.2.2.2.1
  have hx1 : x ≠ 1 := hSStar.2.2.1
  have hxB : x ∈ B := hSStar.2.1
  have hcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) := hSStar.2.2.2.1
  have hxLc : x ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcomp.1 hl)
  have hxBs : x ∈ Bs := hcfg.2.1.1 hxB
  have hBs : IsElemAbelian 3 Bs := hcfg.2.1.2.1
  let T : Subgroup G := Bs ⊓ Subgroup.centralizer (L : Set G)
  have hTexp : ∀ t ∈ T, t ^ 3 = 1 :=
    fun t ht => hBs.2 t ht.1
  have hT3 : IsPGroup 3 T := fun t => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hTexp (t : G) t.2)⟩
  have hTcyc : IsCyclic T := hSStar.2.2.2.2 T inf_le_right hT3
  have hcardT : Nat.card T ≤ 3 := by
    obtain ⟨g, hg⟩ := hTcyc.exists_generator
    have hg3 : g ^ 3 = 1 := Subtype.ext (hTexp (g : G) g.2)
    have hdvd : Nat.card T ∣ 3 := by
      rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
      exact orderOf_dvd_of_pow_eq_one hg3
    exact Nat.le_of_dvd (by norm_num) hdvd
  have hTsub : T.subgroupOf Bs = (Subgroup.centralizer (L : Set G)).subgroupOf Bs := by
    ext b
    simp [T, Subgroup.mem_subgroupOf]
  have hIndex : (T.subgroupOf Bs).index ≤ 3 ^ 4 := by
    rw [hTsub, ← QTwoCav.beta_card hperf θ hN]
    exact himage
  have h := (T.subgroupOf Bs).card_mul_index
  have hcard_sub : Nat.card (T.subgroupOf Bs) = Nat.card T :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  rw [hcard_sub] at h
  calc Nat.card Bs = Nat.card T * (T.subgroupOf Bs).index := h.symm
    _ ≤ 3 * 3 ^ 4 := Nat.mul_le_mul hcardT hIndex
    _ = 3 ^ 5 := by norm_num

theorem ggQTwoE6_card_meet_centralizer_L_le_three {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) :
    Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ 3 := by
  have hSStar : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hBs : IsElemAbelian 3 Bs := hS.1.1.2.1.2.1
  let T : Subgroup G := Bs ⊓ Subgroup.centralizer (L : Set G)
  have hTexp : ∀ t ∈ T, t ^ 3 = 1 := fun t ht => hBs.2 t ht.1
  have hT3 : IsPGroup 3 T := fun t => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hTexp (t : G) t.2)⟩
  have hTcyc : IsCyclic T := hSStar.2.2.2.2 T inf_le_right hT3
  obtain ⟨g, hg⟩ := hTcyc.exists_generator
  have hg3 : g ^ 3 = 1 := Subtype.ext (hTexp (g : G) g.2)
  have hdvd : Nat.card T ∣ 3 := by
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact orderOf_dvd_of_pow_eq_one hg3
  exact Nat.le_of_dvd (by norm_num) hdvd

theorem ggQTwoE6_B_eq_Bstar
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    Bs = B := by
  have hcardBs := ggQTwoE6_card_Bs_le_three_pow_five hS.1.1 hq2 htag hmark
  have hBmax : LargeEvenIsBmax 3 B := hS.1.1.1.2.2.2.2.2.2.1.1
  have hcardB : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hBmax.2.1
  have h5 : 5 ≤ LargeEvenTwoLocalRank 3 G :=
    ggQTwoE6_localRank_ge_five hS hq2 htag hmark
  have hB5 : 3 ^ 5 ≤ Nat.card B := by
    rw [hcardB]
    exact Nat.pow_le_pow_right (by norm_num) h5
  have hBBs : B ≤ Bs := hS.1.1.2.1.1
  exact (Subgroup.eq_of_le_of_card_ge hBBs (le_trans hcardBs hB5)).symm

theorem ggQTwoE6_card_Bs
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    Nat.card Bs = 3 ^ 5 := by
  have hB : Bs = B := ggQTwoE6_B_eq_Bstar hS hq2 htag hmark
  have hcardBs := ggQTwoE6_card_Bs_le_three_pow_five hS.1.1 hq2 htag hmark
  have hBmax : LargeEvenIsBmax 3 B := hS.1.1.1.2.2.2.2.2.2.1.1
  have hcardB : Nat.card B = 3 ^ LargeEvenTwoLocalRank 3 G := hBmax.2.1
  have h5 : 5 ≤ LargeEvenTwoLocalRank 3 G :=
    ggQTwoE6_localRank_ge_five hS hq2 htag hmark
  have hB5 : 3 ^ 5 ≤ Nat.card B := by
    rw [hcardB]
    exact Nat.pow_le_pow_right (by norm_num) h5
  rw [hB] at hcardBs ⊢
  exact le_antisymm hcardBs hB5

theorem ggQTwoE6_D_eq {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {z : G}
    (hzD : z ∈ D) (hzx : z ∉ Subgroup.zpowers x) :
    D = Subgroup.zpowers x ⊔ Subgroup.zpowers z := by
  have hSStar : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hDelem : IsElemAbelian 3 D := hS.1.1.2.2.1.2.1
  have hxD : x ∈ D := hS.1.1.2.2.1.2.2.2.1
  have hx1 : x ≠ 1 := hSStar.2.2.1
  have hx3 : x ^ 3 = 1 := hDelem.2 x hxD
  have hz3 : z ^ 3 = 1 := hDelem.2 z hzD
  have hz1 : z ≠ 1 := fun h => hzx (by rw [h]; exact Subgroup.one_mem _)
  have hDcard : Nat.card D = 9 := by
    have := hS.1.1.2.2.1.2.2.1
    rw [this]; norm_num
  have hxord : orderOf (⟨x, hxD⟩ : D) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hx3 hx1
  have hzord : orderOf (⟨z, hzD⟩ : D) = 3 := by
    rw [Subgroup.orderOf_mk]
    exact orderOf_eq_prime hz3 hz1
  have hne : (⟨z, hzD⟩ : D) ∉ Subgroup.zpowers (⟨x, hxD⟩ : D) := by
    intro h
    apply hzx
    rw [Subgroup.mem_zpowers_iff] at h ⊢
    obtain ⟨k, hk⟩ := h
    exact ⟨k, by simpa using congrArg Subtype.val hk⟩
  have htop : Subgroup.zpowers (⟨x, hxD⟩ : D) ⊔ Subgroup.zpowers (⟨z, hzD⟩ : D) = ⊤ :=
    CFSG.LocalAnalysis.RankThreeTheoremC.TwelveNotLe.Sym.zpowers_sup_eq_of_card_nine
      hDcard hxord hzord hne
  have hmap := congrArg (Subgroup.map D.subtype) htop
  simpa [Subgroup.map_sup, Subgroup.map_top, MonoidHom.map_zpowers] using hmap.symm

theorem ggQTwoE6_z_not_central {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {z : G}
    (hzD : z ∈ D) (hzx : z ∉ Subgroup.zpowers x) :
    z ∉ Subgroup.centralizer (L : Set G) := by
  intro hzC
  have hSStar : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hDelem : IsElemAbelian 3 D := hS.1.1.2.2.1.2.1
  have hDgen : D = Subgroup.zpowers x ⊔ Subgroup.zpowers z := ggQTwoE6_D_eq hS hzD hzx
  have hDle : D ≤ Subgroup.centralizer (L : Set G) := by
    rw [hDgen]
    have hxCent : x ∈ Subgroup.centralizer (L : Set G) :=
      Subgroup.mem_centralizer_iff.mpr fun l hl =>
        Subgroup.mem_centralizer_singleton_iff.mp (hSStar.2.2.2.1.1 hl)
    exact sup_le (Subgroup.zpowers_le.mpr hxCent) (Subgroup.zpowers_le.mpr hzC)
  have hD3 : IsPGroup 3 D := fun d => ⟨1, by
    rw [pow_one]
    exact Subtype.ext (hDelem.2 (d : G) d.2)⟩
  have hDcyc : IsCyclic D := hSStar.2.2.2.2 D hDle hD3
  obtain ⟨g, hg⟩ := hDcyc.exists_generator
  have hg3 : g ^ 3 = 1 := Subtype.ext (hDelem.2 (g : G) g.2)
  have hdvd : Nat.card D ∣ 3 := by
    rw [← orderOf_eq_card_of_forall_mem_zpowers hg]
    exact orderOf_dvd_of_pow_eq_one hg3
  have hDcard : Nat.card D = 9 := by
    have := hS.1.1.2.2.1.2.2.1
    rw [this]; norm_num
  have hle : Nat.card D ≤ 3 := Nat.le_of_dvd (by norm_num) hdvd
  omega

theorem pow_three_mul_conj_conj_conj {M : Type*} [Group M] (k l : M) :
    k ^ 3 * (k⁻¹ * (k⁻¹ * (k⁻¹ * l * k) * k) * k) = l * k ^ 3 := by
  group
  simp [pow_three, mul_assoc]

theorem ggQTwoE6_hasLabel_E6
    {G : Type} [Group G] [Finite G] {_B Bs : Subgroup G} {L : Subgroup G}
    {lab : LargeEvenLabel} (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    GGHasLabel ⟨.E6, 0, 1⟩ (L ⧸ Subgroup.center L) := by
  obtain ⟨labM', hlabM', hHasM', R, hR, I, F, θ, hP⟩ :=
    largeEvenMarking_exists_hasLabel hmark
  have hlabEq' : labM' = lab := hP.1
  have htagM' : labM'.tag = .E6 := by rw [hlabEq']; exact htag
  have hn1' : labM'.n = 1 := by
    have hlt : labM'.n < 2 := by rw [hlabEq']; exact hq2
    have hn : 1 ≤ labM'.n := hlabM'.1
    omega
  have hrank0' : labM'.rank = 0 := by
    have h := hlabM'.2
    rw [htagM'] at h
    simpa using h
  have hlabE6' : labM' = ⟨.E6, 0, 1⟩ := by
    cases labM'
    simp_all
  rwa [hlabE6'] at hHasM'

theorem ggQTwoE6_lift_exists_k
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x z : G} {L D J : Subgroup G}
    {lab : LargeEvenLabel}
    (hS : GGQTwoSetting 3 B Bs x L D J)
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hzD : z ∈ D) :
    ∃ k ∈ L, (∀ l ∈ L, z * l * z⁻¹ = k⁻¹ * l * k) ∧ z ^ 3 = 1 ∧
      z ∈ Subgroup.normalizer (L : Set G) := by
  classical
  obtain ⟨hperf, labM, hlabM, hrawM⟩ := hmark
  have hBBs : B ≤ Bs := hS.1.1.2.1.1
  have hDleB : D ≤ B := hS.1.1.2.2.1.1
  have hDelem : IsElemAbelian 3 D := hS.1.1.2.2.1.2.1
  have hzBs : z ∈ Bs := hBBs (hDleB hzD)
  have hz3 : z ^ 3 = 1 := hDelem.2 z hzD
  obtain ⟨-, -, -, -, -, -, -, hlabEq, -, -⟩ := largeEvenRawDatum_exists hrawM
  have hn1 : labM.n = 1 := by
    have hlt : labM.n < 2 := by rw [hlabEq]; exact hq2
    have hn : 1 ≤ labM.n := hlabM.1
    omega
  have htagM : labM.tag = .E6 := by rw [hlabEq]; exact htag
  rw [LargeEvenRawDatumLegacy, htagM] at hrawM
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hrawM
  let : Field K := hfield
  let : Finite K := hfinite
  have hK2 : Nat.card K = 2 := by rw [hK, hn1]; norm_num
  have : CharP K 2 := charP_two_of_card (m := 1) (by rw [hK2, pow_one])
  obtain ⟨-, -, θ, -, hN, hI⟩ := hQ
  let θ' : L ⧸ Subgroup.center L ≃* TableBExc.RecipeGroup .E6 K := θ
  have hzN : z ∈ Subgroup.normalizer (L : Set G) := hN hzBs
  obtain ⟨φ, hφI, hφind⟩ := hI z hzBs
  obtain ⟨r, rfl⟩ := TableBExc.E6Three.recipeID_subset_inn_E6_two hK2 hφI
  have hφeq : ggLAut L θ' ⟨z⁻¹, inv_mem hzN⟩ = MulAut.conj r :=
    (eq_ggLAut_of_induces L θ' (b := z) hzN hφind).symm
  obtain ⟨k, hkL, hkconj⟩ :=
    NbrInnerMore.exists_conj_of_ggLAut_eq_conj hperf θ' (x := z⁻¹) (inv_mem hzN) hφeq
  have hkconj' : ∀ l ∈ L, z * l * z⁻¹ = k⁻¹ * l * k := by
    intro l hl
    have h := hkconj l hl
    simpa using h
  exact ⟨k, hkL, hkconj', hz3, hzN⟩

theorem ggQTwoE6_lift_k3_centralizes {G : Type} [Group G]
    {z : G} {L : Subgroup G} {k : G}
    (hzN : z ∈ Subgroup.normalizer (L : Set G)) (hz3 : z ^ 3 = 1)
    (hkconj' : ∀ l ∈ L, z * l * z⁻¹ = k⁻¹ * l * k) :
    k ^ 3 ∈ Subgroup.centralizer (L : Set G) := by
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have hconj : ∀ l ∈ L, (MulAut.conj z) l = (MulAut.conj k⁻¹) l := by
    intro l hl
    rw [MulAut.conj_apply, MulAut.conj_apply]
    simpa using hkconj' l hl
  have hmem1 : (MulAut.conj z) l ∈ L := by
    rw [MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.mp hzN l).mp hl
  have hmem2 : (MulAut.conj z) ((MulAut.conj z) l) ∈ L := by
    rw [MulAut.conj_apply]
    exact (Subgroup.mem_normalizer_iff.mp hzN _).mp hmem1
  have h2 : (MulAut.conj k⁻¹) ((MulAut.conj k⁻¹) ((MulAut.conj k⁻¹) l)) = l := by
    calc (MulAut.conj k⁻¹) ((MulAut.conj k⁻¹) ((MulAut.conj k⁻¹) l))
        = (MulAut.conj k⁻¹) ((MulAut.conj k⁻¹) ((MulAut.conj z) l)) := by rw [hconj l hl]
      _ = (MulAut.conj k⁻¹) ((MulAut.conj z) ((MulAut.conj z) l)) := by rw [hconj _ hmem1]
      _ = (MulAut.conj z) ((MulAut.conj z) ((MulAut.conj z) l)) := by rw [hconj _ hmem2]
      _ = l := by
          simp only [MulAut.conj_apply]
          have hz3' : z * z * z = 1 := by
            rw [mul_assoc]
            simpa [pow_three] using hz3
          have hz3inv : z⁻¹ * z⁻¹ * z⁻¹ = 1 := by
            rw [mul_assoc]
            have h : (z⁻¹) ^ 3 = 1 := by rw [inv_pow, hz3, inv_one]
            simpa [pow_three] using h
          calc z * (z * (z * l * z⁻¹) * z⁻¹) * z⁻¹
              = (z * z * z) * l * (z⁻¹ * z⁻¹ * z⁻¹) := by group
            _ = l := by rw [hz3', hz3inv]; group
  simp only [MulAut.conj_apply, inv_inv] at h2
  have h2' : k ^ 3 * l = l * k ^ 3 := by
    calc k ^ 3 * l = k ^ 3 * (k⁻¹ * (k⁻¹ * (k⁻¹ * l * k) * k) * k) := by
          conv_lhs => rw [← h2]
      _ = l * k ^ 3 := pow_three_mul_conj_conj_conj k l
  exact h2'.symm

theorem ggQTwoE6_lift_k3_eq_one {G : Type} [Group G]
    {L : Subgroup G} {k : G} (hkL : k ∈ L)
    (hcent : k ^ 3 ∈ Subgroup.centralizer (L : Set G))
    (hZ : Subgroup.center ↥L = ⊥) :
    k ^ 3 = 1 := by
  have hk3L : k ^ 3 ∈ L := Subgroup.pow_mem L hkL 3
  have hk3Z : (⟨k ^ 3, hk3L⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (hcent (l : G) l.2)
  rw [hZ] at hk3Z
  exact congrArg Subtype.val (Subgroup.mem_bot.mp hk3Z)

theorem ggQTwoE6_lift_k_ne_one {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x z : G} {L D J : Subgroup G} {k : G}
    (hS : GGQTwoSetting 3 B Bs x L D J) (hzD : z ∈ D)
    (hzx : z ∉ Subgroup.zpowers x)
    (hkconj' : ∀ l ∈ L, z * l * z⁻¹ = k⁻¹ * l * k) :
    k ≠ 1 := by
  intro hk1
  apply ggQTwoE6_z_not_central hS hzD hzx
  rw [Subgroup.mem_centralizer_iff]
  intro l hl
  have h := hkconj' l hl
  rw [hk1] at h
  have hzl : z * l = l * z := by
    calc z * l = (z * l * z⁻¹) * z := by group
      _ = l * z := by rw [h]; group
  exact hzl.symm

theorem ggQTwoE6_lift_centralizer_eq {G : Type} [Group G]
    {z : G} {L : Subgroup G} {k : G}
    (hkconj' : ∀ l ∈ L, z * l * z⁻¹ = k⁻¹ * l * k) :
    L ⊓ Subgroup.centralizer ({z} : Set G) =
      L ⊓ Subgroup.centralizer ({k} : Set G) := by
  ext l
  simp only [Subgroup.mem_inf, Subgroup.mem_centralizer_singleton_iff]
  constructor
  · rintro ⟨hlL, hlC⟩
    refine ⟨hlL, ?_⟩
    have h := hkconj' l hlL
    rw [show z * l * z⁻¹ = l from by rw [← hlC]; group] at h
    have hkl : k * l = l * k := by
      calc k * l = k * (k⁻¹ * l * k) := by conv_lhs => rw [h]
        _ = l * k := by group
    exact hkl.symm
  · rintro ⟨hlL, hlC⟩
    refine ⟨hlL, ?_⟩
    have h := hkconj' l hlL
    have hk : k⁻¹ * l * k = l := by
      calc k⁻¹ * l * k = k⁻¹ * (l * k) := by group
        _ = k⁻¹ * (k * l) := by rw [hlC]
        _ = l := by group
    rw [hk] at h
    have hzl : z * l = l * z := by
      calc z * l = (z * l * z⁻¹) * z := by simp [mul_assoc]
        _ = l * z := by rw [h]
    exact hzl.symm

theorem ggQTwoE6_exists_lift
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x z : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hzD : z ∈ D) (hzx : z ∉ Subgroup.zpowers x) :
    ∃ k ∈ L, k ^ 3 = 1 ∧ k ≠ 1 ∧
      L ⊓ Subgroup.centralizer ({z} : Set G) = L ⊓ Subgroup.centralizer ({k} : Set G) := by
  have hperf : commutator ↥L = ⊤ := hmark.1
  have hHas : GGHasLabel ⟨.E6, 0, 1⟩ (L ⧸ Subgroup.center L) :=
    ggQTwoE6_hasLabel_E6 (_B := B) hq2 htag hmark
  have hZ : Subgroup.center ↥L = ⊥ := ggQTwoE6_center_bot L hperf hHas
  obtain ⟨k, hkL, hkconj', hz3, hzN⟩ :=
    ggQTwoE6_lift_exists_k hS hq2 htag hmark hzD
  have hcent := ggQTwoE6_lift_k3_centralizes hzN hz3 hkconj'
  have hk3 := ggQTwoE6_lift_k3_eq_one hkL hcent hZ
  have hk1 := ggQTwoE6_lift_k_ne_one hS hzD hzx hkconj'
  have hCeq := ggQTwoE6_lift_centralizer_eq hkconj'
  exact ⟨k, hkL, hk3, hk1, hCeq⟩

theorem ggQTwoE6_exists_z_in_D {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) :
    ∃ z ∈ D, z ∉ Subgroup.zpowers x := by
  have hSStar : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hxD : x ∈ D := hS.1.1.2.2.1.2.2.2.1
  have hx1 : x ≠ 1 := hSStar.2.2.1
  have hDelem : IsElemAbelian 3 D := hS.1.1.2.2.1.2.1
  have hx3 : x ^ 3 = 1 := hDelem.2 x hxD
  have hDcard : Nat.card D = 9 := by
    have := hS.1.1.2.2.1.2.2.1
    rw [this]; norm_num
  have hxlt : Subgroup.zpowers x < D := by
    rw [lt_iff_le_not_ge]
    refine ⟨Subgroup.zpowers_le.mpr hxD, ?_⟩
    intro hle
    have h1 : Nat.card (Subgroup.zpowers x) = 3 := by
      rw [Nat.card_zpowers, orderOf_eq_prime hx3 hx1]
    have h2 : Nat.card D ≤ 3 := by rw [← h1]; exact Subgroup.card_le_of_le hle
    omega
  exact SetLike.exists_of_lt hxlt

theorem ggQTwoE6_centralizer_D_eq {G : Type} [Group G] {x z : G} {D : Subgroup G}
    (hxD : x ∈ D) (hzD : z ∈ D)
    (hDgen : D = Subgroup.zpowers x ⊔ Subgroup.zpowers z) :
    Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({z} : Set G) := by
  apply le_antisymm
  · intro g hg
    exact ⟨Subgroup.centralizer_le (by rw [Set.singleton_subset_iff]; exact hxD) hg,
      Subgroup.centralizer_le (by rw [Set.singleton_subset_iff]; exact hzD) hg⟩
  · rintro g ⟨hx, hz⟩
    have hxg : x * g = g * x :=
      Subgroup.mem_centralizer_iff.mp hx x (Set.mem_singleton x)
    have hzg : z * g = g * z :=
      Subgroup.mem_centralizer_iff.mp hz z (Set.mem_singleton z)
    have hsub : Subgroup.zpowers x ⊔ Subgroup.zpowers z ≤
        Subgroup.centralizer ({g} : Set G) := by
      refine sup_le ?_ ?_
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr hxg
      · rw [Subgroup.zpowers_le]
        exact Subgroup.mem_centralizer_singleton_iff.mpr hzg
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact Subgroup.mem_centralizer_singleton_iff.mp (hsub (by rwa [← hDgen]))

theorem ggQTwoE6_meet_centralizer_D_eq {G : Type} [Group G] {x z : G} {L D : Subgroup G}
    (hCsup : Subgroup.centralizer (D : Set G) =
      Subgroup.centralizer ({x} : Set G) ⊓ Subgroup.centralizer ({z} : Set G))
    (hLx : L ≤ Subgroup.centralizer ({x} : Set G)) :
    L ⊓ Subgroup.centralizer (D : Set G) =
      L ⊓ Subgroup.centralizer ({z} : Set G) := by
  rw [hCsup, ← inf_assoc, inf_eq_left.mpr hLx]

theorem ggQTwoE6_label_of_subgroupOf {H : Type} [Group H] {J L : Subgroup H}
    (htr' : J.subgroupOf L ≃* J)
    (h : GGHasLabel ⟨.A, 5, 1⟩
        (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L)) ∨
      GGHasLabel ⟨.twD, 4, 1⟩
        (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L)) ∨
      GGHasLabel ⟨.A, 2, 2⟩
        (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L))) :
    GGHasLabel ⟨.A, 5, 1⟩ (J ⧸ Subgroup.center J) ∨
      GGHasLabel ⟨.twD, 4, 1⟩ (J ⧸ Subgroup.center J) ∨
      GGHasLabel ⟨.A, 2, 2⟩ (J ⧸ Subgroup.center J) := by
  rcases h with hA | hD4 | hA2
  · exact Or.inl (ggHasLabel_quotCenter_of_mulEquiv htr' hA)
  · exact Or.inr (Or.inl (ggHasLabel_quotCenter_of_mulEquiv htr' hD4))
  · exact Or.inr (Or.inr (ggHasLabel_quotCenter_of_mulEquiv htr' hA2))

theorem ggQTwoE6_J_label
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    GGHasLabel ⟨.A, 5, 1⟩ (J ⧸ Subgroup.center J) ∨
      GGHasLabel ⟨.twD, 4, 1⟩ (J ⧸ Subgroup.center J) ∨
      GGHasLabel ⟨.A, 2, 2⟩ (J ⧸ Subgroup.center J) := by
  classical
  obtain ⟨z, hzD, hzx⟩ := ggQTwoE6_exists_z_in_D hS
  obtain ⟨k, hkL, hk3, hk1, hCeq⟩ := ggQTwoE6_exists_lift hS hq2 htag hmark hzD hzx
  have hSStar : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hxD : x ∈ D := hS.1.1.2.2.1.2.2.2.1
  have hLx : L ≤ Subgroup.centralizer ({x} : Set G) := hSStar.2.2.2.1.1
  have hDgen : D = Subgroup.zpowers x ⊔ Subgroup.zpowers z := ggQTwoE6_D_eq hS hzD hzx
  have hCsup := ggQTwoE6_centralizer_D_eq hxD hzD hDgen
  have hCD := ggQTwoE6_meet_centralizer_D_eq hCsup hLx
  have hJ0 : J = LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hS.1.1.2.2.1.2.2.2.2.1
  have hJc0 : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hS.1.1.2.2.1.2.2.2.2.2.1
  have hJ : J = LargeEvenLayer (L ⊓ Subgroup.centralizer ({k} : Set G)) := by
    rw [hJ0, hCD, hCeq]
  have hJc : IsComponentOf J (L ⊓ Subgroup.centralizer ({k} : Set G)) := by
    rw [hCD, hCeq] at hJc0
    exact hJc0
  have htr := ggR4Meet_transport hkL hJ hJc
  have hHasL : GGHasLabel ⟨.E6, 0, 1⟩ (↥L ⧸ Subgroup.center ↥L) :=
    ggQTwoE6_hasLabel_E6 (_B := B) hq2 htag hmark
  have hkl : (⟨k, hkL⟩ : ↥L) ≠ 1 := fun h => hk1 (congrArg Subtype.val h)
  have hk3l : (⟨k, hkL⟩ : ↥L) ^ 3 = 1 := Subtype.ext hk3
  have : Group.IsPerfect ↥L := Group.isPerfect_def.2 hmark.1
  have hlab := ggE6OppOrderThree_label_two hHasL hkl hk3l htr.2.1 htr.2.2
  have htr' : J.subgroupOf L ≃* J := Subgroup.subgroupOfEquivOfLe htr.1
  exact ggQTwoE6_label_of_subgroupOf htr' hlab

theorem ggQTwoE6_A2_impossible
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hN : Bs ≤ Subgroup.normalizer (L : Set G))
    (hJ : GGHasLabel ⟨.A, 2, 2⟩ (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L))) :
    False := by
  have hcfg : GGConfig 3 B Bs x L D J := hS.1.1
  have hCard : Nat.card Bs = 3 ^ 5 := ggQTwoE6_card_Bs hS hq2 htag hmark
  have hperf : commutator ↥L = ⊤ := hmark.1
  have hL : GGHasLabel ⟨.E6, 0, 1⟩ (↥L ⧸ Subgroup.center ↥L) :=
    ggQTwoE6_hasLabel_E6 (_B := B) hq2 htag hmark
  have hZ : Subgroup.center ↥L = ⊥ := ggQTwoE6_center_bot (K := ↥L) hperf hL
  have hZL : ∀ g ∈ Subgroup.center ↥L, Nat.Coprime 3 (orderOf g) := by
    intro g hg
    rw [hZ, Subgroup.mem_bot] at hg
    rw [hg]
    norm_num
  exact ggR4Meet_noE6TwoL34 hcfg hN hCard hperf hZL hL hJ

theorem ggQTwoE6_A5_slLift {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (hperf : commutator ↥J = ⊤)
    (hJ : GGHasLabel ⟨.A, 5, 1⟩ (J ⧸ Subgroup.center J)) :
    ∃ φ : Matrix.SpecialLinearGroup (Fin 6) GGHalf.F2 →* G,
      φ.range = J ∧ Function.Injective φ := by
  have hΛ : LargeEvenInLambda2 ⟨.A, 5, 1⟩ := by simp [LargeEvenInLambda2]
  have hmod : CFSG.Open.StatedClassicalModel (J ⧸ Subgroup.center J) .PSL 6 2 1 := by
    simpa using statedClassicalModel_of_hasLabel_typeA hΛ hJ
  exact GGHalf.exists_slLift_two (m := 3) (by norm_num) hperf hmod

theorem ggQTwoE6_A5_frame {G : Type} [Group G] [Finite G] {B Bs J : Subgroup G}
    (hB : GGBstar 3 B Bs) (hnorm : Bs ≤ Subgroup.normalizer (J : Set G))
    {φ : Matrix.SpecialLinearGroup (Fin 6) GGHalf.F2 →* G}
    (hφr : φ.range = J) (hφi : Function.Injective φ) :
    ∃ ψ : Matrix.SpecialLinearGroup (Fin 6) GGHalf.F2 →* G,
      GGHalfTorusFrame Bs J (GGHalf.halfTorus 5) ψ := by
  obtain ⟨A, hframe⟩ :=
    ggHalf_torusFrame (hp := rfl) hB (N := 5) (by omega) hnorm φ hφr hφi
  exact ⟨φ.comp (MulAut.conj A).toMonoidHom, hframe⟩

theorem ggQTwoE6_bstar_eq_sup {G : Type} [Group G] {Bs J : Subgroup G} {n : ℕ}
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (hF : GGHalfTorusFrame Bs J (GGHalf.halfTorus n) ψ) :
    Bs = (Bs ⊓ Subgroup.centralizer (J : Set G)) ⊔ (GGHalf.halfTorus n).map ψ := by
  refine le_antisymm ?_ (sup_le inf_le_left hF.torus_le)
  intro b hb
  obtain ⟨t, ht, hact⟩ := hF.act b hb
  have hψtB : ψ t ∈ Bs := hF.torus_le (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩)
  have hcent : (ψ t)⁻¹ * b ∈ Subgroup.centralizer (J : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h := hact l hl
    calc l * ((ψ t)⁻¹ * b)
        = (ψ t)⁻¹ * (ψ t * l * (ψ t)⁻¹) * b := by group
      _ = (ψ t)⁻¹ * (b * l * b⁻¹) * b := by rw [← h]
      _ = (ψ t)⁻¹ * b * l := by group
  have hmem : (ψ t)⁻¹ * b ∈ Bs ⊓ Subgroup.centralizer (J : Set G) :=
    ⟨Bs.mul_mem (Bs.inv_mem hψtB) hb, hcent⟩
  have heq : b = ψ t * ((ψ t)⁻¹ * b) := by group
  rw [heq, sup_comm]
  exact Subgroup.mul_mem_sup (Subgroup.mem_map.mpr ⟨t, ht, rfl⟩) hmem

theorem psi_delta_mem_normalizer_halfTorus {n : ℕ} {G : Type} [Group G]
    {ψ : Matrix.SpecialLinearGroup (Fin (n + 1)) GGHalf.F2 →* G}
    (S : Finset (Fin (GGQ2Lin.R n))) :
    ψ (GGQ2Lin.delta n S) ∈
      Subgroup.normalizer (((GGHalf.halfTorus n).map ψ : Subgroup G) : Set G) := by
  have hg2 : ψ (GGQ2Lin.delta n S) * ψ (GGQ2Lin.delta n S) = 1 := by
    rw [← map_mul, GGQ2Lin.delta_sq n S, map_one]
  refine GGQ2Lin.mem_normalizer_of_conj_mem hg2 ?_
  intro y hy
  obtain ⟨s, hsT, rfl⟩ := Subgroup.mem_map.mp hy
  have huc := GGQ2Lin.ggQ2Lin_delta_conj_mem_halfTorus n S hsT
  have hconj : ψ (GGQ2Lin.delta n S) * ψ s * (ψ (GGQ2Lin.delta n S))⁻¹ =
      ψ (GGQ2Lin.delta n S * s * (GGQ2Lin.delta n S)⁻¹) := by
    rw [← map_mul, ← map_inv, ← map_mul]
  rw [hconj]
  exact Subgroup.mem_map.mpr ⟨_, huc, rfl⟩

theorem psi_delta_mem_normalizer_bstar {G : Type} [Group G] {Bs J : Subgroup G}
    {ψ : Matrix.SpecialLinearGroup (Fin 6) GGHalf.F2 →* G}
    (hF : GGHalfTorusFrame Bs J (GGHalf.halfTorus 5) ψ)
    (hBs : Bs = (Bs ⊓ Subgroup.centralizer (J : Set G)) ⊔ (GGHalf.halfTorus 5).map ψ)
    (S : Finset (Fin (GGQ2Lin.R 5))) :
    ψ (GGQ2Lin.delta 5 S) ∈ Subgroup.normalizer (Bs : Set G) := by
  have hgJ : ψ (GGQ2Lin.delta 5 S) ∈ J := by
    rw [← hF.range]
    exact ⟨GGQ2Lin.delta 5 S, rfl⟩
  have hgC : ψ (GGQ2Lin.delta 5 S) ∈
      Subgroup.centralizer ((Bs ⊓ Subgroup.centralizer (J : Set G)) : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    exact (Subgroup.mem_centralizer_iff.mp hy.2 (ψ (GGQ2Lin.delta 5 S)) hgJ).symm
  have hgNc : ψ (GGQ2Lin.delta 5 S) ∈
      Subgroup.normalizer ((Bs ⊓ Subgroup.centralizer (J : Set G)) : Set G) :=
    Subgroup.centralizer_le_normalizer _ hgC
  have hgT := psi_delta_mem_normalizer_halfTorus (n := 5) (ψ := ψ) S
  rw [hBs]
  exact Subgroup.inf_normalizer_le_normalizer_sup _ _ ⟨hgNc, hgT⟩

theorem ggQTwoE6_blockGen_ne_inv (n : ℕ) (i : Fin (GGQ2Lin.R n)) :
    GGQ2Lin.blockGen n i ≠ (GGQ2Lin.blockGen n i)⁻¹ := by
  intro h
  have hsq : GGQ2Lin.blockGen n i * GGQ2Lin.blockGen n i = 1 := by
    nth_rewrite 1 [h]
    exact inv_mul_cancel _
  have hcube : GGQ2Lin.blockGen n i ^ 3 = 1 := by
    unfold GGQ2Lin.blockGen
    exact GGHalf.omegaBlock_pow_three n (GGQ2Lin.pairIdx n i)
  have hne : GGQ2Lin.blockGen n i ≠ 1 := by
    unfold GGQ2Lin.blockGen
    exact GGHalf.omegaBlock_ne_one n (GGQ2Lin.pairIdx n i)
  have h3 : GGQ2Lin.blockGen n i ^ 3 = GGQ2Lin.blockGen n i := by
    rw [pow_succ, pow_two, hsq, one_mul]
  rw [hcube] at h3
  exact hne h3.symm

theorem ggQTwoE6_swapPerm_comm_of_disjoint (n : ℕ)
    {S T : Finset (Fin (GGQ2Lin.R n))} (h : Disjoint S T) :
    GGQ2Lin.swapPerm n S * GGQ2Lin.swapPerm n T =
      GGQ2Lin.swapPerm n T * GGQ2Lin.swapPerm n S := by
  ext x
  rcases hx : GGQ2Lin.epsTwo n x with ⟨a, i⟩ | j
  · have hx' : x = GGQ2Lin.pairCoord n i a := by
      rw [← GGQ2Lin.epsTwo_symm_inl n i a, ← hx, Equiv.symm_apply_apply]
    rw [hx']
    simp only [Equiv.Perm.mul_apply, GGQ2Lin.swapPerm_apply_pair]
    by_cases hS : i ∈ S
    · have hT : i ∉ T := Finset.disjoint_left.mp h hS
      simp [hS, hT]
    · by_cases hT : i ∈ T
      · simp [hS, hT]
      · simp [hS, hT]
  · have hx' : x = GGQ2Lin.restCoord n j := by
      rw [← GGQ2Lin.epsTwo_symm_inr n j, ← hx, Equiv.symm_apply_apply]
    rw [hx']
    simp only [Equiv.Perm.mul_apply, GGQ2Lin.swapPerm_apply_rest]

theorem ggQTwoE6_delta_comm_of_disjoint (n : ℕ)
    {S T : Finset (Fin (GGQ2Lin.R n))} (h : Disjoint S T) :
    GGQ2Lin.delta n S * GGQ2Lin.delta n T =
      GGQ2Lin.delta n T * GGQ2Lin.delta n S := by
  unfold GGQ2Lin.delta
  rw [← map_mul, ← map_mul, ggQTwoE6_swapPerm_comm_of_disjoint n h]

theorem ggQTwoE6_A5_frame_data {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hJ : GGHasLabel ⟨.A, 5, 1⟩ (J ⧸ Subgroup.center J)) :
    ∃ (ψ : Matrix.SpecialLinearGroup (Fin 6) GGHalf.F2 →* G),
      GGHalfTorusFrame Bs J (GGHalf.halfTorus 5) ψ ∧
      Bs = (Bs ⊓ Subgroup.centralizer (J : Set G)) ⊔ (GGHalf.halfTorus 5).map ψ := by
  have hJc : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hS.1.1.2.2.1.2.2.2.2.2.1
  have hperfJ : commutator ↥J = ⊤ := hJc.2.2.1
  obtain ⟨φ, hφr, hφi⟩ := ggQTwoE6_A5_slLift hperfJ hJ
  have hB : GGBstar 3 B Bs := hS.1.1.2.1
  have hInn : GGInnerDiagOn Bs L := hS.1.2.2.1.1
  have hnorm : Bs ≤ Subgroup.normalizer (J : Set G) := ggR4_normalizes_J hS.1.1 hInn
  obtain ⟨ψ, hF⟩ := ggQTwoE6_A5_frame hB hnorm hφr hφi
  exact ⟨ψ, hF, ggQTwoE6_bstar_eq_sup hF⟩

theorem psi_delta_conj_blockGen_ne {G : Type} [Group G] {Bs J : Subgroup G}
    {ψ : Matrix.SpecialLinearGroup (Fin 6) GGHalf.F2 →* G}
    (hF : GGHalfTorusFrame Bs J (GGHalf.halfTorus 5) ψ)
    (S : Finset (Fin (GGQ2Lin.R 5))) {i : Fin (GGQ2Lin.R 5)} (hi : i ∈ S) :
    ψ (GGQ2Lin.delta 5 S) * ψ (GGQ2Lin.blockGen 5 i) * (ψ (GGQ2Lin.delta 5 S))⁻¹ ≠
      ψ (GGQ2Lin.blockGen 5 i) := by
  intro hconj
  have h1 : GGQ2Lin.delta 5 S * GGQ2Lin.blockGen 5 i * (GGQ2Lin.delta 5 S)⁻¹ =
      GGQ2Lin.blockGen 5 i := by
    apply hF.inj
    simpa only [map_mul, map_inv] using hconj
  rw [GGQ2Lin.delta_conj_blockGen_of_mem 5 S hi] at h1
  exact ggQTwoE6_blockGen_ne_inv 5 i h1.symm

theorem psi_delta_conj_blockGen_eq {G : Type} [Group G] {Bs J : Subgroup G}
    {ψ : Matrix.SpecialLinearGroup (Fin 6) GGHalf.F2 →* G}
    (_hF : GGHalfTorusFrame Bs J (GGHalf.halfTorus 5) ψ)
    (S : Finset (Fin (GGQ2Lin.R 5))) {i : Fin (GGQ2Lin.R 5)} (hi : i ∉ S) :
    ψ (GGQ2Lin.delta 5 S) * ψ (GGQ2Lin.blockGen 5 i) * (ψ (GGQ2Lin.delta 5 S))⁻¹ =
      ψ (GGQ2Lin.blockGen 5 i) := by
  have h1 : GGQ2Lin.delta 5 S * GGQ2Lin.blockGen 5 i * (GGQ2Lin.delta 5 S)⁻¹ =
      GGQ2Lin.blockGen 5 i := GGQ2Lin.delta_conj_blockGen_of_not_mem 5 S hi
  calc ψ (GGQ2Lin.delta 5 S) * ψ (GGQ2Lin.blockGen 5 i) * (ψ (GGQ2Lin.delta 5 S))⁻¹
      = ψ (GGQ2Lin.delta 5 S * GGQ2Lin.blockGen 5 i * (GGQ2Lin.delta 5 S)⁻¹) := by
        rw [← map_mul, ← map_inv, ← map_mul]
    _ = ψ (GGQ2Lin.blockGen 5 i) := by rw [h1]

theorem ggQTwoE6_A5_data_basic {G : Type} [Group G] [Finite G] {Bs J : Subgroup G}
    {ψ : Matrix.SpecialLinearGroup (Fin 6) GGHalf.F2 →* G}
    (hF : GGHalfTorusFrame Bs J (GGHalf.halfTorus 5) ψ)
    (hBs : Bs = (Bs ⊓ Subgroup.centralizer (J : Set G)) ⊔ (GGHalf.halfTorus 5).map ψ)
    (i0 i1 : Fin (GGQ2Lin.R 5)) (_hi01 : i0 ≠ i1)
    (hdisj : Disjoint ({i0} : Finset (Fin (GGQ2Lin.R 5))) {i1}) :
    ∃ (g h b0 b1 : G),
      g = ψ (GGQ2Lin.delta 5 {i0}) ∧ h = ψ (GGQ2Lin.delta 5 {i1}) ∧
      b0 = ψ (GGQ2Lin.blockGen 5 i0) ∧ b1 = ψ (GGQ2Lin.blockGen 5 i1) ∧
      g ∈ J ∧ h ∈ J ∧ g ∈ Subgroup.normalizer (Bs : Set G) ∧
      h ∈ Subgroup.normalizer (Bs : Set G) ∧ g * g = 1 ∧ h * h = 1 ∧
      g * h = h * g ∧ b0 ∈ Bs ∧ b1 ∈ Bs := by
  refine ⟨ψ (GGQ2Lin.delta 5 {i0}), ψ (GGQ2Lin.delta 5 {i1}),
    ψ (GGQ2Lin.blockGen 5 i0), ψ (GGQ2Lin.blockGen 5 i1),
    rfl, rfl, rfl, rfl, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [← hF.range]
    exact ⟨GGQ2Lin.delta 5 {i0}, rfl⟩
  · rw [← hF.range]
    exact ⟨GGQ2Lin.delta 5 {i1}, rfl⟩
  · exact psi_delta_mem_normalizer_bstar hF hBs {i0}
  · exact psi_delta_mem_normalizer_bstar hF hBs {i1}
  · rw [← map_mul, GGQ2Lin.delta_sq 5 {i0}, map_one]
  · rw [← map_mul, GGQ2Lin.delta_sq 5 {i1}, map_one]
  · rw [← map_mul, ← map_mul, ggQTwoE6_delta_comm_of_disjoint 5 hdisj]
  · exact hF.torus_le
      (Subgroup.mem_map.mpr ⟨GGQ2Lin.blockGen 5 i0, GGQ2Lin.blockGen_mem 5 i0, rfl⟩)
  · exact hF.torus_le
      (Subgroup.mem_map.mpr ⟨GGQ2Lin.blockGen 5 i1, GGQ2Lin.blockGen_mem 5 i1, rfl⟩)

theorem ggQTwoE6_A5_data_moves {G : Type} [Group G] {Bs J : Subgroup G}
    {ψ : Matrix.SpecialLinearGroup (Fin 6) GGHalf.F2 →* G}
    (hF : GGHalfTorusFrame Bs J (GGHalf.halfTorus 5) ψ)
    (i0 i1 : Fin (GGQ2Lin.R 5)) (hi01 : i0 ≠ i1) (g h b0 b1 : G)
    (hg : g = ψ (GGQ2Lin.delta 5 {i0})) (hh : h = ψ (GGQ2Lin.delta 5 {i1}))
    (hb0 : b0 = ψ (GGQ2Lin.blockGen 5 i0)) (hb1 : b1 = ψ (GGQ2Lin.blockGen 5 i1)) :
    g * b0 * g⁻¹ ≠ b0 ∧ h * b1 * h⁻¹ ≠ b1 ∧ h * b0 * h⁻¹ = b0 ∧
      g ≠ 1 ∧ h ≠ 1 ∧ g ≠ h ∧ (g * h) * b0 * (g * h)⁻¹ ≠ b0 := by
  subst hg hh hb0 hb1
  have hg_move : ψ (GGQ2Lin.delta 5 {i0}) * ψ (GGQ2Lin.blockGen 5 i0) *
      (ψ (GGQ2Lin.delta 5 {i0}))⁻¹ ≠ ψ (GGQ2Lin.blockGen 5 i0) :=
    psi_delta_conj_blockGen_ne hF {i0} (by simp)
  have hh_move : ψ (GGQ2Lin.delta 5 {i1}) * ψ (GGQ2Lin.blockGen 5 i1) *
      (ψ (GGQ2Lin.delta 5 {i1}))⁻¹ ≠ ψ (GGQ2Lin.blockGen 5 i1) :=
    psi_delta_conj_blockGen_ne hF {i1} (by simp)
  have hh_fix : ψ (GGQ2Lin.delta 5 {i1}) * ψ (GGQ2Lin.blockGen 5 i0) *
      (ψ (GGQ2Lin.delta 5 {i1}))⁻¹ = ψ (GGQ2Lin.blockGen 5 i0) :=
    psi_delta_conj_blockGen_eq hF {i1} (by simpa using hi01)
  refine ⟨hg_move, hh_move, hh_fix, ?_, ?_, ?_, ?_⟩
  · intro h1
    exact hg_move (by rw [h1]; group)
  · intro h1
    exact hh_move (by rw [h1]; group)
  · intro h1
    exact hg_move (by rw [h1]; exact hh_fix)
  · intro hconj
    apply hg_move
    calc ψ (GGQ2Lin.delta 5 {i0}) * ψ (GGQ2Lin.blockGen 5 i0) *
          (ψ (GGQ2Lin.delta 5 {i0}))⁻¹
        = ψ (GGQ2Lin.delta 5 {i0}) *
            (ψ (GGQ2Lin.delta 5 {i1}) * ψ (GGQ2Lin.blockGen 5 i0) *
              (ψ (GGQ2Lin.delta 5 {i1}))⁻¹) * (ψ (GGQ2Lin.delta 5 {i0}))⁻¹ := by
          rw [hh_fix]
      _ = (ψ (GGQ2Lin.delta 5 {i0}) * ψ (GGQ2Lin.delta 5 {i1})) *
            ψ (GGQ2Lin.blockGen 5 i0) *
              (ψ (GGQ2Lin.delta 5 {i0}) * ψ (GGQ2Lin.delta 5 {i1}))⁻¹ := by group
      _ = ψ (GGQ2Lin.blockGen 5 i0) := hconj

theorem ggQTwoE6_A5_four_dvd {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G}
    {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hJ : GGHasLabel ⟨.A, 5, 1⟩ (J ⧸ Subgroup.center J)) :
    4 ∣ Nat.card (ggAutomizer J Bs) := by
  obtain ⟨ψ, hF, hBs⟩ := ggQTwoE6_A5_frame_data hS hJ
  let i0 : Fin (GGQ2Lin.R 5) := ⟨0, by norm_num [GGQ2Lin.R]⟩
  let i1 : Fin (GGQ2Lin.R 5) := ⟨1, by norm_num [GGQ2Lin.R]⟩
  have hi01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  have hdisj : Disjoint ({i0} : Finset (Fin (GGQ2Lin.R 5))) {i1} := by
    rw [Finset.disjoint_singleton_left]
    simp [hi01]
  obtain ⟨g, h, b0, b1, hg, hh, hb0, hb1, hgJ, hhJ, hgN, hhN, hg2, hh2, hcomm,
    hb0Bs, hb1Bs⟩ := ggQTwoE6_A5_data_basic hF hBs i0 i1 hi01 hdisj
  obtain ⟨hg_move, hh_move, hh_fix, hg1, hh1, hne, hgh_move⟩ :=
    ggQTwoE6_A5_data_moves hF i0 i1 hi01 g h b0 b1 hg hh hb0 hb1
  refine GGQ2Lin.ggQ2Lin_four_dvd_aut hgJ hhJ hgN hhN hg2 hh2 hcomm hg1 hh1 hne ?_
  intro x hx hcent
  have hxset : x ∈ ({1, g, h, g * h} : Set G) := by
    rw [← CFSG.GroupTheory.coe_closure_pair_eq hg2 hh2 hcomm hg1 hh1 hne]
    exact hx
  rcases hxset with rfl | rfl | rfl | rfl
  · rfl
  · exact absurd (hcent b0 hb0Bs) hg_move
  · exact absurd (hcent b1 hb1Bs) hh_move
  · exact absurd (hcent b0 hb0Bs) hgh_move

theorem ggQTwoE6_D4_omegaLift {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (hperf : commutator ↥J = ⊤)
    (hJ : GGHasLabel ⟨.twD, 4, 1⟩ (J ⧸ Subgroup.center J)) :
    ∃ φ : ↥(CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 (ZMod 2) 1 1)) →* G,
      φ.range = J ∧ Function.Injective φ := by
  have hmodel : CFSG.Open.StatedClassicalModel (J ⧸ Subgroup.center J) .POmegaMinus 4 2 1 :=
    statedClassicalModel_of_hasLabel_typeTwD (by norm_num) hJ
  have hPerf : Group.IsPerfect ↥J := Group.isPerfect_def.2 hperf
  have hZ : Subgroup.center ↥J = ⊥ :=
    @HalfRowData.center_eq_bot_of_pomegaMinus_two ↥J _ hPerf 4 1 hmodel
  obtain ⟨e⟩ :=
    CFSG.HardMathSupport.Foote.E27.nonempty_mulEquiv_omegaMinus hmodel
  let q : (↥J ⧸ Subgroup.center ↥J) ≃* ↥J :=
    (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
  let eJ : ↥J ≃* CFSG.Open.StatedOmega (CFSG.Open.StatedQuadMinus 4 (ZMod 2) 1 1) :=
    q.symm.trans e
  refine ⟨J.subtype.comp eJ.symm.toMonoidHom, ?_, ?_⟩
  · rw [MonoidHom.range_comp, MonoidHom.range_eq_top.mpr eJ.symm.surjective,
      Subgroup.map_top, Subgroup.range_subtype]
  · exact J.subtype_injective.comp eJ.symm.injective

theorem ggQTwoE6_D4_center_bot
    {G : Type} [Group G] [Finite G] {J : Subgroup G}
    (hperf : commutator ↥J = ⊤)
    (hJ : GGHasLabel ⟨.twD, 4, 1⟩ (J ⧸ Subgroup.center J)) :
    Subgroup.center ↥J = ⊥ := by
  have hmodel : CFSG.Open.StatedClassicalModel (J ⧸ Subgroup.center J) .POmegaMinus 4 2 1 :=
    statedClassicalModel_of_hasLabel_typeTwD (by norm_num) hJ
  exact @HalfRowData.center_eq_bot_of_pomegaMinus_two ↥J _ (Group.isPerfect_def.2 hperf)
    4 1 hmodel

theorem ggQTwoE6_conj_injective_of_center_eq_bot {G : Type} [Group G] {L : Subgroup G}
    (hZ : Subgroup.center ↥L = ⊥) :
    Function.Injective (MulAut.conj : ↥L →* MulAut ↥L) := by
  intro a b hab
  have h : b⁻¹ * a ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 := congrArg (fun f : MulAut ↥L => f z) hab
    rw [MulAut.conj_apply, MulAut.conj_apply] at h1
    calc z * (b⁻¹ * a) = b⁻¹ * (b * z * b⁻¹) * a := by group
      _ = b⁻¹ * (a * z * a⁻¹) * a := by rw [← h1]
      _ = (b⁻¹ * a) * z := by group
  rw [hZ, Subgroup.mem_bot] at h
  calc a = b * (b⁻¹ * a) := by group
    _ = b := by rw [h, mul_one]

theorem ggQTwoE6_eq_one_of_conj_eq_one {G : Type} [Group G] {L : Subgroup G}
    (hZ : Subgroup.center ↥L = ⊥) {a : ↥L} (h : MulAut.conj a = 1) : a = 1 := by
  have hmem : a ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 := congrArg (fun f : MulAut ↥L => f z) h
    rw [MulAut.conj_apply, MulAut.one_apply] at h1
    calc z * a = (a * z * a⁻¹) * a := by rw [h1]
      _ = a * z := by group
  rw [hZ, Subgroup.mem_bot] at hmem
  exact hmem

theorem ggQTwoE6_x_not_mem_L
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    x ∉ L := by
  intro hxL
  have hperf : commutator ↥L = ⊤ := hmark.1
  have hHas : GGHasLabel ⟨.E6, 0, 1⟩ (L ⧸ Subgroup.center L) :=
    ggQTwoE6_hasLabel_E6 (_B := B) hq2 htag hmark
  have hZ : Subgroup.center ↥L = ⊥ := ggQTwoE6_center_bot L hperf hHas
  have hcomp : IsComponentOf L (Subgroup.centralizer ({x} : Set G)) :=
    hS.1.1.1.2.2.2.2.2.2.1.2.2.2.1
  have hxc : ∀ l ∈ L, l * x = x * l := by
    intro l hl
    exact Subgroup.mem_centralizer_singleton_iff.mp (hcomp.1 hl)
  have hx1 : x ≠ 1 := hS.1.1.1.2.2.2.2.2.2.1.2.2.1
  have hxZ : (⟨x, hxL⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro l
    exact Subtype.ext (hxc l l.2)
  rw [hZ, Subgroup.mem_bot] at hxZ
  exact hx1 (congrArg Subtype.val hxZ)

theorem ggQTwoE6_Bs_le_normalizer_L {G : Type} [Group G] {Bs L : Subgroup G}
    {lab : LargeEvenLabel} (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    Bs ≤ Subgroup.normalizer (L : Set G) := by
  obtain ⟨-, labM, hlabM, hrawM⟩ := hmark
  obtain ⟨-, -, -, -, -, -, -, hlabEq, -, -⟩ := largeEvenRawDatum_exists hrawM
  have ht0 : labM.tag = .E6 := by rw [hlabEq]; exact htag
  rw [LargeEvenRawDatumLegacy, ht0] at hrawM
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hrawM
  obtain ⟨-, -, θ, -, hN, hI⟩ := hQ
  exact hN

theorem ggQTwoE6_innerOn_L
    {G : Type} [Group G] [Finite G] {Bs : Subgroup G} {L : Subgroup G}
    {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    ∀ b : Bs, ∃ a : G, a ∈ L ∧
      ∀ l ∈ L, (b : G) * l * (b : G)⁻¹ = a * l * a⁻¹ := by
  classical
  obtain ⟨hperf, labM, hlabM, hrawM⟩ := hmark
  obtain ⟨-, -, -, -, -, -, -, hlabEq, -, -⟩ := largeEvenRawDatum_exists hrawM
  have hn1 : labM.n = 1 := by
    have hlt : labM.n < 2 := by rw [hlabEq]; exact hq2
    have hn : 1 ≤ labM.n := hlabM.1
    omega
  have htagM : labM.tag = .E6 := by rw [hlabEq]; exact htag
  rw [LargeEvenRawDatumLegacy, htagM] at hrawM
  obtain ⟨K, hfield, hfinite, hK, hQ⟩ := hrawM
  let : Field K := hfield
  let : Finite K := hfinite
  have hK2 : Nat.card K = 2 := by rw [hK, hn1]; norm_num
  obtain ⟨-, -, θ, -, hN, hI⟩ := hQ
  intro b
  obtain ⟨φ, hφI, hφind⟩ := hI ((b : Bs)⁻¹ : G) (Bs.inv_mem b.2)
  obtain ⟨r, rfl⟩ := TableBExc.E6Three.recipeID_subset_inn_E6_two hK2 hφI
  let ψ : ↥L →* TableBExc.RecipeGroup .E6 K :=
    θ.toMonoidHom.comp (QuotientGroup.mk' (Subgroup.center ↥L))
  have hψ : Function.Surjective ψ := θ.surjective.comp (QuotientGroup.mk'_surjective _)
  have hker : ψ.ker ≤ Subgroup.center ↥L := by
    have hker_eq : ψ.ker = Subgroup.center ↥L := by
      ext y
      rw [MonoidHom.mem_ker]
      change θ (QuotientGroup.mk y) = 1 ↔ y ∈ Subgroup.center ↥L
      rw [MulEquiv.map_eq_one_iff, QuotientGroup.eq_one_iff]
    rw [hker_eq]
  have hbN : (b : G) ∈ Subgroup.normalizer (L : Set G) := hN b.2
  let a : MulAut ↥L := L.normalizerMonoidHom ⟨(b : G), hbN⟩
  have hcoe : ∀ l : ↥L, ((a l : ↥L) : G) = (b : G) * (l : G) * (b : G)⁻¹ := by
    intro l
    change ((L.normalizerMonoidHom ⟨(b : G), hbN⟩ l : ↥L) : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe]
  have hind' : ∀ l : ↥L, MulAut.conj r (ψ l) = ψ (a l) := by
    intro l
    exact hφind l (a l) (by simpa using hcoe l)
  obtain ⟨g, hg⟩ := isInner_of_induces hψ hker hperf a ⟨r, rfl⟩ hind'
  refine ⟨(g : G), g.2, fun l hl => ?_⟩
  have h := congrArg (fun f : MulAut ↥L => (((f ⟨l, hl⟩ : ↥L) : G))) hg
  simpa [hcoe, MulAut.conj_apply] using h

theorem ggQTwoE6_centralizes_of_innerOn_L
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    {b : Bs} {a : G} (haL : a ∈ L)
    (ha : ∀ l ∈ L, (b : G) * l * (b : G)⁻¹ = a * l * a⁻¹) :
    a ∈ Subgroup.centralizer (Bs : Set G) := by
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    ggQTwoE6_Bs_le_normalizer_L htag hmark
  have hZ : Subgroup.center ↥L = ⊥ :=
    ggQTwoE6_center_bot L hmark.1 (ggQTwoE6_hasLabel_E6 (_B := B) hq2 htag hmark)
  have hBelem : IsElemAbelian 3 Bs := hS.1.1.2.1.2.1
  rw [Subgroup.mem_centralizer_iff]
  intro c hc
  have hcL : c ∈ Subgroup.normalizer (L : Set G) := hN hc
  have hcaL : c * a * c⁻¹ ∈ L := (Subgroup.mem_normalizer_iff.mp hcL a).mp haL
  have hconj : MulAut.conj (⟨a, haL⟩ : ↥L) =
      MulAut.conj (⟨c * a * c⁻¹, hcaL⟩ : ↥L) := by
    ext l
    rw [MulAut.conj_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    have hbcomm : c * (b : G) = (b : G) * c :=
      (CFSG.commute_of_mem_of_isMulCommutative hBelem.1 hc b.2).eq
    have hl1' : c⁻¹ * (l : G) * c ∈ L := by
      simpa using (Subgroup.mem_normalizer_iff.mp
        ((Subgroup.normalizer (L : Set G)).inv_mem hcL) (l : G)).mp l.2
    have h1 := ha (c⁻¹ * (l : G) * c) hl1'
    have h4 : c * ((b : G) * (c⁻¹ * (l : G) * c) * (b : G)⁻¹) * c⁻¹ =
        (b : G) * (l : G) * (b : G)⁻¹ := by
      have hcb' : c * (b : G) * c⁻¹ = (b : G) := by rw [hbcomm]; group
      calc c * ((b : G) * (c⁻¹ * (l : G) * c) * (b : G)⁻¹) * c⁻¹
          = (c * (b : G) * c⁻¹) * (l : G) * (c * (b : G) * c⁻¹)⁻¹ := by group
        _ = (b : G) * (l : G) * (b : G)⁻¹ := by rw [hcb']
    calc a * (l : G) * a⁻¹ = (b : G) * (l : G) * (b : G)⁻¹ := (ha (l : G) l.2).symm
      _ = c * ((b : G) * (c⁻¹ * (l : G) * c) * (b : G)⁻¹) * c⁻¹ := h4.symm
      _ = c * (a * (c⁻¹ * (l : G) * c) * a⁻¹) * c⁻¹ := by rw [h1]
      _ = (c * a * c⁻¹) * (l : G) * (c * a * c⁻¹)⁻¹ := by group
  have hsub : (⟨a, haL⟩ : ↥L) = ⟨c * a * c⁻¹, hcaL⟩ :=
    ggQTwoE6_conj_injective_of_center_eq_bot hZ hconj
  have hval : a = c * a * c⁻¹ := congrArg Subtype.val hsub
  have hac : a * c = c * a := by
    conv_lhs => rw [hval]
    group
  exact hac.symm

theorem ggQTwoE6_pow_three_of_innerOn_L
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    {b : Bs} {a : G} (haL : a ∈ L)
    (ha : ∀ l ∈ L, (b : G) * l * (b : G)⁻¹ = a * l * a⁻¹) :
    a ^ 3 = 1 := by
  have hN : Bs ≤ Subgroup.normalizer (L : Set G) :=
    ggQTwoE6_Bs_le_normalizer_L htag hmark
  have hZ : Subgroup.center ↥L = ⊥ :=
    ggQTwoE6_center_bot L hmark.1 (ggQTwoE6_hasLabel_E6 (_B := B) hq2 htag hmark)
  have hb3 : ((b : Bs) : G) ^ 3 = 1 := hS.1.1.2.1.2.1.2 (b : Bs) b.2
  let β : MulAut ↥L := L.normalizerMonoidHom ⟨(b : G), hN b.2⟩
  have hβ : β = MulAut.conj (⟨a, haL⟩ : ↥L) := by
    ext l
    show ((L.normalizerMonoidHom ⟨(b : G), hN b.2⟩) l : G) = _
    rw [Subgroup.normalizerMonoidHom_apply_apply_coe, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv]
    exact ha (l : G) l.2
  have hβ3 : β ^ 3 = 1 := by
    show (L.normalizerMonoidHom ⟨(b : G), hN b.2⟩) ^ 3 = 1
    rw [← map_pow]
    have hg3 : (⟨(b : G), hN b.2⟩ : Subgroup.normalizer (L : Set G)) ^ 3 = 1 := by
      apply Subtype.ext
      exact hb3
    rw [hg3, map_one]
  have hconj_a3 : MulAut.conj (⟨a ^ 3, L.pow_mem haL 3⟩ : ↥L) = 1 := by
    have hx : (⟨a ^ 3, L.pow_mem haL 3⟩ : ↥L) = (⟨a, haL⟩ : ↥L) ^ 3 := rfl
    rw [hx, map_pow]
    rw [← hβ]
    exact hβ3
  have hval : (⟨a ^ 3, L.pow_mem haL 3⟩ : ↥L) = 1 :=
    ggQTwoE6_eq_one_of_conj_eq_one hZ hconj_a3
  exact congrArg Subtype.val hval

theorem ggQTwoE6_mem_inf_L_of_mem_Bs
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    ∀ b : Bs, ∃ a : G, a ∈ Bs ∧ a ∈ L ∧
      ∀ l ∈ L, (b : G) * l * (b : G)⁻¹ = a * l * a⁻¹ := by
  intro b
  obtain ⟨a, haL, ha⟩ := ggQTwoE6_innerOn_L hq2 htag hmark b
  exact ⟨a, hS.1.1.2.1.2.2.2 a
    (ggQTwoE6_centralizes_of_innerOn_L hS hq2 htag hmark haL ha)
    (ggQTwoE6_pow_three_of_innerOn_L hS hq2 htag hmark haL ha), haL, ha⟩

theorem ggQTwoE6_eq_sup_inf_L
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    Bs = (Bs ⊓ Subgroup.centralizer (L : Set G)) ⊔ (Bs ⊓ L) := by
  classical
  have hBelem : IsElemAbelian 3 Bs := hS.1.1.2.1.2.1
  refine le_antisymm ?_ (sup_le inf_le_left inf_le_left)
  intro b hb
  obtain ⟨a, haBs, haL, ha⟩ := ggQTwoE6_mem_inf_L_of_mem_Bs hS hq2 htag hmark ⟨b, hb⟩
  have hcC : a⁻¹ * b ∈ Subgroup.centralizer (L : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro l hl
    have h1 : (a⁻¹ * b) * l * (a⁻¹ * b)⁻¹ = l := by
      calc (a⁻¹ * b) * l * (a⁻¹ * b)⁻¹ = a⁻¹ * (b * l * b⁻¹) * a := by group
        _ = a⁻¹ * (a * l * a⁻¹) * a := by rw [ha l hl]
        _ = l := by group
    calc l * (a⁻¹ * b) = ((a⁻¹ * b) * l * (a⁻¹ * b)⁻¹) * (a⁻¹ * b) := by rw [h1]
      _ = (a⁻¹ * b) * l := by group
  have hb_eq : b = (a⁻¹ * b) * a := by
    have hba : b * a = a * b :=
      (CFSG.commute_of_mem_of_isMulCommutative hBelem.1 hb haBs).eq
    calc b = a⁻¹ * (a * b) := by group
      _ = a⁻¹ * (b * a) := by rw [hba]
      _ = (a⁻¹ * b) * a := by group
  rw [hb_eq]
  exact Subgroup.mul_mem_sup
    (Subgroup.mem_inf.mpr ⟨Bs.mul_mem (Bs.inv_mem haBs) hb, hcC⟩)
    (Subgroup.mem_inf.mpr ⟨haBs, haL⟩)

theorem ggQTwoE6_disjoint_centralizer_L
    {G : Type} [Group G] [Finite G] {Bs L : Subgroup G} {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    (Bs ⊓ Subgroup.centralizer (L : Set G)) ⊓ (Bs ⊓ L) = ⊥ := by
  have hZ : Subgroup.center ↥L = ⊥ :=
    ggQTwoE6_center_bot L hmark.1 (ggQTwoE6_hasLabel_E6 (_B := Bs) hq2 htag hmark)
  rw [eq_bot_iff]
  rintro y ⟨hyC, hyL⟩
  have hyZ : (⟨y, hyL.2⟩ : ↥L) ∈ Subgroup.center ↥L := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hyC.2 z z.2
  rw [hZ, Subgroup.mem_bot] at hyZ
  exact congrArg Subtype.val hyZ

theorem ggQTwoE6_card_meet_L_lower
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    3 ^ 4 ≤ Nat.card ↥(Bs ⊓ L) := by
  have hsplit : Bs = (Bs ⊓ Subgroup.centralizer (L : Set G)) ⊔ (Bs ⊓ L) :=
    ggQTwoE6_eq_sup_inf_L hS hq2 htag hmark
  have hdisj := ggQTwoE6_disjoint_centralizer_L hq2 htag hmark
  have hcomm : ∀ a ∈ Bs ⊓ Subgroup.centralizer (L : Set G),
      ∀ b ∈ Bs ⊓ L, Commute a b := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp ha.2 b hb.2).symm
  have hcard : Nat.card Bs = Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) *
      Nat.card ↥(Bs ⊓ L) := by
    conv_lhs => rw [hsplit]
    rw [CFSG.card_sup_eq_mul_of_commute (Bs ⊓ Subgroup.centralizer (L : Set G)) (Bs ⊓ L)
      hcomm hdisj]
  have hBs5 : Nat.card Bs = 3 ^ 5 := ggQTwoE6_card_Bs hS hq2 htag hmark
  have hC3 : Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ 3 :=
    ggQTwoE6_card_meet_centralizer_L_le_three hS
  have h1 : Nat.card ↥(Bs ⊓ L) *
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) = 3 ^ 5 := by
    calc Nat.card ↥(Bs ⊓ L) * Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G))
        = Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) * Nat.card ↥(Bs ⊓ L) :=
          mul_comm _ _
      _ = Nat.card Bs := hcard.symm
      _ = 3 ^ 5 := hBs5
  have h2 : Nat.card ↥(Bs ⊓ L) *
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (L : Set G)) ≤ Nat.card ↥(Bs ⊓ L) * 3 :=
    Nat.mul_le_mul_left _ hC3
  have h3 : 3 ^ 5 ≤ Nat.card ↥(Bs ⊓ L) * 3 := by rw [← h1]; exact h2
  have h4 : (3 : ℕ) ^ 5 = 3 ^ 4 * 3 := by norm_num
  rw [h4] at h3
  exact Nat.le_of_mul_le_mul_right h3 (by norm_num)

theorem ggQTwoE6_card_meet_L_upper
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    Nat.card ↥(Bs ⊓ L) ≤ 3 ^ 4 := by
  have hSStar : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hxBs : x ∈ Bs := hS.1.1.2.1.1 hSStar.2.1
  have hxL : x ∉ L := ggQTwoE6_x_not_mem_L hS hq2 htag hmark
  have hTne : (Bs ⊓ L).subgroupOf Bs ≠ ⊤ := by
    intro htop
    have hxT : (⟨x, hxBs⟩ : ↥Bs) ∈ (Bs ⊓ L).subgroupOf Bs := by
      rw [htop]
      exact Subgroup.mem_top _
    exact hxL (Subgroup.mem_subgroupOf.mp hxT).2
  have hlt : 1 < ((Bs ⊓ L).subgroupOf Bs).index :=
    Subgroup.one_lt_index_of_ne_top hTne
  have hcardT : Nat.card ((Bs ⊓ L).subgroupOf Bs) = Nat.card ↥(Bs ⊓ L) :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_left).toEquiv
  have hBs5 : Nat.card Bs = 3 ^ 5 := ggQTwoE6_card_Bs hS hq2 htag hmark
  have hmul : Nat.card ((Bs ⊓ L).subgroupOf Bs) *
      ((Bs ⊓ L).subgroupOf Bs).index = 3 ^ 5 := by
    rw [Subgroup.card_mul_index, hBs5]
  have hdvd : ((Bs ⊓ L).subgroupOf Bs).index ∣ 3 ^ 5 := by
    refine ⟨Nat.card ((Bs ⊓ L).subgroupOf Bs), ?_⟩
    rw [mul_comm, ← hmul]
  obtain ⟨m, -, hmk⟩ :=
    (Nat.dvd_prime_pow (by norm_num : Nat.Prime 3)).mp hdvd
  have hm0 : m ≠ 0 := by
    rintro rfl
    rw [hmk, pow_zero] at hlt
    exact lt_irrefl 1 hlt
  have h3le : 3 ≤ ((Bs ⊓ L).subgroupOf Bs).index := by
    rw [hmk]
    calc 3 = 3 ^ 1 := by norm_num
      _ ≤ 3 ^ m := Nat.pow_le_pow_right (by norm_num) (Nat.one_le_iff_ne_zero.mpr hm0)
  have h1 : Nat.card ↥(Bs ⊓ L) * 3 ≤ 3 ^ 5 := by
    calc Nat.card ↥(Bs ⊓ L) * 3 = Nat.card ((Bs ⊓ L).subgroupOf Bs) * 3 := by rw [hcardT]
      _ ≤ Nat.card ((Bs ⊓ L).subgroupOf Bs) * ((Bs ⊓ L).subgroupOf Bs).index :=
          Nat.mul_le_mul_left _ h3le
      _ = 3 ^ 5 := hmul
  have h4 : (3 : ℕ) ^ 5 = 3 ^ 4 * 3 := by norm_num
  rw [h4] at h1
  exact Nat.le_of_mul_le_mul_right h1 (by norm_num)

theorem ggQTwoE6_card_meet_L
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    Nat.card ↥(Bs ⊓ L) = 3 ^ 4 :=
  le_antisymm (ggQTwoE6_card_meet_L_upper hS hq2 htag hmark)
    (ggQTwoE6_card_meet_L_lower hS hq2 htag hmark)

theorem ggQTwoE6_exists_lift_mem_Bs
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x z : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hzD : z ∈ D) (hzx : z ∉ Subgroup.zpowers x) :
    ∃ k ∈ L, k ∈ Bs ∧ k ^ 3 = 1 ∧ k ≠ 1 ∧
      (∀ l ∈ L, z * l * z⁻¹ = k⁻¹ * l * k) ∧
      L ⊓ Subgroup.centralizer ({z} : Set G) =
        L ⊓ Subgroup.centralizer ({k} : Set G) := by
  classical
  obtain ⟨k, hkL, hkconj, hz3, hzN⟩ := ggQTwoE6_lift_exists_k hS hq2 htag hmark hzD
  have hzBs : z ∈ Bs := hS.1.1.2.1.1 (hS.1.1.2.2.1.1 hzD)
  obtain ⟨a, haBs, haL, ha⟩ :=
    ggQTwoE6_mem_inf_L_of_mem_Bs hS hq2 htag hmark ⟨z, hzBs⟩
  have hZ : Subgroup.center ↥L = ⊥ :=
    ggQTwoE6_center_bot L hmark.1 (ggQTwoE6_hasLabel_E6 (_B := B) hq2 htag hmark)
  have hconj : MulAut.conj (⟨a, haL⟩ : ↥L) =
      MulAut.conj (⟨k⁻¹, L.inv_mem hkL⟩ : ↥L) := by
    ext l
    rw [MulAut.conj_apply, MulAut.conj_apply]
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, inv_inv]
    calc a * (l : G) * a⁻¹ = (z : G) * (l : G) * (z : G)⁻¹ := (ha (l : G) l.2).symm
      _ = k⁻¹ * (l : G) * k := hkconj (l : G) l.2
  have haeq : a = k⁻¹ := congrArg Subtype.val
    (ggQTwoE6_conj_injective_of_center_eq_bot hZ hconj)
  have hkBs : k ∈ Bs := by
    have hk : k = a⁻¹ := by rw [haeq]; group
    rw [hk]
    exact Bs.inv_mem haBs
  have hk3 : k ^ 3 = 1 :=
    ggQTwoE6_lift_k3_eq_one hkL (ggQTwoE6_lift_k3_centralizes hzN hz3 hkconj) hZ
  have hk1 : k ≠ 1 := ggQTwoE6_lift_k_ne_one hS hzD hzx hkconj
  exact ⟨k, hkL, hkBs, hk3, hk1, hkconj, ggQTwoE6_lift_centralizer_eq hkconj⟩

theorem ggQTwoE6_J_subgroupOf_label {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hJ : GGHasLabel ⟨.twD, 4, 1⟩ (J ⧸ Subgroup.center J)) :
    GGHasLabel ⟨.twD, 4, 1⟩
      (↥(J.subgroupOf L) ⧸ Subgroup.center ↥(J.subgroupOf L)) := by
  have hJc0 : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hS.1.1.2.2.1.2.2.2.2.2.1
  have hJleL : J ≤ L := fun j hj => (hJc0.1 hj).1
  exact ggHasLabel_quotCenter_of_mulEquiv (Subgroup.subgroupOfEquivOfLe hJleL).symm hJ

theorem ggQTwoE6_card_inf_centralizer_J
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    3 ^ 2 ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) := by
  have hB : Bs = B := ggQTwoE6_B_eq_Bstar hS hq2 htag hmark
  have hJc0 : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hS.1.1.2.2.1.2.2.2.2.2.1
  have hDleB : D ≤ B := hS.1.1.2.2.1.1
  have hJleCD : J ≤ Subgroup.centralizer (D : Set G) := fun j hj => (hJc0.1 hj).2
  have hDleCJ : D ≤ Subgroup.centralizer (J : Set G) := by
    intro d hd
    rw [Subgroup.mem_centralizer_iff]
    intro j hj
    exact (Subgroup.mem_centralizer_iff.mp (hJleCD hj) d hd).symm
  have hDle : D ≤ Bs ⊓ Subgroup.centralizer (J : Set G) := by
    intro d hd
    exact Subgroup.mem_inf.mpr ⟨by rw [hB]; exact hDleB hd, hDleCJ hd⟩
  have hDcard : Nat.card D = 9 := by
    have := hS.1.1.2.2.1.2.2.1
    rw [this]
    norm_num
  have hle := Subgroup.card_le_of_le hDle
  rw [hDcard] at hle
  have h9 : (3 : ℕ) ^ 2 = 9 := by norm_num
  rw [h9]
  exact hle

theorem ggQTwoE6_J_meet_data
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x z : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hzD : z ∈ D) (hzx : z ∉ Subgroup.zpowers x) :
    ∃ k : G, ∃ hkL : k ∈ L, k ∈ Bs ∧ k ^ 3 = 1 ∧ k ≠ 1 ∧ J ≤ L ∧
      J.subgroupOf L = LargeEvenLayer
        (Subgroup.centralizer ({(⟨k, hkL⟩ : ↥L)} : Set ↥L)) ∧
      IsComponentOf (J.subgroupOf L)
        (Subgroup.centralizer ({(⟨k, hkL⟩ : ↥L)} : Set ↥L)) := by
  obtain ⟨k, hkL, hkBs, hk3, hk1, -, hCeq⟩ :=
    ggQTwoE6_exists_lift_mem_Bs hS hq2 htag hmark hzD hzx
  have hJc0 : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hS.1.1.2.2.1.2.2.2.2.2.1
  have hSStar : LargeEvenSStar 3 B x L := hS.1.1.1.2.2.2.2.2.2.1
  have hDgen : D = Subgroup.zpowers x ⊔ Subgroup.zpowers z := ggQTwoE6_D_eq hS hzD hzx
  have hCD := ggQTwoE6_meet_centralizer_D_eq (ggQTwoE6_centralizer_D_eq
    hS.1.1.2.2.1.2.2.2.1 hzD hDgen) hSStar.2.2.2.1.1
  have hJ0 : J = LargeEvenLayer (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hS.1.1.2.2.1.2.2.2.2.1
  have hJlay : J = LargeEvenLayer (L ⊓ Subgroup.centralizer ({k} : Set G)) := by
    rw [hJ0, hCD, hCeq]
  have hJc : IsComponentOf J (L ⊓ Subgroup.centralizer ({k} : Set G)) := by
    rw [hCD, hCeq] at hJc0
    exact hJc0
  obtain ⟨hJleL, hJ', hJc'⟩ := ggR4Meet_transport hkL hJlay hJc
  exact ⟨k, hkL, hkBs, hk3, hk1, hJleL, hJ', hJc'⟩

theorem ggQTwoE6_D4_layer_elemAbelian {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) :
    IsElemAbelian 3 ((Bs ⊓ L).subgroupOf L) := by
  refine ⟨⟨⟨fun y z => ?_⟩⟩, ?_⟩
  · apply Subtype.ext
    apply Subtype.ext
    simpa only [Subgroup.coe_mul] using (CFSG.commute_of_mem_of_isMulCommutative
      hS.1.1.2.1.2.1.1 (Subgroup.mem_subgroupOf.mp y.2).1
        (Subgroup.mem_subgroupOf.mp z.2).1).eq
  · intro y hy
    apply Subtype.ext
    exact hS.1.1.2.1.2.1.2 ((y : ↥L) : G) (Subgroup.mem_subgroupOf.mp hy).1

theorem ggQTwoE6_D4_layer_le_centralizer {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J) {k : G}
    (hkL : k ∈ L) (hkBs : k ∈ Bs) :
    (Bs ⊓ L).subgroupOf L ≤
      Subgroup.centralizer ({(⟨k, hkL⟩ : ↥L)} : Set ↥L) := by
  intro y hy
  rw [Subgroup.mem_centralizer_singleton_iff]
  exact Subtype.ext (CFSG.commute_of_mem_of_isMulCommutative hS.1.1.2.1.2.1.1
    (Subgroup.mem_subgroupOf.mp hy).1 hkBs).eq

theorem ggQTwoE6_D4_layer_card
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L) :
    Nat.card ↥((Bs ⊓ L).subgroupOf L) = 3 ^ 4 :=
  (Nat.card_congr (Subgroup.subgroupOfEquivOfLe inf_le_right).toEquiv).trans
    (ggQTwoE6_card_meet_L hS hq2 htag hmark)

theorem ggQTwoE6_D4_layer_meet {G : Type} [Group G] {Bs L J : Subgroup G} (hJleL : J ≤ L) :
    Nat.card ↥((Bs ⊓ L).subgroupOf L ⊓ J.subgroupOf L) = Nat.card ↥(Bs ⊓ J) := by
  have hEq : (Bs ⊓ L).subgroupOf L ⊓ J.subgroupOf L = (Bs ⊓ J).subgroupOf L := by
    ext x
    simp only [Subgroup.mem_inf, Subgroup.mem_subgroupOf]
    constructor
    · rintro ⟨⟨hxB, -⟩, hxJ⟩
      exact ⟨hxB, hxJ⟩
    · rintro ⟨hxB, hxJ⟩
      exact ⟨⟨hxB, hJleL hxJ⟩, hxJ⟩
  rw [hEq]
  exact Nat.card_congr (Subgroup.subgroupOfEquivOfLe (inf_le_right.trans hJleL)).toEquiv

theorem ggQTwoE6_D4_opposite_layer
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    {k : G} (hkL : k ∈ L) (hkBs : k ∈ Bs) (hJleL : J ≤ L) :
    ∃ E' : Subgroup ↥L, IsElemAbelian 3 E' ∧ Nat.card E' = 3 ^ 4 ∧
      E' ≤ Subgroup.centralizer ({(⟨k, hkL⟩ : ↥L)} : Set ↥L) ∧
      Nat.card ↥(E' ⊓ J.subgroupOf L) = Nat.card ↥(Bs ⊓ J) :=
  ⟨(Bs ⊓ L).subgroupOf L, ggQTwoE6_D4_layer_elemAbelian hS,
    ggQTwoE6_D4_layer_card hS hq2 htag hmark,
    ggQTwoE6_D4_layer_le_centralizer hS hkL hkBs,
    ggQTwoE6_D4_layer_meet hJleL⟩

theorem ggQTwoE6_card_inf_J
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hJ : GGHasLabel ⟨.twD, 4, 1⟩ (J ⧸ Subgroup.center J)) :
    3 ^ 3 ≤ Nat.card ↥(Bs ⊓ J) := by
  have hperfL : Group.IsPerfect ↥L := Group.isPerfect_def.2 hmark.1
  obtain ⟨z, hzD, hzx⟩ := ggQTwoE6_exists_z_in_D hS
  obtain ⟨k, hkL, hkBs, hk3, hk1, hJleL, hJ', hJc'⟩ :=
    ggQTwoE6_J_meet_data hS hq2 htag hmark hzD hzx
  obtain ⟨E', hE, hcardE, hEz, hcardEJ⟩ :=
    ggQTwoE6_D4_opposite_layer hS hq2 htag hmark hkL hkBs hJleL
  have hH6 : GGHasLabel ⟨.E6, 0, 1⟩ (↥L ⧸ Subgroup.center ↥L) :=
    ggQTwoE6_hasLabel_E6 (_B := B) hq2 htag hmark
  have hz1 : (⟨k, hkL⟩ : ↥L) ≠ 1 := fun h => hk1 (congrArg Subtype.val h)
  have hz3' : (⟨k, hkL⟩ : ↥L) ^ 3 = 1 := Subtype.ext hk3
  have hle := ggE6OppOrderThree_card_le (H := ↥L) (f := 1) le_rfl
    (Or.inl ⟨hH6, by norm_num⟩) hz1 hz3' hJ' hJc'
    (Or.inr (Or.inr (ggQTwoE6_J_subgroupOf_label hS hJ))) hEz hE
  rw [hcardE, hcardEJ] at hle
  have h34 : (3 : ℕ) ^ 4 = 3 * 3 ^ 3 := by norm_num
  rw [h34] at hle
  exact Nat.le_of_mul_le_mul_left hle (by norm_num)
theorem ggQTwoE6_disjoint_centralizer_J
    {G : Type} [Group G] [Finite G]
    {B Bs : Subgroup G} {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    (hJ : GGHasLabel ⟨.twD, 4, 1⟩ (J ⧸ Subgroup.center J)) :
    (Bs ⊓ Subgroup.centralizer (J : Set G)) ⊓ (Bs ⊓ J) = ⊥ := by
  have hJc0 : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hS.1.1.2.2.1.2.2.2.2.2.1
  have hZJ : Subgroup.center ↥J = ⊥ := ggQTwoE6_D4_center_bot hJc0.2.2.1 hJ
  rw [eq_bot_iff]
  rintro y ⟨hyC, hyJ⟩
  have hyZ : (⟨y, hyJ.2⟩ : ↥J) ∈ Subgroup.center ↥J := by
    rw [Subgroup.mem_center_iff]
    intro z
    apply Subtype.ext
    exact Subgroup.mem_centralizer_iff.mp hyC.2 z z.2
  rw [hZJ, Subgroup.mem_bot] at hyZ
  exact congrArg Subtype.val hyZ

theorem ggQTwoE6_bstar_eq_sup_L
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hJ : GGHasLabel ⟨.twD, 4, 1⟩ (J ⧸ Subgroup.center J)) :
    Bs = (Bs ⊓ Subgroup.centralizer (J : Set G)) ⊔ (Bs ⊓ J) := by
  classical
  have hle : (Bs ⊓ Subgroup.centralizer (J : Set G)) ⊔ (Bs ⊓ J) ≤ Bs :=
    sup_le inf_le_left inf_le_left
  have hcomm : ∀ a ∈ Bs ⊓ Subgroup.centralizer (J : Set G),
      ∀ b ∈ Bs ⊓ J, Commute a b := by
    intro a ha b hb
    exact (Subgroup.mem_centralizer_iff.mp ha.2 b hb.2).symm
  have hdisj := ggQTwoE6_disjoint_centralizer_J hS hJ
  have hsupcard : Nat.card ↥((Bs ⊓ Subgroup.centralizer (J : Set G)) ⊔ (Bs ⊓ J)) =
      Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) * Nat.card ↥(Bs ⊓ J) := by
    rw [CFSG.card_sup_eq_mul_of_commute (Bs ⊓ Subgroup.centralizer (J : Set G))
      (Bs ⊓ J) hcomm hdisj]
  have hcardCJ := ggQTwoE6_card_inf_centralizer_J hS hq2 htag hmark
  have hcardBJ := ggQTwoE6_card_inf_J hS hq2 htag hmark hJ
  have hcardBs : Nat.card Bs = 3 ^ 5 := ggQTwoE6_card_Bs hS hq2 htag hmark
  have hcardle : Nat.card Bs ≤
      Nat.card ↥((Bs ⊓ Subgroup.centralizer (J : Set G)) ⊔ (Bs ⊓ J)) := by
    rw [hcardBs, hsupcard]
    calc (3 : ℕ) ^ 5 = 3 ^ 2 * 3 ^ 3 := by norm_num
      _ ≤ Nat.card ↥(Bs ⊓ Subgroup.centralizer (J : Set G)) * Nat.card ↥(Bs ⊓ J) :=
          Nat.mul_le_mul hcardCJ hcardBJ
  exact (Subgroup.eq_of_le_of_card_ge hle hcardle).symm

noncomputable abbrev ggQTwoE6_Q : QuadraticForm (ZMod 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2) :=
  CFSG.LieType.Universal.Spin.quadMinus 4 (ZMod 2) 1 1

noncomputable abbrev ggQTwoE6_Q₀ : (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2) → ZMod 2 :=
  CFSG.Open.StatedQuadMinus 4 (ZMod 2) 1 1

noncomputable abbrev ggQTwoE6_Omega : Subgroup ((Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2) ≃ₗ[ZMod 2]
    (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2)) :=
  CFSG.RankThree.Classical2.orthDerived ggQTwoE6_Q

noncomputable abbrev ggQTwoE6_eta :
    ↥(CFSG.Open.StatedOmega ggQTwoE6_Q₀) ≃* ↥ggQTwoE6_Omega :=
  CFSG.RankThree.PartOne.statedOmegaOrthEquiv
    (CFSG.LieType.Universal.Spin.coe_quadMinus 4 (ZMod 2) 1 1)

noncomputable abbrev ggQTwoE6_etaH :
    ↥(CFSG.Open.StatedOmega ggQTwoE6_Q₀) →* ↥ggQTwoE6_Omega :=
  ggQTwoE6_eta.toMonoidHom

theorem ggQTwoE6_Q_nondegenerate : (QuadraticMap.polarBilin ggQTwoE6_Q).Nondegenerate :=
  CFSG.LieType.Universal.Spin.nondegenerate_polarBilin_quadMinus 4 (ZMod 2) (by decide)

theorem ggQTwoE6_Q_not_isPlusType :
    ¬ CFSG.GroupTheory.WeirSylow.IsPlusType ggQTwoE6_Q :=
  CFSG.GroupTheory.WeirSylow.not_isPlusType_quadMinus (n := 4) (K := ZMod 2)
    (b := 1) (c := 1) (by norm_num) (by decide)

theorem ggQTwoE6_Q_finrank :
    Module.finrank (ZMod 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2) = 2 * 4 := by
  rw [Module.finrank_fintype_fun_eq_card, Fintype.card_sum, Fintype.card_sum,
    Fintype.card_fin]
  norm_num

theorem ggQTwoE6_D4_E_elemAbelian {G : Type} [Group G] [Finite G] {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting 3 B Bs x L D J)
    {φ : ↥(CFSG.Open.StatedOmega ggQTwoE6_Q₀) →* G} (hφi : Function.Injective φ) :
    IsElemAbelian 3 (((Bs ⊓ J).comap φ).map ggQTwoE6_etaH) := by
  have hBelem := hS.1.1.2.1.2.1
  have hCommBsJ : IsMulCommutative ↥(Bs ⊓ J) := by
    refine ⟨⟨fun a b => ?_⟩⟩
    apply Subtype.ext
    exact (CFSG.commute_of_mem_of_isMulCommutative hBelem.1 a.2.1 b.2.1).eq
  have hCommComap : IsMulCommutative ↥((Bs ⊓ J).comap φ) :=
    Subgroup.comap_injective_isMulCommutative (Bs ⊓ J) hφi
  have hCommMap : IsMulCommutative ↥(((Bs ⊓ J).comap φ).map ggQTwoE6_etaH) :=
    Subgroup.map_isMulCommutative ((Bs ⊓ J).comap φ) ggQTwoE6_etaH
  refine ⟨hCommMap, ?_⟩
  intro y hy
  obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.mp hy
  have hy3 : y' ^ 3 = 1 := by
    apply hφi
    rw [map_pow, map_one]
    exact hBelem.2 (φ y') hy'.1
  rw [← hyy, ← map_pow, hy3, map_one]

theorem ggQTwoE6_D4_E_le_Bs {G : Type} [Group G] {Bs J : Subgroup G}
    {φ : ↥(CFSG.Open.StatedOmega ggQTwoE6_Q₀) →* G} :
    ∀ y ∈ ((Bs ⊓ J).comap φ).map ggQTwoE6_etaH, φ (ggQTwoE6_eta.symm y) ∈ Bs := by
  intro y hy
  obtain ⟨y', hy', hyy⟩ := Subgroup.mem_map.mp hy
  rw [← hyy]
  simpa [ggQTwoE6_etaH] using hy'.1

theorem ggQTwoE6_D4_comm_inf_J {G : Type} [Group G] {Bs J : Subgroup G}
    {φ : ↥(CFSG.Open.StatedOmega ggQTwoE6_Q₀) →* G} (hφr : φ.range = J)
    {A : ↥(CFSG.Open.StatedOmega ggQTwoE6_Q₀)} {g : ↥ggQTwoE6_Omega}
    (hgA : ggQTwoE6_eta A = g)
    (hg : ∀ y ∈ ((Bs ⊓ J).comap φ).map ggQTwoE6_etaH, g * y = y * g) :
    ∀ c ∈ Bs ⊓ J, φ A * c = c * φ A := by
  intro c hc
  have hcrange : c ∈ φ.range := by rw [hφr]; exact hc.2
  obtain ⟨X, hX⟩ := MonoidHom.mem_range.mp hcrange
  rw [← hX] at hc ⊢
  have hXE : ggQTwoE6_eta X ∈ ((Bs ⊓ J).comap φ).map ggQTwoE6_etaH := by
    refine Subgroup.mem_map.mpr ⟨X, ?_, rfl⟩
    rw [Subgroup.mem_comap]
    exact hc
  have hcomm := hg (ggQTwoE6_eta X) hXE
  rw [← hgA] at hcomm
  rw [← map_mul, ← map_mul] at hcomm
  have h := congrArg φ (ggQTwoE6_eta.injective hcomm)
  rwa [map_mul, map_mul] at h

theorem ggQTwoE6_D4_E_comm_centralizer
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hJ : GGHasLabel ⟨.twD, 4, 1⟩ (J ⧸ Subgroup.center J))
    {φ : ↥(CFSG.Open.StatedOmega ggQTwoE6_Q₀) →* G} (hφr : φ.range = J)
    {g : ↥ggQTwoE6_Omega}
    (hg : ∀ y ∈ ((Bs ⊓ J).comap φ).map ggQTwoE6_etaH, g * y = y * g) (hg3 : g ^ 3 = 1) :
    φ (ggQTwoE6_eta.symm g) ∈ Bs := by
  let A : ↥(CFSG.Open.StatedOmega ggQTwoE6_Q₀) := ggQTwoE6_eta.symm g
  have hgA : ggQTwoE6_eta A = g := ggQTwoE6_eta.apply_symm_apply g
  have hA3 : A ^ 3 = 1 := by
    apply ggQTwoE6_eta.injective
    rw [map_pow, map_one, hgA, hg3]
  have hφA3 : (φ A) ^ 3 = 1 := by rw [← map_pow, hA3, map_one]
  have hφA_J : φ A ∈ J := by
    have h : φ A ∈ φ.range := MonoidHom.mem_range.mpr ⟨A, rfl⟩
    rwa [hφr] at h
  have hcommJ := ggQTwoE6_D4_comm_inf_J hφr hgA hg
  have hcent : φ A ∈ Subgroup.centralizer (Bs : Set G) := by
    rw [Subgroup.mem_centralizer_iff]
    intro b hb
    have hb' : b ∈ (Bs ⊓ Subgroup.centralizer (J : Set G)) ⊔ (Bs ⊓ J) := by
      rw [← ggQTwoE6_bstar_eq_sup_L hS hq2 htag hmark hJ]
      exact hb
    have hcommAJ : ∀ a ∈ Bs ⊓ Subgroup.centralizer (J : Set G),
        ∀ c ∈ Bs ⊓ J, Commute a c := by
      intro a ha c hc
      exact (Subgroup.mem_centralizer_iff.mp ha.2 c hc.2).symm
    obtain ⟨a, ha, c, hc, hac⟩ := (CFSG.mem_sup_of_commute hcommAJ).mp hb'
    have hya : a * φ A = φ A * a :=
      (Subgroup.mem_centralizer_iff.mp ha.2 (φ A) hφA_J).symm
    have hyc : c * φ A = φ A * c := (hcommJ c hc).symm
    rw [← hac]
    calc (a * c) * φ A = a * (c * φ A) := by group
      _ = a * (φ A * c) := by rw [hyc]
      _ = (a * φ A) * c := by group
      _ = (φ A * a) * c := by rw [hya]
      _ = φ A * (a * c) := by group
  exact hS.1.1.2.1.2.2.2 (φ A) hcent hφA3

theorem ggQTwoE6_D4_E_selfCentralizing
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hJ : GGHasLabel ⟨.twD, 4, 1⟩ (J ⧸ Subgroup.center J))
    {φ : ↥(CFSG.Open.StatedOmega ggQTwoE6_Q₀) →* G} (hφr : φ.range = J) :
    ∀ g : ↥ggQTwoE6_Omega,
      (∀ y ∈ ((Bs ⊓ J).comap φ).map ggQTwoE6_etaH, g * y = y * g) → g ^ 3 = 1 →
      g ∈ ((Bs ⊓ J).comap φ).map ggQTwoE6_etaH := by
  intro g hg hg3
  have hBs := ggQTwoE6_D4_E_comm_centralizer hS hq2 htag hmark hJ hφr hg hg3
  have hJ' : φ (ggQTwoE6_eta.symm g) ∈ J := by
    have h : φ (ggQTwoE6_eta.symm g) ∈ φ.range := MonoidHom.mem_range.mpr ⟨_, rfl⟩
    rwa [hφr] at h
  refine Subgroup.mem_map.mpr ⟨ggQTwoE6_eta.symm g, ?_, ggQTwoE6_eta.apply_symm_apply g⟩
  rw [Subgroup.mem_comap]
  exact Subgroup.mem_inf.mpr ⟨hBs, hJ'⟩

theorem ggQTwoE6_D4_frame
    {G : Type} [Group G] [Finite G] {B Bs : Subgroup G} {x : G} {L D J : Subgroup G}
    (hS : GGQTwoSetting 3 B Bs x L D J) {lab : LargeEvenLabel}
    (hq2 : GGLabQTwo 3 lab) (htag : lab.tag = .E6)
    (hmark : GGInnerDiagOnLabel (fun _ lab' => lab' = lab) 3 Bs L)
    (hJ : GGHasLabel ⟨.twD, 4, 1⟩ (J ⧸ Subgroup.center J)) :
    ∃ (φ : ↥(CFSG.Open.StatedOmega ggQTwoE6_Q₀) →* G)
      (η : ↥(CFSG.Open.StatedOmega ggQTwoE6_Q₀) ≃* ↥ggQTwoE6_Omega)
      (E : Subgroup ↥ggQTwoE6_Omega)
      (k : ℕ) (U : Fin k → Submodule (ZMod 2) (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2))
      (e : Fin k → ↥ggQTwoE6_Omega) (u : Fin k → (Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2))
      (c t : ZMod 2) (f f' : Fin 3 ⊕ Fin 3 ⊕ Fin 2 → ZMod 2),
      φ.range = J ∧ Function.Injective φ ∧ E = ((Bs ⊓ J).comap φ).map η.toMonoidHom ∧
      IsElemAbelian 3 E ∧
      (∀ g : ↥ggQTwoE6_Omega, (∀ y ∈ E, g * y = y * g) → g ^ 3 = 1 → g ∈ E) ∧
      (∀ y ∈ E, φ (η.symm y) ∈ Bs) ∧
      CFSG.StandardType.OmNsRootGen.IsCoherentFrame ggQTwoE6_Q 3 U e E u c t ∧
      k + 1 = 4 ∧
      f ∈ CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarPerp ggQTwoE6_Q (⨆ j, U j) ∧
      f' ∈ CFSG.LocalAnalysis.GLTheoremA.S172C.Cent.polarPerp ggQTwoE6_Q (⨆ j, U j) ∧
      ggQTwoE6_Q f = 0 ∧ ggQTwoE6_Q f' = 0 ∧
      QuadraticMap.polar ggQTwoE6_Q f f' = 1 := by
  classical
  have hJc0 : IsComponentOf J (L ⊓ Subgroup.centralizer (D : Set G)) :=
    hS.1.1.2.2.1.2.2.2.2.2.1
  obtain ⟨φ, hφr, hφi⟩ := ggQTwoE6_D4_omegaLift hJc0.2.2.1 hJ
  have hEab := ggQTwoE6_D4_E_elemAbelian hS hφi
  have hEsc := ggQTwoE6_D4_E_selfCentralizing hS hq2 htag hmark hJ hφr
  have hEBs := ggQTwoE6_D4_E_le_Bs (Bs := Bs) (J := J) (φ := φ)
  have htype : CFSG.GroupTheory.WeirSylow.IsPlusType ggQTwoE6_Q ↔ Odd 4 :=
    ⟨fun h => absurd h ggQTwoE6_Q_not_isPlusType, fun h => absurd h (by norm_num)⟩
  have hpq : 3 ∣ Nat.card (ZMod 2) + 1 := by norm_num [Nat.card_zmod]
  obtain ⟨k, U, e, u, c, t, f, f', hF, hk, hf, hf', hQf, hQf', hff'⟩ :=
    TorDNs.exists_nonFullCoherentFrame (Q := ggQTwoE6_Q) ggQTwoE6_Q_nondegenerate
      (p := 3) Nat.prime_three (by norm_num) hpq ggQTwoE6_Q_finrank (by norm_num)
      htype hEab hEsc
  exact ⟨φ, ggQTwoE6_eta, _, k, U, e, u, c, t, f, f', hφr, hφi, rfl, hEab, hEsc, hEBs,
    hF, hk, hf, hf', hQf, hQf', hff'⟩

end CFSG.StandardType

end
