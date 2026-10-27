module

public import CFSG.RankThree.PartTwo.Sec15.Sylow155R1Defs
public import CFSG.RankThree.PartTwo.Sec18.Item189KTypeBridge
public import CFSG.RankThree.PartTwo.Sec4.Item41Narrow
import CFSG.RankThree.PartTwo.Sec15.Sylow155R1FactLem
import CFSG.RankThree.PartTwo.Sec15.Sylow155T51Comp
import CFSG.RankThree.PartTwo.Sec15.Sylow155T51Lift
import CFSG.RankThree.PartTwo.Sec4.Item423StepsProof432Use
import CFSG.RankThree.PartTwo.Sec14.Item148HJProofPoint
import CFSG.GroupTheory.Fitting.LayerTopBot
public import CFSG.GroupTheory.ElementaryAbelianTransport

public section

namespace CFSG.RankThree.PartTwo.Sec15.Sylow155R1

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.RankThree.PartTwo.Sec13
  CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.LocalRank

theorem mem_zpowers_of_commute_of_maximal {M : Type} [Group M] [Finite M] (N : Subgroup M)
    [N.Normal] (hN : ¬ 3 ∣ Nat.card N) {A B : Subgroup M}
    (hA : CFSG.Assembly.IsElemAbelian 3 A)
    (hmax : ∀ E : Subgroup M, CFSG.Assembly.IsElemAbelian 3 E → A ≤ E → E = A)
    (hBZ : B ≤ Subgroup.center M) {a : M} (hAeq : A = B ⊔ Subgroup.zpowers a)
    {Y : Subgroup (M ⧸ N)} (haY : QuotientGroup.mk' N a ∈ Y)
    (hBY : B.map (QuotientGroup.mk' N) ⊓ Y = ⊥) :
    ∀ y ∈ Y, y * QuotientGroup.mk' N a = QuotientGroup.mk' N a * y → y ^ 3 = 1 →
      y ∈ Subgroup.zpowers (QuotientGroup.mk' N a) := by
  intro y hyY hycomm hy3
  have hA3 : IsPGroup 3 A := hA.isPGroup
  have hBtilde_central : B.map (QuotientGroup.mk' N) ≤ Subgroup.center (M ⧸ N) :=
    (Subgroup.map_mono hBZ).trans
      (Subgroup.map_center_le_center (QuotientGroup.mk'_surjective N))
  haveI hBnorm : (B.map (QuotientGroup.mk' N)).Normal :=
    Subgroup.normal_of_le_center hBtilde_central
  have hAtilde_eq : A.map (QuotientGroup.mk' N) =
      B.map (QuotientGroup.mk' N) ⊔ Subgroup.zpowers (QuotientGroup.mk' N a) := by
    rw [hAeq, Subgroup.map_sup, MonoidHom.map_zpowers]
  have hAtelem : CFSG.Assembly.IsElemAbelian 3 (A.map (QuotientGroup.mk' N)) := hA.map _
  have hcommA : ∀ e ∈ A.map (QuotientGroup.mk' N), e * y = y * e := by
    intro e he
    rw [hAtilde_eq] at he
    obtain ⟨b, hb, z, hz, rfl⟩ :=
      (Subgroup.mem_sup_of_normal_left (s := B.map (QuotientGroup.mk' N))
        (t := Subgroup.zpowers (QuotientGroup.mk' N a))).mp he
    have hbcomm : b * y = y * b := (Subgroup.mem_center_iff.mp (hBtilde_central hb) y).symm
    have hzcomm : z * y = y * z := by
      obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.mp hz
      exact (((commute_iff_eq _ _).mpr hycomm.symm).zpow_left k).eq
    calc (b * z) * y = b * (z * y) := by group
      _ = b * (y * z) := by rw [hzcomm]
      _ = (b * y) * z := by group
      _ = (y * b) * z := by rw [hbcomm]
      _ = y * (b * z) := by group
  have hE : CFSG.Assembly.IsElemAbelian 3
      (A.map (QuotientGroup.mk' N) ⊔ Subgroup.zpowers y) :=
    CFSG.RankThree.PartTwo.Sec15.isElemAbelian_sup_zpowers hAtelem hy3 hcommA
  obtain ⟨S, hAS, hSmap, hS_elem, -⟩ :=
    Sylow155T51.exists_elemAbelian_lift_le N hN hA3 hE le_sup_left
  have hSeq : S = A := hmax S hS_elem hAS
  have hEeq : A.map (QuotientGroup.mk' N) ⊔ Subgroup.zpowers y = A.map (QuotientGroup.mk' N) := by
    rw [← hSmap, hSeq]
  have hyA : y ∈ A.map (QuotientGroup.mk' N) := by
    rw [← hEeq]
    exact Subgroup.mem_sup_right (Subgroup.mem_zpowers y)
  rw [hAtilde_eq] at hyA
  obtain ⟨b, hb, z, hz, hbz⟩ :=
    (Subgroup.mem_sup_of_normal_left (s := B.map (QuotientGroup.mk' N))
      (t := Subgroup.zpowers (QuotientGroup.mk' N a))).mp hyA
  have hb_eq : b = y * z⁻¹ := by
    rw [← hbz]
    group
  have hbY : b ∈ Y := by
    rw [hb_eq]
    exact Y.mul_mem hyY (Y.inv_mem ((Subgroup.zpowers_le.mpr haY) hz))
  have hbBot : b ∈ (⊥ : Subgroup (M ⧸ N)) := by
    have hmem : b ∈ B.map (QuotientGroup.mk' N) ⊓ Y := ⟨hb, hbY⟩
    rwa [hBY] at hmem
  have hb1 : b = 1 := by simpa using hbBot
  rw [hb1, one_mul] at hbz
  rw [← hbz]
  exact hz

private theorem isPGroup_center_of_isComponent_three {X : Type*} [Group X] [Finite X]
    (hO : CFSG.pPrimeCore 3 X = ⊥) {L : Subgroup X} (hL : CFSG.IsComponent L) :
    IsPGroup 3 (Subgroup.center ↥L) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hle : (Subgroup.center ↥L).map L.subtype ≤ CFSG.pCore 3 X :=
    (CFSG.LocalCores.center_component_le_center_layer hL).trans
      (CFSG.WholeGroup.center_layer_le_pCore_of_pPrimeCore_eq_bot 3 hO)
  exact ((CFSG.pCore_isPGroup (p := 3) (G := X)).to_le hle).of_equiv
    (Subgroup.equivMapOfInjective (Subgroup.center ↥L) L.subtype L.subtype_injective).symm

theorem isSimple_pRank_one_of_unique_three {Q : Type} [Group Q] [Finite Q]
    (hO : CFSG.pPrimeCore 3 Q = ⊥) {Y At : Subgroup Q} [Y.Normal] (hY : CFSG.IsComponent Y)
    (hAt : IsPGroup 3 At) {x : Q} (hxA : x ∈ At) (hxY : x ∈ Y) (hx1 : x ≠ 1) (hx3 : x ^ 3 = 1)
    (hR1 : ∀ y ∈ Y, y * x = x * y → y ^ 3 = 1 → y ∈ Subgroup.zpowers x) :
    IsSimpleGroup ↥Y ∧ CFSG.Open.pRank 3 (⊤ : Subgroup ↥Y) = 1 ∧ ∃ a b : ↥Y, a * b ≠ b * a := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨P, hP⟩ := exists_isCyclic_sylow hAt hxA hxY hx1 hx3 hR1
  have hx'3 : (⟨x, hxY⟩ : ↥Y) ^ 3 = 1 := Subtype.ext (by simpa using hx3)
  have hx'1 : (⟨x, hxY⟩ : ↥Y) ≠ 1 := fun h => hx1 (congrArg Subtype.val h)
  have hR1' : ∀ y : ↥Y, y * ⟨x, hxY⟩ = ⟨x, hxY⟩ * y → y ^ 3 = 1 →
      y ∈ Subgroup.zpowers (⟨x, hxY⟩ : ↥Y) := by
    intro y hyc hy3
    have hy3' : (y : Q) ^ 3 = 1 := by simpa using congrArg Subtype.val hy3
    have hyc' : (y : Q) * x = x * (y : Q) := congrArg Subtype.val hyc
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (hR1 _ y.2 hyc' hy3')
    exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext (by simpa using hk)⟩
  obtain ⟨u, huY, hu3, v, hvY, huv⟩ :=
    Sylow155T51.exists_pow_three_not_commute_of_isComponent hO hY
  have hI : ∃ u : ↥Y, u ^ 3 = 1 ∧ ∃ y : ↥Y, u * y ≠ y * u :=
    ⟨⟨u, huY⟩, Subtype.ext (by simpa using hu3), ⟨v, hvY⟩, fun h => huv (congrArg Subtype.val h)⟩
  have hcen : Subgroup.center ↥Y = ⊥ :=
    center_eq_bot_of_unique_three hx'3 hR1' (isPGroup_center_of_isComponent_three hO hY) hI
  have hsimple : IsSimpleGroup ↥Y :=
    (((QuotientGroup.quotientMulEquivOfEq hcen).trans
      (QuotientGroup.quotientBot (G := ↥Y))).isSimpleGroup_congr).mp hY.1.2.1
  refine ⟨hsimple, le_antisymm (pRank_top_le_one_of_isCyclic_sylow P hP)
    (one_le_pRank_top_of_pow_three hx'3 hx'1), ?_⟩
  obtain ⟨u', hu'3, y, huy⟩ := hI
  exact ⟨u', y, huy⟩

private theorem normal_of_unique_isComponent {M : Type} [Group M] [Finite M] {B : Subgroup M}
    (hB : CFSG.Assembly.IsElemAbelian 3 B) (hB9 : Nat.card B = 9)
    (hBZ : B ≤ Subgroup.center M)
    (hmax : ∀ E : Subgroup M, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      (∃ U : Subgroup M, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set M)) →
      ∀ E' : Subgroup M, CFSG.Assembly.IsElemAbelian 3 E' → E ≤ E' → E' = E)
    {Y : Subgroup (M ⧸ CFSG.pPrimeCore 3 M)} (hY : CFSG.IsComponent Y) : Y.Normal := by
  have hYaut : ∀ ψ : (M ⧸ CFSG.pPrimeCore 3 M) ≃* (M ⧸ CFSG.pPrimeCore 3 M),
      Y.map ψ.toMonoidHom = Y := fun ψ =>
    Sylow155T51.eq_of_isComponent hB hB9 hBZ hmax
      (CFSG.LocalCores.isComponent_map_mulEquiv ψ hY) hY
  have hYn : ∀ q : M ⧸ CFSG.pPrimeCore 3 M,
      q ∈ Subgroup.normalizer (Y : Set (M ⧸ CFSG.pPrimeCore 3 M)) := fun q =>
    Subgroup.mem_normalizer_iff_map_conj_eq.mpr (hYaut (MulAut.conj q))
  exact ⟨fun n hn g => (Subgroup.mem_normalizer_iff.mp (hYn g) n).mp hn⟩

section Certified


theorem isSimple_rankOne_of_component
    {G : Type} [Group G] [Finite G]
    (h1 : Sec4.Item4_1LargePrime) {A L : Subgroup G} {c : G} (h : Sec14Std G A c L)
    {B C : Subgroup G} (hC : C = Subgroup.centralizer (B : Set G)) (hH : IsHyperplane A B)
    (hfree : ∀ b ∈ B, b ≠ 1 → Subgroup.zpowers b ∉ omegaA A)
    {Yc : Subgroup (↥C ⧸ CFSG.pPrimeCore 3 ↥C)} (hYc : CFSG.IsComponent Yc)
    (hcY : c ∈ (Yc.comap (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C))).map C.subtype)
    (hBY : (B.subgroupOf C).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) ⊓ Yc = ⊥) :
    IsSimpleGroup ↥Yc ∧ Sec18.IsRankOneType189 ↥Yc := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hT : TheoremFourHyp G := h.toTheoremFourHyp
  have hFE := (hT.partTwoF_eq_partTwoE h.partTwoS_eq).1
  have hA : A ∈ partTwoF G := h.mem_partTwoF
  have hAab : CFSG.Assembly.IsElemAbelian 3 A := hA.1
  have hA27 : Nat.card A = 27 := h.mem_partTwoE.2.1
  have hBA : B ≤ A := hH.1
  have hB9 : Nat.card B = 9 := by
    have h9 := hH.2
    rw [hA27] at h9
    omega
  have hCmem : ∀ x : G, x ∈ C ↔ ∀ b ∈ B, b * x = x * b := fun x => by
    rw [hC]
    exact Subgroup.mem_centralizer_iff
  have hcmem := mem_omegaA_iff.mp h.zpowers_mem_omegaA
  have hcA : c ∈ A := hcmem.1 (Subgroup.mem_zpowers c)
  have hco : orderOf c = 3 := by
    rw [← Nat.card_zpowers]
    exact hcmem.2.1
  have hc1 : c ≠ 1 := by
    intro hc
    rw [hc, orderOf_one] at hco
    omega
  have hcB : c ∉ B := fun hcB => hfree c hcB hc1 h.zpowers_mem_omegaA
  have hsup : B ⊔ Subgroup.zpowers c = A :=
    Sec14.Item148HJ.sup_zpowers_eq_of_isHyperplane hH hcA hcB
  have hAC : A ≤ C := fun x hx => (hCmem x).mpr fun b hb =>
    congrArg Subtype.val (hAab.1.is_comm.comm ⟨b, hBA hb⟩ ⟨x, hx⟩)
  have hBC : B ≤ C := hBA.trans hAC
  have hCtop : C ≠ ⊤ := by
    intro hCt
    have hZ : Subgroup.center G = ⊥ := by
      rcases hT.isSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center G) with h0 | h0
      · exact h0
      · exfalso
        obtain ⟨a, b, hab⟩ := hT.nonabelian
        exact hab (Subgroup.mem_center_iff.mp (h0 ▸ Subgroup.mem_top b) a)
    have hBZ : B ≤ Subgroup.center G := by
      intro b hb
      rw [Subgroup.mem_center_iff]
      intro g
      exact ((hCmem g).mp (hCt ▸ Subgroup.mem_top g) b hb).symm
    rw [hZ, le_bot_iff] at hBZ
    rw [hBZ, Subgroup.card_bot] at hB9
    norm_num at hB9
  have hC4 : SectionFourHyp ↥C := hT.sectionFourHyp hCtop
  have hY4 : SectionFourHyp ↥Yc :=
    Sec4.Item432Proof.sectionFourHyp_component_quot_pPrimeCore h1 hC4 hYc
  have hN3 : ¬ 3 ∣ Nat.card (CFSG.pPrimeCore 3 ↥C) :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp CFSG.pPrimeCore_coprime_card
  have hA'ab : CFSG.Assembly.IsElemAbelian 3 (A.subgroupOf C) := hAab.subgroupOf C
  have hB'ab : CFSG.Assembly.IsElemAbelian 3 (B.subgroupOf C) := (hAab.mono hBA).subgroupOf C
  have hB'9 : Nat.card (B.subgroupOf C) = 9 :=
    (Nat.card_congr (Subgroup.subgroupOfEquivOfLe hBC).toEquiv).trans hB9
  have hBZ : B.subgroupOf C ≤ Subgroup.center ↥C := by
    intro x hx
    rw [Subgroup.mem_center_iff]
    intro y
    exact Subtype.ext (((hCmem (y : G)).mp y.2) (x : G) hx).symm
  have hmaxC : ∀ E : Subgroup C, CFSG.Assembly.IsElemAbelian 3 E → Nat.card E = 27 →
      (∃ U : Subgroup C, U ≠ ⊥ ∧ IsPGroup 2 U ∧ E ≤ Subgroup.normalizer (U : Set C)) →
      ∀ E' : Subgroup C, CFSG.Assembly.IsElemAbelian 3 E' → E ≤ E' → E' = E := by
    rintro E hE hE27 ⟨U, hU1, hU2, hEU⟩ E' hE' hEE'
    have hmem : E.map C.subtype ∈ partTwoF G := by
      rw [hFE]
      refine ⟨hE.map _, ?_, U.map C.subtype, ?_, hU2.map _,
        (Subgroup.map_mono hEU).trans (Subgroup.le_normalizer_map _)⟩
      · rw [Subgroup.card_map_of_injective C.subtype_injective, hE27]
      · exact fun h0 => hU1 ((Subgroup.map_eq_bot_iff_of_injective U C.subtype_injective).mp h0)
    exact Subgroup.map_injective C.subtype_injective
      (hmem.2.1 _ (hE'.map _) (Subgroup.map_mono hEE'))
  have hA'max : ∀ E : Subgroup C, CFSG.Assembly.IsElemAbelian 3 E → A.subgroupOf C ≤ E →
      E = A.subgroupOf C := by
    intro E hE hAE'
    have hAEm : A ≤ E.map C.subtype := fun a ha =>
      ⟨⟨a, hAC ha⟩, hAE' (show (⟨a, hAC ha⟩ : C) ∈ A.subgroupOf C from ha), rfl⟩
    have hEq : E.map C.subtype = A := hA.2.1 _ (hE.map _) hAEm
    rw [← hEq]
    exact (Subgroup.comap_map_eq_self_of_injective C.subtype_injective E).symm
  haveI hYnormal : Yc.Normal := normal_of_unique_isComponent hB'ab hB'9 hBZ hmaxC hYc
  obtain ⟨c', hc'Y, hc'c⟩ := Subgroup.mem_map.mp hcY
  have hc'c' : (c' : G) = c := hc'c
  have hc'A : c' ∈ A.subgroupOf C := Subgroup.mem_subgroupOf.mpr (by rw [hc'c']; exact hcA)
  have hA'3 : IsPGroup 3 (A.subgroupOf C) := hA'ab.isPGroup
  have hinj := Sylow155T51.injective_mk_comp_subtype (CFSG.pPrimeCore 3 ↥C) hN3 hA'3
  have hc'3 : c' ^ 3 = 1 :=
    Subtype.ext (by rw [Subgroup.coe_pow, hc'c']; exact hAab.2 c hcA)
  have hx3 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) c' ^ 3 = 1 := by
    rw [← map_pow, hc'3, map_one]
  have hx1 : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) c' ≠ 1 := by
    intro hx
    have hsub : (⟨c', hc'A⟩ : A.subgroupOf C) = ⟨1, Subgroup.one_mem _⟩ := by
      apply hinj
      change QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) c' =
        QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) (1 : C)
      rw [map_one]
      exact hx
    have hc'1 : c' = 1 := congrArg Subtype.val hsub
    exact hc1 (by rw [← hc'c', hc'1]; rfl)
  have hxA : QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C) c' ∈
      (A.subgroupOf C).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C)) := ⟨c', hc'A, rfl⟩
  have hAt3 : IsPGroup 3 ((A.subgroupOf C).map (QuotientGroup.mk' (CFSG.pPrimeCore 3 ↥C))) :=
    (hA'ab.map _).isPGroup
  have hzp : (Subgroup.zpowers (c' : G)).subgroupOf C = Subgroup.zpowers c' := by
    ext y
    simp only [Subgroup.mem_subgroupOf, Subgroup.mem_zpowers_iff]
    constructor
    · rintro ⟨k, hk⟩
      exact ⟨k, Subtype.ext hk⟩
    · rintro ⟨k, hk⟩
      exact ⟨k, congrArg Subtype.val hk⟩
  have hAsub : A.subgroupOf C = B.subgroupOf C ⊔ Subgroup.zpowers c' := by
    have hsup' : B ⊔ Subgroup.zpowers (c' : G) = A := by
      rw [hc'c']
      exact hsup
    rw [← hsup', Subgroup.subgroupOf_sup hBC (Subgroup.zpowers_le.mpr c'.2), hzp]
  have hR1 := mem_zpowers_of_commute_of_maximal (CFSG.pPrimeCore 3 ↥C) hN3 hA'ab hA'max hBZ
    hAsub hc'Y hBY
  have hO : CFSG.pPrimeCore 3 (↥C ⧸ CFSG.pPrimeCore 3 ↥C) = ⊥ :=
    CFSG.pPrimeCore_quotient_pPrimeCore_eq_bot 3
  obtain ⟨hsimple, hrank, hnab⟩ :=
    isSimple_pRank_one_of_unique_three hO hYc hAt3 hxA hc'Y hx1 hx3 hR1
  haveI := hsimple
  obtain ⟨i, ⟨e⟩⟩ : Assembly.InCatalog ↥Yc :=
    KCore.KGroupAllSimple.catalogue_self (C := Assembly.InCatalog)
      Assembly.inCatalog_isoInvariant hY4.kGroup
  exact ⟨hsimple, Sec18.isRankOneType189_of_index hsimple hnab i e hrank⟩

theorem res1TypeFact_of
    (h1 : Sec4.Item4_1LargePrime) : Res1TypeFact := by
  intro G _ _ A c L Yc h hH hfree hcomp
  obtain ⟨hYc, hcY, hBY⟩ := hcomp
  exact isSimple_rankOne_of_component h1 h (C := Res1C A L) rfl hH hfree hYc hcY hBY

end Certified

end CFSG.RankThree.PartTwo.Sec15.Sylow155R1
