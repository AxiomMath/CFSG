module

public import CFSG.Timmesfeld.Bridge.OddRootDefs
import CFSG.Timmesfeld.Bridge.OddRootBasic
import CFSG.Timmesfeld.Bridge.OddRootSqOut
import CFSG.Timmesfeld.Bridge.OddRootOrbit
import CFSG.Timmesfeld.Bridge.OddLocalCommonY
import CFSG.Timmesfeld.Bridge.OddTranspMain
import CFSG.StronglyEmbedded.PSU3TwoElements
import CFSG.GroupTheory.ABGLocalTools.OddOrderLocal
public import CFSG.Timmesfeld.Bridge.Asc73Central

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Bridge.OddLocal
  CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki CFSG.Timmesfeld.Connectivity

variable {G : Type} [Group G] {D : Set G}

private theorem closure_ne_top_of_isMaxOrbit [Finite G] (h : Hyp G D) {c : G}
    (hc : c ∈ D) {E : Set G} (hE : IsMaxOrbit D c E) :
    Subgroup.closure E ≠ ⊤ := by
  intro htop
  have hle : Subgroup.closure E ≤ Subgroup.centralizer ({c} : Set G) := by
    rw [Subgroup.closure_le]
    intro x hx
    exact Subgroup.mem_centralizer_singleton_iff.mpr
      ((subset_commSet h.setup.normal hE hx).2.1)
  have hcCenter : c ∈ Subgroup.center G := by
    rw [Subgroup.mem_center_iff]
    intro g
    exact Subgroup.mem_centralizer_singleton_iff.mp (hle (htop ▸ Subgroup.mem_top g))
  have hZnormal : (Subgroup.zpowers c).Normal :=
    Subgroup.normal_of_le_center (Subgroup.zpowers_le.mpr hcCenter)
  have hZ2 : IsPGroup 2 (Subgroup.zpowers c) :=
    IsPGroup.of_card (n := 1) (by
      rw [Nat.card_zpowers, h.setup.oddT.orderOf_eq_two hc, pow_one])
  have hmem : c ∈ CFSG.pCore 2 G :=
    CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hZnormal hZ2
      (Subgroup.mem_zpowers c)
  rw [h.o2] at hmem
  have hc1 : c = 1 := Subgroup.mem_bot.mp hmem
  have hc2 : orderOf c = 2 := h.setup.oddT.orderOf_eq_two hc
  rw [hc1, orderOf_one] at hc2
  exact absurd hc2 (by decide)



private theorem false_of_mem_pCore_of_mem_E [Finite G] (h : Hyp G D)
    {c : G} {E : Set G} (hE : IsMaxOrbit D c E) {e f : G} (he : e ∈ E) (hf : f ∈ E)
    (hrE : rootSet D e ⊆ E) (hsq : SqOut ↥(rootGen D e f)) {d : G} (hd : d ∈ E)
    (hdQ : (⟨d, Subgroup.subset_closure hd⟩ : ↥(Subgroup.closure E)) ∈
      CFSG.pCore 2 ↥(Subgroup.closure E)) : False := by
  let H : Subgroup G := Subgroup.closure E
  let Q : Subgroup H := CFSG.pCore 2 H
  have hdH : d ∈ H := Subgroup.subset_closure hd
  have heH : e ∈ H := Subgroup.subset_closure he
  have hfH : f ∈ H := Subgroup.subset_closure hf
  have hclass : hClass H d = E := hClass_closure_eq h.setup hE hd
  have hdQ' : (⟨d, hdH⟩ : H) ∈ Q := hdQ
  have hEsubQ : ((↑) : H → G) ⁻¹' E ⊆ Q := by
    intro x hx
    have hxmem : (x : G) ∈ hClass H d := hclass ▸ hx
    obtain ⟨l, hl, hlx⟩ := hxmem
    let lH : H := ⟨l, hl⟩
    have hxconj : x = lH * ⟨d, hdH⟩ * lH⁻¹ := by
      ext
      simpa [lH] using hlx
    rw [hxconj]
    exact (inferInstance : Q.Normal).conj_mem _ hdQ' lH
  have hcltop : Subgroup.closure (((↑) : H → G) ⁻¹' E) = (⊤ : Subgroup H) := by
    simpa [H] using Subgroup.closure_preimage_eq_top (S := E)
  have hQtop : Q = ⊤ := by
    have hle : Subgroup.closure (((↑) : H → G) ⁻¹' E) ≤ Q :=
      (Subgroup.closure_le Q).mpr hEsubQ
    rw [hcltop] at hle
    exact eq_top_iff.mpr hle
  have hQ2 : IsPGroup 2 Q := CFSG.pCore_isPGroup
  have htop : IsPGroup 2 (⊤ : Subgroup H) :=
    hQ2.of_equiv (MulEquiv.subgroupCongr hQtop)
  have hH2 : IsPGroup 2 H := htop.of_equiv (Subgroup.topEquiv (G := H))
  have hXH : rootGen D e f ≤ H := by
    rw [rootGen, Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact hfH
    · exact Subgroup.subset_closure (hrE hy)
  exact not_sqOut_of_isPGroup (hH2.to_le hXH) hsq

private theorem pCore_quotient_mk_ne_one [Finite G] (h : Hyp G D) {c : G} {E : Set G}
    (hE : IsMaxOrbit D c E) {e f : G} (he : e ∈ E) (hf : f ∈ E)
    (hrE : rootSet D e ⊆ E) (hsq : SqOut ↥(rootGen D e f)) :
    ∀ d ∈ (((↑) : ↥(Subgroup.closure E) → G) ⁻¹' E),
      QuotientGroup.mk' (CFSG.pCore 2 ↥(Subgroup.closure E)) d ≠ 1 := by
  intro d hd h1
  exact false_of_mem_pCore_of_mem_E h hE he hf hrE hsq hd
    ((QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥(Subgroup.closure E)) d).mp h1)


private theorem map_rootGen_mem_of_generators {H : Subgroup G} {D : Set G} {e f : G}
    {P : Subgroup H} [P.Normal] {A : Subgroup (H ⧸ P)} (hXH : rootGen D e f ≤ H)
    (hgen : ∀ x (hx : x ∈ insert f (rootSet D e)),
      QuotientGroup.mk' P ⟨x, hXH (Subgroup.subset_closure hx)⟩ ∈ A) :
    ∀ x (hx : x ∈ rootGen D e f),
      QuotientGroup.mk' P ⟨x, hXH hx⟩ ∈ A := by
  intro x hx
  induction hx using Subgroup.closure_induction with
  | mem y hy => exact hgen y hy
  | one => exact A.one_mem
  | mul a b ha hb iha ihb =>
    have hprod : (⟨a * b,
          hXH (Subgroup.mul_mem (Subgroup.closure (insert f (rootSet D e))) ha hb)⟩ : H) =
        ⟨a, hXH ha⟩ * ⟨b, hXH hb⟩ := rfl
    rw [hprod, map_mul]
    exact A.mul_mem iha ihb
  | inv a ha iha =>
    have hinv : (⟨a⁻¹,
          hXH (Subgroup.inv_mem (Subgroup.closure (insert f (rootSet D e))) ha)⟩ : H) =
        (⟨a, hXH ha⟩ : H)⁻¹ := rfl
    rw [hinv, map_inv]
    exact A.inv_mem iha


private theorem sqOut_map_rootGen_pCore [Finite G] (h : Hyp G D) {c : G} {E : Set G}
    (hE : IsMaxOrbit D c E) {e f : G} (he : e ∈ E) (hf : f ∈ E)
    (hrE : rootSet D e ⊆ E) (hsq : SqOut ↥(rootGen D e f)) :
    SqOut ↥(rootGen
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(Subgroup.closure E)) ''
        (((↑) : ↥(Subgroup.closure E) → G) ⁻¹' E))
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(Subgroup.closure E))
        ⟨e, Subgroup.subset_closure he⟩)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(Subgroup.closure E))
        ⟨f, Subgroup.subset_closure hf⟩)) := by
  let H : Subgroup G := Subgroup.closure E
  let Q : Subgroup H := CFSG.pCore 2 H
  let π : H →* H ⧸ Q := QuotientGroup.mk' Q
  let EH : Set H := ((↑) : H → G) ⁻¹' E
  let Ē : Set (H ⧸ Q) := π '' EH
  have heH : e ∈ H := Subgroup.subset_closure he
  have hfH : f ∈ H := Subgroup.subset_closure hf
  have heEH : (⟨e, heH⟩ : H) ∈ EH := he
  have hfEH : (⟨f, hfH⟩ : H) ∈ EH := hf
  have heD : e ∈ D := (subset_commSet h.setup.normal hE he).1
  have hclass : hClass H e = E := hClass_closure_eq h.setup hE he
  have hsetupH : Asc72.Setup H EH := by
    have hgen : H ≤ Subgroup.closure (hClass H e) := by rw [hclass]
    have h1 := setup_hClass h.setup.oddT h.setup.normal heH heD hgen
    simpa [EH, hclass] using h1
  let X : Subgroup G := rootGen D e f
  have hXH : X ≤ H := by
    change rootGen D e f ≤ H
    rw [rootGen, Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact hfH
    · exact Subgroup.subset_closure (hrE hy)
  let πX : X →* H ⧸ Q := π.comp (Subgroup.inclusion hXH)
  let K' : Subgroup (H ⧸ Q) := rootGen Ē (π ⟨e, heH⟩) (π ⟨f, hfH⟩)
  have hroot_map : ∀ y (hy : y ∈ rootSet D e),
      π ⟨y, hXH (Subgroup.subset_closure (Set.mem_insert_of_mem f hy))⟩ ∈
        rootSet Ē (π ⟨e, heH⟩) := by
    intro y hy
    let yH : H := ⟨y, hXH (Subgroup.subset_closure (Set.mem_insert_of_mem f hy))⟩
    have hyH : yH ∈ EH := hrE hy
    refine ⟨⟨yH, hrE hy, rfl⟩, ?_⟩
    rintro z ⟨s, hs, rfl⟩
    have hsD : (s : G) ∈ D := (subset_commSet h.setup.normal hE hs).1
    rw [OddLocal.commute_iff_of_mem_pCore hsetupH.oddT
        (CFSG.pCore_isPGroup (p := 2) (G := H)) hyH hs,
      OddLocal.commute_iff_of_mem_pCore hsetupH.oddT
        (CFSG.pCore_isPGroup (p := 2) (G := H)) heEH hs]
    have h1 := commute_coe_iff (u := yH) (v := s)
    have h2 := commute_coe_iff (u := (⟨e, heH⟩ : H)) (v := s)
    exact h1.symm.trans ((hy.2 (s : G) hsD).trans h2)
  have himage : ∀ x : X, πX x ∈ K' := by
    intro x
    refine map_rootGen_mem_of_generators (P := Q) (A := K') hXH ?_ (x : G) x.2
    intro y hy
    rcases (Set.mem_insert_iff.mp hy) with rfl | hy
    · exact Subgroup.subset_closure (Set.mem_insert _ _)
    · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (hroot_map y hy))
  let φ : X →* K' := πX.codRestrict K' himage
  have hker : φ.ker = Q.comap (Subgroup.inclusion hXH) := by
    ext x
    rw [MonoidHom.mem_ker, Subgroup.mem_comap]
    constructor
    · intro hx
      exact (QuotientGroup.eq_one_iff (N := Q) ((Subgroup.inclusion hXH) x)).mp
        (congrArg Subtype.val hx)
    · intro hx
      exact Subtype.ext
        ((QuotientGroup.eq_one_iff (N := Q) ((Subgroup.inclusion hXH) x)).mpr hx)
  have hφ2 : IsPGroup 2 φ.ker := by
    rw [hker]
    exact (CFSG.pCore_isPGroup (p := 2) (G := H)).comap_of_injective
      (Subgroup.inclusion hXH) (Subgroup.inclusion_injective hXH)
  exact SqOut.map φ hφ2 hsq

private theorem not_sqOut_quotient_pCore [Finite G] (IH : NoSzBelow (Nat.card G))
    (h : Hyp G D) {c : G} (hc : c ∈ D) {E : Set G} (hE : IsMaxOrbit D c E)
    {e f : G} (he : e ∈ E) (hf : f ∈ E) (hef : ¬ Commute e f)
    (hrE : rootSet D e ⊆ E) (hsq : SqOut ↥(rootGen D e f))
    (hconn : ¬ Connectivity.Disconnected (((↑) : ↥(Subgroup.closure E) → G) ⁻¹' E)) :
    ¬ SqOut ↥(rootGen
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(Subgroup.closure E)) ''
        (((↑) : ↥(Subgroup.closure E) → G) ⁻¹' E))
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(Subgroup.closure E))
        ⟨e, Subgroup.subset_closure he⟩)
      (QuotientGroup.mk' (CFSG.pCore 2 ↥(Subgroup.closure E))
        ⟨f, Subgroup.subset_closure hf⟩)) := by
  classical
  let H : Subgroup G := Subgroup.closure E
  let Q : Subgroup H := CFSG.pCore 2 H
  let π : H →* H ⧸ Q := QuotientGroup.mk' Q
  let EH : Set H := ((↑) : H → G) ⁻¹' E
  let Ē : Set (H ⧸ Q) := π '' EH
  have heH : e ∈ H := Subgroup.subset_closure he
  have hfH : f ∈ H := Subgroup.subset_closure hf
  have heEH : (⟨e, heH⟩ : H) ∈ EH := he
  have hfEH : (⟨f, hfH⟩ : H) ∈ EH := hf
  have heD : e ∈ D := (subset_commSet h.setup.normal hE he).1
  have hclass : hClass H e = E := hClass_closure_eq h.setup hE he
  have hsetupH : Asc72.Setup H EH := by
    have hgen : H ≤ Subgroup.closure (hClass H e) := by rw [hclass]
    have h1 := setup_hClass h.setup.oddT h.setup.normal heH heD hgen
    simpa [EH, hclass] using h1
  have hmeetsH : OddTransp.MeetsSq EH := by
    obtain ⟨v, hv, hve, hev⟩ := exists_rootSet_triple h.setup h.sq heD
    have hvH : v ∈ H := Subgroup.subset_closure (hrE hv)
    refine ⟨⟨e, heH⟩, heEH, ⟨v, hvH⟩, hrE hv, ?_, ?_, ?_⟩
    · intro h'
      exact hve (congrArg Subtype.val h').symm
    · exact (commute_coe_iff (H := H)).mp
        (commute_of_mem_rootSet heD (mem_rootSet_self heD) hv)
    · change (e * v : G) ∈ E
      exact hrE hev
  have huniq : ∀ d ∈ EH, π d ≠ 1 := pCore_quotient_mk_ne_one h hE he hf hrE hsq
  have hsetupK : Asc72.Setup (H ⧸ Q) Ē := hsetupH.map π (QuotientGroup.mk'_surjective Q) huniq
  have hmeetsK : OddTransp.MeetsSq Ē := hmeetsH.map hsetupH.oddT π huniq
  have hconnK : ¬ Connectivity.Disconnected Ē := by
    intro hdisc
    obtain ⟨a, ha, b, hb, hab⟩ := hdisc
    obtain ⟨a', ha', rfl⟩ := ha
    obtain ⟨b', hb', rfl⟩ := hb
    have hreach : Reach EH a' b' := by
      by_contra h
      exact hconn ⟨a', ha', b', hb', h⟩
    exact hab (reach_map π hreach)
  have hHtop : H ≠ ⊤ := closure_ne_top_of_isMaxOrbit h hc hE
  have hHG : Nat.card H < Nat.card G := by
    refine lt_of_le_of_ne (Subgroup.card_le_card_group H) ?_
    intro heq
    exact hHtop ((Subgroup.card_eq_iff_eq_top H).1 heq)
  have hcardK : Nat.card (H ⧸ Q) < Nat.card G :=
    lt_of_le_of_lt (Nat.card_le_card_of_surjective π (QuotientGroup.mk'_surjective Q)) hHG
  have hO2K : CFSG.pCore 2 (H ⧸ Q) = ⊥ := CFSG.ABGLocalTools.pCore_quotient_pCore_eq_bot
  have hneπ : ¬ Commute (π ⟨e, heH⟩) (π ⟨f, hfH⟩) :=
    fun hc => hef ((commute_coe_iff (H := H)).mpr
      ((OddLocal.commute_iff_of_mem_pCore hsetupH.oddT
        (CFSG.pCore_isPGroup (p := 2) (G := H)) heEH hfEH).mp hc))
  have hHypK : Hyp (H ⧸ Q) Ē := ⟨hsetupK, hO2K, hmeetsK, hconnK⟩
  have hnoK : ¬ SqOut ↥(rootGen Ē (π ⟨e, heH⟩) (π ⟨f, hfH⟩)) :=
    IH (H ⧸ Q) Ē hcardK hHypK _ ⟨⟨e, heH⟩, heEH, rfl⟩ _
      ⟨⟨f, hfH⟩, hfEH, rfl⟩ hneπ
  exact hnoK

private theorem false_of_connected [Finite G] (IH : NoSzBelow (Nat.card G))
    (h : Hyp G D) {c : G} (hc : c ∈ D) {E : Set G} (hE : IsMaxOrbit D c E)
    {e f : G} (he : e ∈ E) (hf : f ∈ E) (hef : ¬ Commute e f)
    (hrE : rootSet D e ⊆ E) (hsq : SqOut ↥(rootGen D e f))
    (hconn : ¬ Connectivity.Disconnected (((↑) : ↥(Subgroup.closure E) → G) ⁻¹' E)) : False := by
  let H : Subgroup G := Subgroup.closure E
  let Q : Subgroup H := CFSG.pCore 2 H
  let π : H →* H ⧸ Q := QuotientGroup.mk' Q
  let EH : Set H := ((↑) : H → G) ⁻¹' E
  let Ē : Set (H ⧸ Q) := π '' EH
  have heH : e ∈ H := Subgroup.subset_closure he
  have hfH : f ∈ H := Subgroup.subset_closure hf
  have hnoK : ¬ SqOut ↥(rootGen Ē (π ⟨e, heH⟩) (π ⟨f, hfH⟩)) := by
    simpa [H, Q, π, EH, Ē] using
      not_sqOut_quotient_pCore IH h hc hE he hf hef hrE hsq hconn
  have hsqK : SqOut ↥(rootGen Ē (π ⟨e, heH⟩) (π ⟨f, hfH⟩)) := by
    simpa [H, Q, π, EH, Ē] using sqOut_map_rootGen_pCore h hE he hf hrE hsq
  exact hnoK hsqK

private theorem disconnected_of_sqOut [Finite G] (IH : NoSzBelow (Nat.card G))
    (h : Hyp G D) {c : G} (hc : c ∈ D) {E : Set G} (hE : IsMaxOrbit D c E)
    {e f : G} (he : e ∈ E) (hf : f ∈ E) (hef : ¬ Commute e f)
    (hrE : rootSet D e ⊆ E) (hsq : SqOut ↥(rootGen D e f)) :
    Connectivity.Disconnected (((↑) : ↥(Subgroup.closure E) → G) ⁻¹' E) := by
  by_contra hconn
  exact false_of_connected IH h hc hE he hf hef hrE hsq hconn


private theorem isBender_quotient_zStar [Finite G]
    (h : Hyp G D) {c e f : G} {E : Set G} (hE : IsMaxOrbit D c E) (he : e ∈ E)
    (hf : f ∈ E) (hrF : rootSet D f ⊆ E)
    (hdisc : Connectivity.Disconnected (((↑) : ↥(Subgroup.closure E) → G) ⁻¹' E)) :
    CFSG.BenderSuzuki.IsBenderGroup
      (↥(Subgroup.closure E) ⧸ zStar ↥(Subgroup.closure E)) := by
  let H : Subgroup G := Subgroup.closure E
  let y : G := e
  have hyH : y ∈ H := Subgroup.subset_closure he
  have heD : e ∈ D := (subset_commSet h.setup.normal hE he).1
  have hclass : hClass H y = E := hClass_closure_eq h.setup hE he
  have hgen : H ≤ Subgroup.closure (hClass H y) := by rw [hclass]
  have hconn : ¬ ∀ a ∈ hClass H y, ∀ b ∈ hClass H y, Reach (hClass H y) a b := by
    intro hall
    rw [hclass] at hall
    obtain ⟨a, ha, b, hb, hab⟩ := hdisc
    refine hab ((reach_preimage_iff (Subgroup.subset_closure)).mpr (hall a ha b hb))
  have hfD : f ∈ D := (subset_commSet h.setup.normal hE hf).1
  have hsq : ∃ u ∈ hClass H y, ∃ v ∈ hClass H y, u ≠ v ∧ Commute u v ∧ u * v ∈ hClass H y := by
    rw [hclass]
    obtain ⟨v, hv, hfv, hfve⟩ := exists_rootSet_triple h.setup h.sq hfD
    exact ⟨f, hf, v, hrF hv, hfv.symm,
      commute_of_mem_rootSet hfD (mem_rootSet_self hfD) hv, hrF hfve⟩
  exact isBender_of_not_conn h.setup.oddT h.setup.normal hyH heD hgen
    oddTranspZStar hconn hsq


private theorem not_sqOut_of_image_mem_sq {H : Subgroup G} {X : Subgroup G} (hXH : X ≤ H)
    {A : Subgroup (H ⧸ zStar H)}
    (hXA : ∀ x (hx : x ∈ X), QuotientGroup.mk' (zStar H) ⟨x, hXH hx⟩ ∈ A)
    (hA : ∀ a ∈ A, (∃ k : ℕ, a ^ 2 ^ k = 1) → a ^ 2 = 1) : ¬ SqOut X := by
  have hYA : (X.subgroupOf H).map (QuotientGroup.mk' (zStar H)) ≤ A := by
    rintro _ ⟨y, hy, rfl⟩
    simpa using hXA (y : G) (Subgroup.mem_subgroupOf.mp hy)
  have hnoY : ¬ SqOut (X.subgroupOf H) := not_sqOut_of_map_le hYA hA
  exact fun hx => hnoY ((sqOut_subgroupOf_iff hXH).mpr hx)

private theorem false_of_psl2 [Finite G]
    {E : Set G} {e f : G} (hf : f ∈ E) (hrE : rootSet D e ⊆ E)
    (hsq : SqOut ↥(rootGen D e f)) {n : ℕ} (hn : 2 ≤ n)
    (eK : (↥(Subgroup.closure E) ⧸ zStar ↥(Subgroup.closure E)) ≃* PSL2Model n) : False := by
  let H : Subgroup G := Subgroup.closure E
  let K : Type := ↥H ⧸ zStar ↥H
  let π : ↥H →* K := QuotientGroup.mk' (zStar ↥H)
  have hXH : rootGen D e f ≤ H := by
    rw [rootGen, Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact Subgroup.subset_closure hf
    · exact Subgroup.subset_closure (hrE hy)
  have hsqK : ∀ g : K, (∃ k : ℕ, g ^ 2 ^ k = 1) → g ^ 2 = 1 := by
    intro g hg
    obtain ⟨k, hk⟩ := hg
    have h2 : (eK g) ^ 2 = 1 :=
      CFSG.Timmesfeld.Bridge.sq_eq_one_of_psl2 (f := n) hn (n := k)
        (by rw [← map_pow, hk, map_one])
    apply eK.injective
    rw [map_pow, map_one]
    exact h2
  have hA : ∀ a ∈ (⊤ : Subgroup K), (∃ k : ℕ, a ^ 2 ^ k = 1) → a ^ 2 = 1 :=
    fun a _ ha => hsqK a ha
  have hXA : ∀ x (hx : x ∈ rootGen D e f), π ⟨x, hXH hx⟩ ∈ (⊤ : Subgroup K) :=
    fun _ _ => Subgroup.mem_top _
  exact not_sqOut_of_image_mem_sq hXH hXA hA hsq


private theorem mem_sylow_of_commute_involution {K : Type*} [Group K] [Finite K]
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) (Q : Sylow 2 K) {u v : K}
    (huQ : u ∈ (Q : Subgroup K)) (hu1 : u ≠ 1) (hu : u * u = 1) (hv : v * v = 1)
    (huv : Commute u v) : v ∈ (Q : Subgroup K) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hu2 : orderOf u = 2 := orderOf_eq_prime (by simpa [pow_two] using hu) hu1
  obtain ⟨q, k, hB, -⟩ := Asc72.IsBenderGroup.exists_fusionBenderBorel hK
  have hM := (hB Q).1
  have hvN : v ∈ Subgroup.normalizer ((Q : Subgroup K) : Set K) :=
    CFSG.Timmesfeld.Connectivity.mem_of_commute_of_stronglyEmbedded hM
      (Subgroup.le_normalizer huQ) hu2 huv.symm
  rcases eq_or_ne v 1 with rfl | hv1
  · exact Q.one_mem
  have hv2 : orderOf v = 2 := orderOf_eq_prime (by simpa [pow_two] using hv) hv1
  have hvp : IsPGroup 2 (Subgroup.zpowers v) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hv2, pow_one])
  have hsup : IsPGroup 2 ↥((Q : Subgroup K) ⊔ Subgroup.zpowers v) :=
    IsPGroup.to_sup_of_normal_left' (H := (Q : Subgroup K)) (K := Subgroup.zpowers v)
      Q.isPGroup' hvp (Subgroup.zpowers_le.mpr hvN)
  have heq := Q.is_maximal' hsup le_sup_left
  rw [← heq]
  exact Subgroup.mem_sup_right (Subgroup.mem_zpowers v)

private theorem mem_center_of_mem_sylow_involution {K : Type*} [Group K] [Finite K]
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) (Q : Sylow 2 K) {x : K}
    (hxQ : x ∈ (Q : Subgroup K)) (hx : x * x = 1) :
    (⟨x, hxQ⟩ : (Q : Subgroup K)) ∈ Subgroup.center (Q : Subgroup K) := by
  refine Subgroup.mem_center_iff.mpr fun y => Subtype.ext ?_
  exact ((Asc72.IsBenderGroup.commute_of_mul_self_eq_one hK Q hxQ hx) (y : K) y.2).eq.symm

private theorem sq_eq_one_of_mem_center_sylow {K : Type*} [Group K] [Finite K]
    (hK : CFSG.BenderSuzuki.IsBenderGroup K) (T : Sylow 2 K) :
    ∀ a ∈ (Subgroup.center (T : Subgroup K)).map (T : Subgroup K).subtype,
      (∃ k : ℕ, a ^ 2 ^ k = 1) → a ^ 2 = 1 := by
  intro a ha _
  obtain ⟨z, hz, rfl⟩ := Subgroup.mem_map.mp ha
  have hzT : (z : K) ∈ (T : Subgroup K) := z.2
  have hzc : ∀ y ∈ (T : Subgroup K), Commute (z : K) y := by
    intro y hy
    show (z : K) * y = y * (z : K)
    exact (congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hz (⟨y, hy⟩ : (T : Subgroup K)))).symm
  simpa [pow_two] using
    (Asc72.IsBenderGroup.mul_self_eq_one_of_commute hK T hzT hzc)



private theorem psu3_rootSet_image_mem_center [Finite G] (h : Hyp G D) {c : G} {E : Set G}
    (hE : IsMaxOrbit D c E) {e f : G} (he : e ∈ E) {K : Type*} [Group K] [Finite K]
    (π : ↥(Subgroup.closure E) →* K)
    (hXH : rootGen D e f ≤ Subgroup.closure E)
    (hB : CFSG.BenderSuzuki.IsBenderGroup K) (T : Sylow 2 K) {ebar : K}
    (hebarT : ebar ∈ (T : Subgroup K)) (hebar1 : ebar ≠ 1) (hebaresq : ebar * ebar = 1)
    (hebar_eq : ebar = π ⟨e, hXH (Subgroup.subset_closure
      (Set.mem_insert_of_mem f (mem_rootSet_self (subset_commSet h.setup.normal hE he).1)))⟩) :
    ∀ r (hr : r ∈ rootSet D e),
      π ⟨r, hXH (Subgroup.subset_closure (Set.mem_insert_of_mem f hr))⟩ ∈
        (Subgroup.center (T : Subgroup K)).map (T : Subgroup K).subtype := by
  let H : Subgroup G := Subgroup.closure E
  let EH : Set H := ((↑) : H → G) ⁻¹' E
  have heH : e ∈ H := Subgroup.subset_closure he
  have heD : e ∈ D := (subset_commSet h.setup.normal hE he).1
  have hclass : hClass H e = E := hClass_closure_eq h.setup hE he
  have hsetupH : Asc72.Setup H EH := by
    have hgen : H ≤ Subgroup.closure (hClass H e) := by rw [hclass]
    have h1 := setup_hClass h.setup.oddT h.setup.normal heH heD hgen
    simpa [EH, hclass] using h1
  have heEH : (⟨e, heH⟩ : H) ∈ EH := he
  intro r hr
  let rH : H := ⟨r, hXH (Subgroup.subset_closure (Set.mem_insert_of_mem f hr))⟩
  let rbar : K := π rH
  have hr_sq : rbar * rbar = 1 := by
    rw [← map_mul]
    have hh : rH * rH = 1 := Subtype.ext (h.setup.oddT.mul_self_eq_one hr.1)
    rw [hh, map_one]
  have hrcomm : Commute ebar rbar := by
    rw [hebar_eq]
    have hc : Commute e r := commute_of_mem_rootSet heD (mem_rootSet_self heD) hr
    exact ((commute_coe_iff (H := H)).mp hc).map π
  have hrT : rbar ∈ (T : Subgroup K) :=
    mem_sylow_of_commute_involution hB T hebarT hebar1 hebaresq hr_sq hrcomm
  have hrZ : (⟨rbar, hrT⟩ : (T : Subgroup K)) ∈ Subgroup.center (T : Subgroup K) :=
    mem_center_of_mem_sylow_involution hB T hrT hr_sq
  simpa [rbar, rH] using Subgroup.mem_map_of_mem (T : Subgroup K).subtype hrZ

section PSU3Certificates

private theorem false_of_psu3 [Finite G]
    (h : Hyp G D) {c : G} {E : Set G} (hE : IsMaxOrbit D c E)
    {e f : G} (he : e ∈ E) (hf : f ∈ E) (hrE : rootSet D e ⊆ E)
    (hsq : SqOut ↥(rootGen D e f)) {n : ℕ} (hn : 2 ≤ n)
    (eK : (↥(Subgroup.closure E) ⧸ zStar ↥(Subgroup.closure E)) ≃* PSU3Model n) : False := by
  let H : Subgroup G := Subgroup.closure E
  let K : Type := ↥H ⧸ zStar ↥H
  let π : ↥H →* K := QuotientGroup.mk' (zStar ↥H)
  have heD : e ∈ D := (subset_commSet h.setup.normal hE he).1
  have hfD : f ∈ D := (subset_commSet h.setup.normal hE hf).1
  have hXH : rootGen D e f ≤ H := by
    rw [rootGen, Subgroup.closure_le]
    rintro y (rfl | hy)
    · exact Subgroup.subset_closure hf
    · exact Subgroup.subset_closure (hrE hy)
  let eH : ↥H := ⟨e, hXH (Subgroup.subset_closure
    (Set.mem_insert_of_mem f (mem_rootSet_self heD)))⟩
  let fH : ↥H := ⟨f, hXH (Subgroup.subset_closure (Set.mem_insert f (rootSet D e)))⟩
  let ebar : K := π eH
  let fbar : K := π fH
  have hebarsq : ebar * ebar = 1 := by
    rw [← map_mul]
    have hh : eH * eH = 1 := Subtype.ext (h.setup.oddT.mul_self_eq_one heD)
    rw [hh, map_one]
  have hfbarsq : fbar * fbar = 1 := by
    rw [← map_mul]
    have hh : fH * fH = 1 := Subtype.ext (h.setup.oddT.mul_self_eq_one hfD)
    rw [hh, map_one]
  have hebar1 : ebar ≠ 1 := by
    intro h1
    have heZ : eH ∈ zStar ↥H := (QuotientGroup.eq_one_iff (N := zStar ↥H) eH).mp h1
    have h2pow : ∃ k : ℕ, eH ^ 2 ^ k = 1 :=
      ⟨1, by rw [pow_one]; simpa [pow_two] using
        (Subtype.ext (h.setup.oddT.mul_self_eq_one heD) : eH * eH = 1)⟩
    exact false_of_mem_pCore_of_mem_E h hE he hf hrE hsq he
      (mem_pCore_of_mem_zStar_of_two_pow heZ h2pow)
  have hebar2 : orderOf ebar = 2 := orderOf_eq_prime (by rwa [pow_two]) hebar1
  have hebarpow : IsPGroup 2 (Subgroup.zpowers ebar) :=
    IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hebar2, pow_one])
  obtain ⟨T, hT⟩ := hebarpow.exists_le_sylow
  have hebarT : ebar ∈ (T : Subgroup K) := hT (Subgroup.mem_zpowers ebar)
  have hB : CFSG.BenderSuzuki.IsBenderGroup K := IsBenderGroup.isPSU3 n hn eK
  have hr_center : ∀ r (hr : r ∈ rootSet D e),
      π ⟨r, hXH (Subgroup.subset_closure (Set.mem_insert_of_mem f hr))⟩ ∈
        (Subgroup.center (T : Subgroup K)).map (T : Subgroup K).subtype :=
    psu3_rootSet_image_mem_center h hE he π hXH hB T hebarT hebar1 hebarsq rfl
  have hmain : ∃ A : Subgroup K,
      (∀ x (hx : x ∈ insert f (rootSet D e)),
        π ⟨x, hXH (Subgroup.subset_closure hx)⟩ ∈ A) ∧
      (∀ a ∈ A, (∃ k : ℕ, a ^ 2 ^ k = 1) → a ^ 2 = 1) := by
    by_cases hfT : fbar ∈ (T : Subgroup K)
    · refine ⟨(Subgroup.center (T : Subgroup K)).map (T : Subgroup K).subtype, ?_,
        sq_eq_one_of_mem_center_sylow hB T⟩
      intro x hx
      rcases (Set.mem_insert_iff.mp hx) with rfl | hx
      · have hfZ : (⟨fbar, hfT⟩ : (T : Subgroup K)) ∈ Subgroup.center (T : Subgroup K) :=
          mem_center_of_mem_sylow_involution hB T hfT hfbarsq
        simpa [fbar, fH] using
          Subgroup.mem_map_of_mem (T : Subgroup K).subtype hfZ
      · simpa using hr_center x hx
    · let A : Subgroup K := Subgroup.closure (insert fbar
        ((Subgroup.center (T : Subgroup K)).map (T : Subgroup K).subtype : Set K))
      have hf1 : fbar ≠ 1 := fun h1 => hfT (h1 ▸ (T : Subgroup K).one_mem)
      have hf2 : orderOf fbar = 2 := orderOf_eq_prime (by rwa [pow_two]) hf1
      refine ⟨A, ?_, ?_⟩
      · intro x hx
        rcases (Set.mem_insert_iff.mp hx) with rfl | hx
        · exact Subgroup.subset_closure (Set.mem_insert _ _)
        · exact Subgroup.subset_closure (Set.mem_insert_of_mem _ (hr_center x hx))
      · intro a ha h2
        exact CFSG.BenderSuzuki.sq_eq_one_of_mem_closure_center_insert hn eK T hf2 hfT ha h2
  obtain ⟨A, hgen, hA⟩ := hmain
  have hXA : ∀ x (hx : x ∈ rootGen D e f),
      π ⟨x, hXH hx⟩ ∈ A :=
    map_rootGen_mem_of_generators hXH hgen
  exact not_sqOut_of_image_mem_sq hXH hXA hA hsq


end PSU3Certificates

private theorem sz_quotient [Finite G]
    (h : Hyp G D) {c : G} {E : Set G} (hE : IsMaxOrbit D c E)
    {e f : G} (he : e ∈ E) (hf : f ∈ E) (hrE : rootSet D e ⊆ E)
    (hrF : rootSet D f ⊆ E) (hsq : SqOut ↥(rootGen D e f))
    (hdisc : Connectivity.Disconnected (((↑) : ↥(Subgroup.closure E) → G) ⁻¹' E)) :
    ∃ n : ℕ, 1 ≤ n ∧
      Nonempty (↥(Subgroup.closure E) ⧸ zStar ↥(Subgroup.closure E) ≃* SzModel n) := by
  have hB : CFSG.BenderSuzuki.IsBenderGroup
      (↥(Subgroup.closure E) ⧸ zStar ↥(Subgroup.closure E)) :=
    isBender_quotient_zStar h hE he hf hrF hdisc
  rcases hB with ⟨n, hn, eK⟩ | ⟨n, hn, eK⟩ | ⟨n, hn, eK⟩
  · exact (false_of_psl2 hf hrE hsq hn eK).elim
  · exact ⟨n, hn, ⟨eK⟩⟩
  · exact (false_of_psu3 h hE he hf hrE hsq hn eK).elim

theorem szMain_config [Finite G]
    (IH : NoSzBelow (Nat.card G)) (h : Hyp G D)
    {c : G} (hc : c ∈ D) {E : Set G} (hE : IsMaxOrbit D c E) {e f : G} (he : e ∈ E)
    (hf : f ∈ E) (hef : ¬ Commute e f) (hrE : rootSet D e ⊆ E) (hrF : rootSet D f ⊆ E)
    (hsq : SqOut ↥(rootGen D e f)) :
    Connectivity.Disconnected (((↑) : ↥(Subgroup.closure E) → G) ⁻¹' E) ∧
    ∃ n : ℕ, 1 ≤ n ∧
      Nonempty (↥(Subgroup.closure E) ⧸ zStar ↥(Subgroup.closure E) ≃* SzModel n) := by
  have hdisc : Connectivity.Disconnected (((↑) : ↥(Subgroup.closure E) → G) ⁻¹' E) :=
    disconnected_of_sqOut IH h hc hE he hf hef hrE hsq
  exact ⟨hdisc, sz_quotient h hE he hf hrE hrF hsq hdisc⟩


end CFSG.Timmesfeld.Bridge.OddRoot
