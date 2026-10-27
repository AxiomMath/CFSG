module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Bot47HvA
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Bot47Plane
import CFSG.GroupTheory.ChiefSectionPGroup
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1Five
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Frat
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Half
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1G47Star

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s16c1_G47_conj_zpowers_fix {z h c : G} (hh : h ∈ centralizer ({z} : Set G))
    (hc : c ∈ Subgroup.zpowers z) : h * c * h⁻¹ = c := by
  obtain ⟨m, rfl⟩ := Subgroup.mem_zpowers_iff.1 hc
  have hzh : Commute z h := (Subgroup.mem_centralizer_iff.1 hh) z (Set.mem_singleton z)
  exact mul_inv_eq_iff_eq_mul.2 (hzh.zpow_left m).eq.symm

theorem s16c1_G47_conj_zpowers {z h : G} (hh : h ∈ centralizer ({z} : Set G)) :
    conjSubgroup (Subgroup.zpowers z) h = Subgroup.zpowers z := by
  ext y
  rw [mem_conjSubgroup_iff]
  constructor
  · intro hy
    have h1 := s16c1_G47_conj_zpowers_fix ((centralizer ({z} : Set G)).inv_mem hh) hy
    have h2 : y = h * y * h⁻¹ := by
      calc y = h⁻¹ * (h * y * h⁻¹) * h⁻¹⁻¹ := by group
        _ = h * y * h⁻¹ := h1
    rw [h2]
    exact hy
  · intro hy
    rwa [s16c1_G47_conj_zpowers_fix hh hy]

theorem s16c1_G47_irr_card (D : Data G) (hkit : OmegaKit) (h41 : R16_41 D)
    {V L : Subgroup G} {hV : IsElemAbelian 2 V} {x : IntMod V hV}
    (ctx : G47Ctx D ⊥ V L hV x) {N : Subgroup G} (hNV : N ≤ V)
    (hNst : ∀ g ∈ xInf L x.val, ∀ n ∈ N, g * n * g⁻¹ ∈ N) :
    Nat.card ↥N = 1 ∨ Nat.card ↥N = 2 ∨ Nat.card ↥N = 32 ∨ Nat.card ↥N = 64 := by
  classical
  have hS := ctx.sect
  have hc := ctx.caseOne
  have hz1 : mkTil (⊥ : Subgroup G) V hV x ≠ 1 := s16c1_mkTil_ne_one hS ctx.setup
  obtain ⟨Q, hQ, hQi⟩ := (h41 ⊥ V L hV hS hc).1
  have hQz : Q (mkTil (⊥ : Subgroup G) V hV x) = 0 := ctx.sing Q hQ hQi
  have h960 : Nat.card ↥(ptCent (lBar (⊥ : Subgroup G) V hV L)
      (mkTil (⊥ : Subgroup G) V hV x)) = 960 :=
    s16c1_card_of_isE16A5 (((h41 ⊥ V L hV hS hc).2 Q hQ hQi).1 _ hz1 hQz)
  have hbar := s16c1_barSub_xInf_eq_ptCent (s16c1_le_stabTil D hS) x ctx.e16 h960
  have hstab : StableUnder
      (ptCent (lBar (⊥ : Subgroup G) V hV L) (mkTil (⊥ : Subgroup G) V hV x))
      (imgTil (⊥ : Subgroup G) V hV N) := by
    intro φ hφ q hq
    rw [← hbar] at hφ
    obtain ⟨g, hg, rfl⟩ := (mem_barSub (⊥ : Subgroup G) V hV _ φ).1 hφ
    obtain ⟨y, hyN, rfl⟩ := (mem_imgTil (⊥ : Subgroup G) V hV _ q).1 hq
    rw [actTil_mk]
    refine (mem_imgTil (⊥ : Subgroup G) V hV _ _).2
      ⟨actStab (⊥ : Subgroup G) V hV g y, ?_, rfl⟩
    rw [actStab_apply_val]
    exact hNst (g : G) hg y.val hyN
  have hIrr := (hkit (Vtil (⊥ : Subgroup G) V hV) (lBar (⊥ : Subgroup G) V hV L)
    hc.2.1).2.1 _ hz1 h960 _ hstab
  rwa [s16c1_card_imgTil_bot hV hNV] at hIrr

theorem s16c1_G47_conj_comm_UQ {V : Subgroup G} {z g : G} (hgH : g ∈ centralizer ({z} : Set G))
    (hgV : g ∈ normalizer (V : Set G)) :
    conjSubgroup (⁅uOne V z, pCoreOf 2 (centralizer ({z} : Set G))⁆ ⊔ Subgroup.zpowers z) g =
      ⁅uOne V z, pCoreOf 2 (centralizer ({z} : Set G))⁆ ⊔ Subgroup.zpowers z := by
  have hconjU := s16c1_conjSubgroup_uOne_eq hgH hgV
  have hconjQ := s16c1_conjSubgroup_pCoreOf_self (centralizer ({z} : Set G)) hgH
  have hconjz := s16c1_G47_conj_zpowers hgH
  have hcomm : conjSubgroup ⁅uOne V z, pCoreOf 2 (centralizer ({z} : Set G))⁆ g =
      ⁅uOne V z, pCoreOf 2 (centralizer ({z} : Set G))⁆ := by
    rw [conjSubgroup, Subgroup.map_commutator]
    change ⁅conjSubgroup (uOne V z) g, conjSubgroup (pCoreOf 2 (centralizer ({z} : Set G))) g⁆ = _
    rw [hconjU, hconjQ]
  rw [conjSubgroup, Subgroup.map_sup]
  change conjSubgroup ⁅uOne V z, pCoreOf 2 (centralizer ({z} : Set G))⁆ g ⊔
    conjSubgroup (Subgroup.zpowers z) g = _
  rw [hcomm, hconjz]

theorem s16c1_G47_comm_UQ (D : Data G) (hkit : OmegaKit) (h41 : R16_41 D) {V L : Subgroup G}
    {hV : IsElemAbelian 2 V} {x : IntMod V hV} (ctx : G47Ctx D ⊥ V L hV x)
    (h47 : Concl1647 V x.val) :
    ⁅uOne V x.val, pCoreOf 2 (centralizer ({x.val} : Set G))⁆ ≤ Subgroup.zpowers x.val := by
  classical
  have hS := ctx.sect
  have hz : x.val ∈ V := x.val_mem
  have hz1 : x.val ≠ 1 := ctx.setup.ne_one
  have hV64 : Nat.card ↥V = 64 := s16c1_card_V_of_case D ctx.caseOne
  have hU32 : Nat.card ↥(uOne V x.val) = 32 := s16c1_card_uOne hV hz hV64 h47
  have hMV : D.M ≤ normalizer (V : Set G) := hS.setting.hyp151.hyp125.pairFacts.le_normalizer
  have hP : pCoreOf 2 (centralizer ({x.val} : Set G)) ≤ normalizer (V : Set G) :=
    (s16c1_pCoreOf_le_M D ctx.sylow).trans hMV
  haveI : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hQ2 : IsPGroup 2 (pCoreOf 2 (centralizer ({x.val} : Set G))) :=
    IsPGroup.map (CFSG.pCore_isPGroup (p := 2) (G := ↥(centralizer ({x.val} : Set G))))
      (centralizer ({x.val} : Set G)).subtype
  have hcardz : Nat.card ↥(Subgroup.zpowers x.val) = 2 := by
    rw [Nat.card_zpowers]
    exact orderOf_eq_prime (hV.2 x.val hz) hz1
  have hzU : Subgroup.zpowers x.val ≤ uOne V x.val := s16c1_zpowers_le_uOne hV hz
  have hne : Subgroup.zpowers x.val ≠ uOne V x.val := by
    intro h
    rw [h] at hcardz
    omega
  have hQz : pCoreOf 2 (centralizer ({x.val} : Set G)) ≤
      normalizer (Subgroup.zpowers x.val : Set G) := by
    intro q hq
    have hqH : q ∈ centralizer ({x.val} : Set G) := Subgroup.map_subtype_le _ hq
    exact (conjSubgroup_eq_iff_mem_normalizer (A := Subgroup.zpowers x.val) (g := q)).1
      (s16c1_G47_conj_zpowers hqH)
  have hlt := CFSG.GroupTheory.commutator_sup_lt_of_isPGroup (p := 2) (X := uOne V x.val)
    (Q := pCoreOf 2 (centralizer ({x.val} : Set G))) (V := Subgroup.zpowers x.val)
    inf_le_right hQ2 (s16c1_pCoreOf_le_normalizer_uOne hP) hQz hzU hne
  set N₁ : Subgroup G :=
    ⁅uOne V x.val, pCoreOf 2 (centralizer ({x.val} : Set G))⁆ ⊔ Subgroup.zpowers x.val with hN₁
  have hN1U : N₁ ≤ uOne V x.val := hlt.le
  have hstab : ∀ g ∈ xInf L x.val, ∀ n ∈ N₁, g * n * g⁻¹ ∈ N₁ := by
    intro g hg n hn
    have hgHL := Subgroup.mem_inf.1 (s16c1_G47_xInf_le L x.val hg)
    have hgM : g ∈ normalizer (V : Set G) := hMV (hS.setting.hyp151.le hgHL.2)
    have h := s16c1_G47_conj_comm_UQ (V := V) hgHL.1 hgM
    have hn' : n ∈ conjSubgroup N₁ g := by
      rw [hN₁, h]
      exact hn
    exact mem_conjSubgroup_iff.1 hn'
  have hIrr := s16c1_G47_irr_card D hkit h41 ctx (hN1U.trans inf_le_left) hstab
  have hNge : 2 ≤ Nat.card ↥N₁ := by
    have h := Subgroup.card_le_of_le (le_sup_right : Subgroup.zpowers x.val ≤ N₁)
    rwa [hcardz] at h
  have hNle : Nat.card ↥N₁ ≤ 32 := by
    have h := Subgroup.card_le_of_le hN1U
    rwa [hU32] at h
  have hcard2 : Nat.card ↥N₁ = 2 := by
    rcases hIrr with h | h | h | h
    · omega
    · exact h
    · exact absurd (Subgroup.eq_of_le_of_card_ge hN1U (by rw [h, hU32])) hlt.ne
    · omega
  have hEq : Subgroup.zpowers x.val = N₁ :=
    Subgroup.eq_of_le_of_card_ge le_sup_right (by rw [hcardz, hcard2])
  exact le_sup_left.trans hEq.ge

theorem s16c1_G47_comm_EQ {V : Subgroup G} {z : G}
    (hUQ : ⁅uOne V z, pCoreOf 2 (centralizer ({z} : Set G))⁆ ≤ Subgroup.zpowers z) :
    ∀ r ∈ pCoreOf 2 (centralizer ({z} : Set G)), ∀ e ∈ eOne V z,
      r * e * r⁻¹ * e⁻¹ ∈ Subgroup.zpowers z := by
  classical
  let K : Subgroup G :=
    { carrier := {e | e ∈ centralizer ({z} : Set G) ∧
        ∀ r ∈ pCoreOf 2 (centralizer ({z} : Set G)), r * e * r⁻¹ * e⁻¹ ∈ Subgroup.zpowers z}
      mul_mem' := by
        rintro a b ⟨haH, ha⟩ ⟨hbH, hb⟩
        refine ⟨(centralizer ({z} : Set G)).mul_mem haH hbH, fun r hr => ?_⟩
        have e1 : r * (a * b) * r⁻¹ * (a * b)⁻¹ =
            (r * a * r⁻¹ * a⁻¹) * (a * (r * b * r⁻¹ * b⁻¹) * a⁻¹) := by group
        rw [e1, s16c1_G47_conj_zpowers_fix haH (hb r hr)]
        exact (Subgroup.zpowers z).mul_mem (ha r hr) (hb r hr)
      one_mem' := ⟨(centralizer ({z} : Set G)).one_mem, fun r _ => by simp⟩
      inv_mem' := by
        rintro a ⟨haH, ha⟩
        refine ⟨(centralizer ({z} : Set G)).inv_mem haH, fun r hr => ?_⟩
        have e1 : r * a⁻¹ * r⁻¹ * (a⁻¹)⁻¹ = a⁻¹ * (r * a * r⁻¹ * a⁻¹)⁻¹ * (a⁻¹)⁻¹ := by group
        rw [e1, s16c1_G47_conj_zpowers_fix ((centralizer ({z} : Set G)).inv_mem haH)
          ((Subgroup.zpowers z).inv_mem (ha r hr))]
        exact (Subgroup.zpowers z).inv_mem (ha r hr) }
  have hEK : eOne V z ≤ K := by
    rw [eOne, hConjClosure]
    refine iSup_le fun h => ?_
    intro y hy
    have hyE : y ∈ eOne V z :=
      le_iSup (fun h : ↥(centralizer ({z} : Set G)) => conjSubgroup (uOne V z) (h : G)) h hy
    have hyQ : y ∈ pCoreOf 2 (centralizer ({z} : Set G)) := s16c1_eOne_le_pCoreOf V z hyE
    have hyH : y ∈ centralizer ({z} : Set G) := Subgroup.map_subtype_le _ hyQ
    refine ⟨hyH, fun r hr => ?_⟩
    have hu : (h : G) * y * (h : G)⁻¹ ∈ uOne V z := mem_conjSubgroup_iff.1 hy
    have hq : (h : G) * r * (h : G)⁻¹ ∈ pCoreOf 2 (centralizer ({z} : Set G)) :=
      s16c1_G47_conj_mem_pCoreOf h.2 hr
    have hc : ⁅(h : G) * y * (h : G)⁻¹, (h : G) * r * (h : G)⁻¹⁆ ∈ Subgroup.zpowers z :=
      hUQ (Subgroup.commutator_mem_commutator hu hq)
    have e1 : r * y * r⁻¹ * y⁻¹ =
        (h : G)⁻¹ * ⁅(h : G) * y * (h : G)⁻¹, (h : G) * r * (h : G)⁻¹⁆⁻¹ * ((h : G)⁻¹)⁻¹ := by
      simp only [commutatorElement_def]
      group
    rw [e1, s16c1_G47_conj_zpowers_fix ((centralizer ({z} : Set G)).inv_mem h.2)
      ((Subgroup.zpowers z).inv_mem hc)]
    exact (Subgroup.zpowers z).inv_mem hc
  intro r hr e he
  exact (hEK he).2 r hr

theorem s16c1_G47_d_mem {V : Subgroup G} {z : G} (hV : IsElemAbelian 2 V) (hz : z ∈ V)
    (hP : pCoreOf 2 (centralizer ({z} : Set G)) ≤ normalizer (V : Set G)) {w e : G} (hw : w ∈ V)
    (he : e ∈ eOne V z) (hsq : e ^ 2 ∈ Subgroup.zpowers z) : w * e * w⁻¹ * e ∈ uOne V z := by
  have h1 : ⁅w, e⁆ ∈ uOne V z :=
    s16c1_comm_V_eOne_le hV hz hP (Subgroup.commutator_mem_commutator hw he)
  have h2 : e ^ 2 ∈ uOne V z := s16c1_zpowers_le_uOne hV hz hsq
  have e1 : w * e * w⁻¹ * e = ⁅w, e⁆ * e ^ 2 := by
    simp only [commutatorElement_def]
    group
  rw [e1]
  exact (uOne V z).mul_mem h1 h2

theorem s16c1_G47_comm_V_of_w {V : Subgroup G} {z : G}
    (hEE : ⁅eOne V z, eOne V z⁆ ≤ Subgroup.zpowers z) {w : G}
    (hwH : w ∈ centralizer ({z} : Set G)) (hVw : ∀ v ∈ V, v ∈ uOne V z ∨ w⁻¹ * v ∈ uOne V z)
    (hall : ∀ e ∈ eOne V z, ⁅w, e⁆ ∈ Subgroup.zpowers z) :
    ⁅V, eOne V z⁆ ≤ Subgroup.zpowers z := by
  rw [Subgroup.commutator_le]
  intro v hv e he
  rcases hVw v hv with hvU | hwv
  · exact hEE (Subgroup.commutator_mem_commutator (s16c1_uOne_le_eOne V z hvU) he)
  · have ha : ⁅w⁻¹ * v, e⁆ ∈ Subgroup.zpowers z :=
      hEE (Subgroup.commutator_mem_commutator (s16c1_uOne_le_eOne V z hwv) he)
    have e1 : ⁅v, e⁆ = w * ⁅w⁻¹ * v, e⁆ * w⁻¹ * ⁅w, e⁆ := by
      simp only [commutatorElement_def]
      group
    rw [e1, s16c1_G47_conj_zpowers_fix hwH ha]
    exact (Subgroup.zpowers z).mul_mem ha (hall e he)

theorem s16c1_G47_cent_le_B {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    {x : IntMod V hV} (hsp : IsStronglyPEmbedded 3 D.M) (hL : L ∈ calC D.M)
    (ctx : G47Ctx D V₀ V L hV x)
    (hX : IsSL2Prime ↥(starImg (centralizer ({x.val} : Set G)) (xInf L x.val)) 5) :
    ∀ c : Bar2 (centralizer ({x.val} : Set G)),
      (∀ y ∈ starImg (centralizer ({x.val} : Set G)) (xInf L x.val), c * y = y * c) →
        c ∈ starImg (centralizer ({x.val} : Set G)) (centralizer ({x.val} : Set G) ⊓ D.M) := by
  have hXHL := s16c1_G47_xInf_le L x.val
  have hXH : xInf L x.val ≤ centralizer ({x.val} : Set G) := hXHL.trans inf_le_left
  have hXM : xInf L x.val ≤ D.M := (hXHL.trans inf_le_right).trans hL.1.le
  have hQM : pCoreOf 2 (centralizer ({x.val} : Set G)) ≤ D.M := s16c1_pCoreOf_le_M D ctx.sylow
  have h120 : Nat.card ↥(starImg (centralizer ({x.val} : Set G)) (xInf L x.val)) = 120 :=
    (s16c1_sl2five_facts hX).1
  have h3X : 3 ∣ Nat.card ↥(xInf L x.val) := by
    have h := s16c1_G47_card_starImg_mul hXH
    rw [h120] at h
    rw [← h]
    exact Dvd.dvd.mul_right (by norm_num) _
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨d, hd⟩ := exists_prime_orderOf_dvd_card' (G := ↥(xInf L x.val)) 3 h3X
  have hd3 : orderOf (d : G) = 3 := by rw [Subgroup.orderOf_coe]; exact hd
  intro c hc
  have hdbar : QuotientGroup.mk' (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G)))
      ⟨(d : G), hXH d.2⟩ ∈ starImg (centralizer ({x.val} : Set G)) (xInf L x.val) :=
    Subgroup.mem_map.2 ⟨⟨(d : G), hXH d.2⟩, Subgroup.mem_subgroupOf.2 d.2, rfl⟩
  have hcent : c ∈ Subgroup.centralizer
      ((Subgroup.zpowers (QuotientGroup.mk' (CFSG.pCore 2 ↥(centralizer ({x.val} : Set G)))
        ⟨(d : G), hXH d.2⟩) : Subgroup (Bar2 (centralizer ({x.val} : Set G)))) :
        Set (Bar2 (centralizer ({x.val} : Set G)))) := by
    rw [Subgroup.mem_centralizer_iff]
    intro h hh
    obtain ⟨k, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    exact ((show Commute c _ from hc _ hdbar).zpow_right k).eq.symm
  exact s16c1_G47_star_normalizer_le hQM hsp hXH hXM d.2 hd3
    (Subgroup.centralizer_le_normalizer _ hcent)

theorem s16c1_G47_mem_of_mk_mem {Γ : Type} [Group Γ] {E U Z : Subgroup Γ} (hUE : U ≤ E)
    (hZU : Z ≤ U) [(Z.subgroupOf E).Normal] {e : ↥E}
    (he : (QuotientGroup.mk e : ↥E ⧸ Z.subgroupOf E) ∈
      (U.subgroupOf E).map (QuotientGroup.mk' (Z.subgroupOf E))) : (e : Γ) ∈ U := by
  obtain ⟨a, ha, hae⟩ := Subgroup.mem_map.1 he
  have hae' : (QuotientGroup.mk a : ↥E ⧸ Z.subgroupOf E) = QuotientGroup.mk e := hae
  have h1 : a⁻¹ * e ∈ Z.subgroupOf E := QuotientGroup.eq.1 hae'
  have h2 : ((a⁻¹ * e : ↥E) : Γ) ∈ Z := Subgroup.mem_subgroupOf.1 h1
  have h3 : (a : Γ) ∈ U := Subgroup.mem_subgroupOf.1 ha
  have h4 : (e : Γ) = (a : Γ) * ((a⁻¹ * e : ↥E) : Γ) := by simp
  rw [h4]
  exact U.mul_mem h3 (hZU h2)

theorem s16c1_G47_card_image {Γ : Type} [Group Γ] [Finite Γ] {E U Z : Subgroup Γ} (hUE : U ≤ E)
    (hZU : Z ≤ U) [(Z.subgroupOf E).Normal] :
    Nat.card ↥((U.subgroupOf E).map (QuotientGroup.mk' (Z.subgroupOf E))) * Nat.card ↥Z =
      Nat.card ↥U := by
  classical
  have hZE : Z ≤ E := hZU.trans hUE
  have hpre : (QuotientGroup.mk ⁻¹' (((U.subgroupOf E).map
      (QuotientGroup.mk' (Z.subgroupOf E)) : Subgroup (↥E ⧸ Z.subgroupOf E)) :
        Set (↥E ⧸ Z.subgroupOf E)) : Set ↥E) = ((U.subgroupOf E : Subgroup ↥E) : Set ↥E) := by
    ext e
    constructor
    · intro he
      exact Subgroup.mem_subgroupOf.2 (s16c1_G47_mem_of_mk_mem hUE hZU he)
    · intro he
      exact ⟨e, he, rfl⟩
  have h := QuotientGroup.card_preimage_mk (Z.subgroupOf E) (((U.subgroupOf E).map
    (QuotientGroup.mk' (Z.subgroupOf E)) : Subgroup (↥E ⧸ Z.subgroupOf E)) :
      Set (↥E ⧸ Z.subgroupOf E))
  rw [hpre] at h
  have hA : Nat.card ↥(U.subgroupOf E) = Nat.card ↥U :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hUE).toEquiv
  have hK : Nat.card ↥(Z.subgroupOf E) = Nat.card ↥Z :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hZE).toEquiv
  rw [← hA, ← hK, mul_comm]
  exact h.symm

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
