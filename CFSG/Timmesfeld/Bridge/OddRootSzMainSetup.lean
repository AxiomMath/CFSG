module

public import CFSG.Timmesfeld.Bridge.OddRootDefs
import CFSG.Timmesfeld.Bridge.OddRootBasic
import CFSG.Timmesfeld.Bridge.OddRootOrbit
import CFSG.Timmesfeld.Bridge.RootClosureThree
import CFSG.LocalAnalysis.AGLEmbedding.TwoCoreObstruction
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp CFSG.Timmesfeld.Bridge.OddLocal
  CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki

variable {G : Type} [Group G] [Finite G] {D : Set G} {d e : G} {E : Set G} {n : ℕ}

structure SzCfg (G : Type) [Group G] (D : Set G) (d : G) (E : Set G) (e : G) (n : ℕ) :
    Prop where
  hyp : Hyp G D
  d_mem : d ∈ D
  maxOrbit : IsMaxOrbit D d E
  e_mem : e ∈ E
  rootSet_subset : rootSet D e ⊆ E
  one_le : 1 ≤ n
  iso : Nonempty (↥(Subgroup.closure E) ⧸ zStar ↥(Subgroup.closure E) ≃* SzModel n)

@[expose] def szQ (E : Set G) : Subgroup G := CFSG.Open.pCoreOf 2 (Subgroup.closure E)

@[expose] def szZ (E : Set G) : Subgroup G := szQ E ⊓ Subgroup.centralizer E

@[expose] def szComp (E : Set G) (a : G) : Set G := {u | u ∈ E ∧ Commute u a}

@[expose] def szE (E : Set G) : Set ↥(Subgroup.closure E) :=
  ((↑) : ↥(Subgroup.closure E) → G) ⁻¹' E

abbrev SzBar (E : Set G) : Type :=
  ↥(Subgroup.closure E) ⧸ CFSG.pCore 2 ↥(Subgroup.closure E)

@[expose] def szMk (E : Set G) : ↥(Subgroup.closure E) →* SzBar E :=
  QuotientGroup.mk' (CFSG.pCore 2 ↥(Subgroup.closure E))

theorem SzCfg.subset_commSet (c : SzCfg G D d E e n) : E ⊆ commSet D d :=
  OddLocal.subset_commSet c.hyp.setup.normal c.maxOrbit

theorem SzCfg.d_not_mem (c : SzCfg G D d E e n) : d ∉ E := fun hd =>
  (c.subset_commSet hd).2.2 rfl

theorem SzCfg.conj_mem (c : SzCfg G D d E e n) {h a : G} (hh : h ∈ Subgroup.closure E)
    (ha : a ∈ E) : h * a * h⁻¹ ∈ E := by
  have himage : (fun y => h * y * h⁻¹) '' E = E :=
    Subgroup.mem_normalizer_iff_conj_image_eq.mp
      (closure_le_normalizer_of_isMaxOrbit c.hyp.setup c.maxOrbit hh)
  rw [← himage]
  exact ⟨a, ha, rfl⟩

theorem SzCfg.exists_conj (c : SzCfg G D d E e n) {a b : G} (ha : a ∈ E) (hb : b ∈ E) :
    ∃ h ∈ Subgroup.closure E, h * a * h⁻¹ = b := by
  obtain ⟨h, hh, hb'⟩ := OddLocal.orbitGen c.hyp.setup c.maxOrbit ha b hb
  exact ⟨h, hh, hb'.symm⟩

theorem SzCfg.exists_not_commute (c : SzCfg G D d E e n) {a : G} (ha : a ∈ E) :
    ∃ x ∈ E, ¬ Commute x a := by
  have hconn : ∀ u ∈ D, ∀ v ∈ D, Reach D u v := by
    intro u hu v hv
    by_contra h
    exact c.hyp.conn ⟨u, hu, v, hv, h⟩
  obtain ⟨x, hx, hxa⟩ :=
    OddLocal.exists_not_commute c.hyp.setup c.d_mem c.maxOrbit hconn ha
  exact ⟨x, hx, fun h => hxa h.symm⟩

theorem SzCfg.rootSet_subset_of_mem (c : SzCfg G D d E e n) {a : G} (ha : a ∈ E) :
    rootSet D a ⊆ E := by
  obtain ⟨e₀, he₀, hEeq, -⟩ := c.maxOrbit
  have ha₀ : a ∈ orbitIn D d e₀ := hEeq ▸ ha
  have he₀' : e ∈ orbitIn D d e₀ := hEeq ▸ c.e_mem
  obtain ⟨g, hg, hga⟩ := ha₀
  obtain ⟨k, hk, hke⟩ := he₀'
  have hmem : g * k⁻¹ ∈ Subgroup.closure (commSet D d) :=
    Subgroup.mul_mem _ hg (Subgroup.inv_mem _ hk)
  have hae : a = (g * k⁻¹) * e * (g * k⁻¹)⁻¹ := by
    rw [hga, hke]
    group
  have himage : (fun y => (g * k⁻¹) * y * (g * k⁻¹)⁻¹) '' E = E :=
    Subgroup.mem_normalizer_iff_conj_image_eq.mp
      (OddLocal.closure_commSet_le_normalizer c.maxOrbit hmem)
  rw [hae, Timmesfeld.rootSet_conj c.hyp.setup.isClass (g * k⁻¹) e]
  intro x hx
  obtain ⟨y, hy, rfl⟩ := hx
  exact himage ▸ ⟨y, c.rootSet_subset hy, rfl⟩

theorem SzCfg.setup (c : SzCfg G D d E e n) :
    Asc72.Setup ↥(Subgroup.closure E) (szE E) := by
  let H : Subgroup G := Subgroup.closure E
  have heH : e ∈ H := Subgroup.subset_closure c.e_mem
  have heD : e ∈ D := (c.subset_commSet c.e_mem).1
  have hclass : OddLocal.hClass H e = E := hClass_closure_eq c.hyp.setup c.maxOrbit c.e_mem
  have hgen : H ≤ Subgroup.closure (OddLocal.hClass H e) := by rw [hclass]
  have h1 := OddLocal.setup_hClass c.hyp.setup.oddT c.hyp.setup.normal heH heD hgen
  simpa [szE, hclass] using h1

theorem SzCfg.perfect (c : SzCfg G D d E e n) :
    commutator ↥(Subgroup.closure E) = ⊤ := by
  let H : Subgroup G := Subgroup.closure E
  have heD : e ∈ D := (c.subset_commSet c.e_mem).1
  obtain ⟨v, hv, -, hev⟩ := exists_rootSet_triple c.hyp.setup c.hyp.sq heD
  have hvE : v ∈ E := c.rootSet_subset_of_mem c.e_mem hv
  have hevE : e * v ∈ E := c.rootSet_subset_of_mem c.e_mem hev
  have hsetup : Asc72.Setup H (szE E) := c.setup
  have heH : (⟨e, Subgroup.subset_closure c.e_mem⟩ : H) ∈ szE E := c.e_mem
  have hvH : (⟨v, Subgroup.subset_closure hvE⟩ : H) ∈ szE E := hvE
  have hevH : (⟨e, Subgroup.subset_closure c.e_mem⟩ : H) *
      (⟨v, Subgroup.subset_closure hvE⟩ : H) ∈ szE E := by
    simpa [szE] using hevE
  exact OddLocal.commutator_eq_top_of_mul_mem hsetup heH hvH hevH

theorem mem_szQ_iff {x : G} : x ∈ szQ E ↔ ∃ h : x ∈ Subgroup.closure E,
    (⟨x, h⟩ : ↥(Subgroup.closure E)) ∈ CFSG.pCore 2 ↥(Subgroup.closure E) := by
  rw [szQ, CFSG.Open.pCoreOf, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    have hx : x ∈ Subgroup.closure E := hyx ▸ y.2
    refine ⟨hx, ?_⟩
    have hy' : (⟨x, hx⟩ : ↥(Subgroup.closure E)) = y := Subtype.ext hyx.symm
    rwa [hy']
  · rintro ⟨hx, hxQ⟩
    exact ⟨⟨x, hx⟩, hxQ, rfl⟩

theorem szQ_le_closure (E : Set G) : szQ E ≤ Subgroup.closure E :=
  CFSG.openPCoreOf_le 2 _

private theorem isPGroup_zpowers_sup_pCore {H : Subgroup G} {x : G} (hx : x ∈ H)
    (hx2 : x * x = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers (⟨x, hx⟩ : H) ⊔ CFSG.pCore 2 H) := by
  have hxH2 : (⟨x, hx⟩ : H) * ⟨x, hx⟩ = 1 := Subtype.ext hx2
  have h1 : IsPGroup 2 (Subgroup.zpowers (⟨x, hx⟩ : H)) :=
    RootClosure.isPGroup_zpowers_of_mul_self_eq_one hxH2
  have hnorm : Subgroup.zpowers (⟨x, hx⟩ : H) ≤
      Subgroup.normalizer ((CFSG.pCore 2 H : Subgroup H) : Set H) := by
    rw [Subgroup.normalizer_eq_top_iff.mpr (CFSG.pCore_normal (G := H))]
    exact le_top
  exact IsPGroup.to_sup_of_normal_right' h1 (CFSG.pCore_isPGroup (p := 2) (G := H)) hnorm

theorem conj_mem_szQ {g x : G}
    (hg : (fun y => g * y * g⁻¹) '' E = E) (hx : x ∈ szQ E) :
    g * x * g⁻¹ ∈ szQ E := by
  let H : Subgroup G := Subgroup.closure E
  have hHmap : H.map (MulAut.conj g).toMonoidHom = H := by
    change (Subgroup.closure E).map (MulAut.conj g).toMonoidHom = Subgroup.closure E
    rw [MonoidHom.map_closure]
    have himg : (MulAut.conj g).toMonoidHom '' E = E := by
      rw [show ((MulAut.conj g).toMonoidHom : G → G) = fun y => g * y * g⁻¹ from
        funext fun y => by simp [MulAut.conj_apply]]
      exact hg
    rw [himg]
  let φ : H ≃* H :=
    (Subgroup.equivMapOfInjective H (MulAut.conj g).toMonoidHom
      (MulAut.conj g).injective).trans (MulEquiv.subgroupCongr hHmap)
  have hφ : ∀ y : H, ((φ y : H) : G) = g * (y : G) * g⁻¹ := fun _ => rfl
  have hp : (CFSG.pCore 2 H).map φ.toMonoidHom = CFSG.pCore 2 H :=
    CFSG.pCore_map_iso 2 φ
  rw [mem_szQ_iff] at hx ⊢
  obtain ⟨hxH, hxQ⟩ := hx
  have hφQ : φ ⟨x, hxH⟩ ∈ CFSG.pCore 2 H :=
    hp ▸ Subgroup.mem_map_of_mem φ.toMonoidHom hxQ
  refine ⟨?_, ?_⟩
  · rw [← hφ ⟨x, hxH⟩]
    exact (φ ⟨x, hxH⟩).2
  · convert hφQ using 2
    exact (hφ ⟨x, hxH⟩).symm

theorem SzCfg.conj_mem_szZ (c : SzCfg G D d E e n) {h z : G}
    (hh : h ∈ Subgroup.closure E) (hz : z ∈ szZ E) : h * z * h⁻¹ ∈ szZ E := by
  have hnorm : h ∈ Subgroup.normalizer E :=
    closure_le_normalizer_of_isMaxOrbit c.hyp.setup c.maxOrbit hh
  have himage : (fun y => h * y * h⁻¹) '' E = E :=
    Subgroup.mem_normalizer_iff_conj_image_eq.mp hnorm
  have himage'' : (fun y => h⁻¹ * y * h⁻¹⁻¹) '' E = E :=
    Subgroup.mem_normalizer_iff_conj_image_eq.mp (Subgroup.inv_mem (Subgroup.normalizer E) hnorm)
  have himage' : (fun y => h⁻¹ * y * h) '' E = E := by
    simpa only [inv_inv] using himage''
  refine ⟨conj_mem_szQ himage hz.1, ?_⟩
  refine Subgroup.mem_centralizer_iff.mpr ?_
  intro a ha
  have hbE : h⁻¹ * a * h ∈ E := himage' ▸ ⟨a, ha, rfl⟩
  have hzeq := (Subgroup.mem_centralizer_iff.mp hz.2 (h⁻¹ * a * h) hbE).symm
  have hb : h * (h⁻¹ * a * h) * h⁻¹ = a := by group
  have hw : (h * z * h⁻¹) * a = a * (h * z * h⁻¹) := by
    calc
      (h * z * h⁻¹) * a = (h * z * h⁻¹) * (h * (h⁻¹ * a * h) * h⁻¹) := by rw [hb]
      _ = h * (z * (h⁻¹ * a * h)) * h⁻¹ := by group
      _ = h * ((h⁻¹ * a * h) * z) * h⁻¹ := by rw [hzeq]
      _ = (h * (h⁻¹ * a * h) * h⁻¹) * (h * z * h⁻¹) := by group
      _ = a * (h * z * h⁻¹) := by rw [hb]
  exact hw.symm

theorem SzCfg.not_mem_szQ (c : SzCfg G D d E e n) {a : G} (ha : a ∈ E) : a ∉ szQ E := by
  intro hz
  let H : Subgroup G := Subgroup.closure E
  have haH : a ∈ H := Subgroup.subset_closure ha
  have haQ : (⟨a, haH⟩ : H) ∈ CFSG.pCore 2 H :=
    (mem_szQ_iff.mp hz).2
  obtain ⟨x, hx, hxa⟩ := c.exists_not_commute ha
  have hxH : x ∈ H := Subgroup.subset_closure hx
  have hxD : x ∈ D := (c.subset_commSet hx).1
  have haD : a ∈ D := (c.subset_commSet ha).1
  have hsup : IsPGroup 2 ↥(Subgroup.zpowers (⟨x, hxH⟩ : H) ⊔ CFSG.pCore 2 H) :=
    isPGroup_zpowers_sup_pCore hxH (c.hyp.setup.oddT.mul_self_eq_one hxD)
  have hDH : IsOddTransp (((↑) : H → G) ⁻¹' D) := c.hyp.setup.oddT.preimage H
  have hcomm : Commute (⟨x, hxH⟩ : H) (⟨a, haH⟩ : H) :=
    hDH.commute_of_isPGroup hsup hxD haD
      (Subgroup.mem_sup_left (Subgroup.mem_zpowers _)) (Subgroup.mem_sup_right haQ)
  exact hxa ((commute_coe_iff (H := H)).mpr hcomm)

theorem isPGroup_zpowers_sup_szQ {x : G}
    (hx : x ∈ Subgroup.closure E) (hx2 : x * x = 1) :
    IsPGroup 2 ↥(Subgroup.zpowers x ⊔ szQ E) := by
  let H : Subgroup G := Subgroup.closure E
  have h := isPGroup_zpowers_sup_pCore (H := H) hx hx2
  have hmap : (Subgroup.zpowers (⟨x, hx⟩ : H) ⊔ CFSG.pCore 2 H).map H.subtype =
      Subgroup.zpowers x ⊔ szQ E := by
    change Subgroup.map (Subgroup.closure E).subtype
      (Subgroup.zpowers (⟨x, hx⟩ : H) ⊔ CFSG.pCore 2 H) =
        Subgroup.zpowers x ⊔ Subgroup.map (Subgroup.closure E).subtype
          (CFSG.pCore 2 (Subgroup.closure E))
    rw [Subgroup.map_sup, MonoidHom.map_zpowers]
    rfl
  have h' := h.map H.subtype
  rwa [hmap] at h'

theorem SzCfg.commute_of_inv_mul_mem (c : SzCfg G D d E e n) {u v : G} (hu : u ∈ D)
    (hv : v ∈ D) (huH : u ∈ Subgroup.closure E) (huv : u⁻¹ * v ∈ szQ E) :
    Commute u v := by
  let H : Subgroup G := Subgroup.closure E
  have hqH : u⁻¹ * v ∈ H := szQ_le_closure E huv
  have hvH : v ∈ H := by
    have h : u * (u⁻¹ * v) = v := by group
    rw [← h]
    exact H.mul_mem huH hqH
  let uH : H := ⟨u, huH⟩
  let vH : H := ⟨v, hvH⟩
  have hq : (⟨u⁻¹ * v, hqH⟩ : H) ∈ CFSG.pCore 2 H :=
    (mem_szQ_iff.mp huv).2
  have hb : vH = uH * ⟨u⁻¹ * v, hqH⟩ := by
    apply Subtype.ext
    simp [uH, vH]
  have hq1 : QuotientGroup.mk' (CFSG.pCore 2 H) ⟨u⁻¹ * v, hqH⟩ = 1 :=
    (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 H) ⟨u⁻¹ * v, hqH⟩).mpr hq
  have hmk : QuotientGroup.mk' (CFSG.pCore 2 H) vH =
      QuotientGroup.mk' (CFSG.pCore 2 H) uH := by
    rw [hb, map_mul, hq1, mul_one]
  have hquot : Commute (QuotientGroup.mk' (CFSG.pCore 2 H) uH)
      (QuotientGroup.mk' (CFSG.pCore 2 H) vH) := by
    rw [hmk]
  have hDH : IsOddTransp (((↑) : H → G) ⁻¹' D) := c.hyp.setup.oddT.preimage H
  have hcomm : Commute uH vH :=
    (OddLocal.commute_iff_of_mem_pCore hDH
      (CFSG.pCore_isPGroup (p := 2) (G := H))
      (show uH ∈ ((↑) : H → G) ⁻¹' D from hu)
      (show vH ∈ ((↑) : H → G) ⁻¹' D from hv)).mp hquot
  exact (commute_coe_iff (H := H)).mpr hcomm

theorem SzCfg.commute_mk_iff (c : SzCfg G D d E e n) {u v : ↥(Subgroup.closure E)}
    (hu : (u : G) ∈ E) (hv : (v : G) ∈ E) :
    Commute (szMk E u) (szMk E v) ↔ Commute u v :=
  OddLocal.commute_iff_of_mem_pCore c.setup.oddT
    (CFSG.pCore_isPGroup (p := 2) (G := ↥(Subgroup.closure E)))
    (show u ∈ szE E from hu) (show v ∈ szE E from hv)

theorem SzCfg.isBenderGroup_zStar (c : SzCfg G D d E e n) :
    IsBenderGroup (↥(Subgroup.closure E) ⧸ zStar ↥(Subgroup.closure E)) := by
  obtain ⟨e⟩ := c.iso
  exact IsBenderGroup.isSuzuki n c.one_le e

private theorem center_quotient_pCore_eq_bot (c : SzCfg G D d E e n) :
    Subgroup.center (SzBar E) = ⊥ := by
  let H : Subgroup G := Subgroup.closure E
  let Q : Subgroup H := CFSG.pCore 2 H
  let K : Type := H ⧸ Q
  have hQ2 : CFSG.pCore 2 K = ⊥ := CFSG.AGLEmbedding.pCore_quotient_pCore_eq_bot' 2
  have hno2 : ∀ N : Subgroup K, N.Normal → IsPGroup 2 N → N = ⊥ := by
    intro N hN hN2
    have hle := CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup hN hN2
    exact le_bot_iff.mp (by simpa [hQ2] using hle)
  have hodd : Odd (Nat.card (Subgroup.center K)) := OddLocal.odd_card_center hno2
  have hperf : commutator K = ⊤ :=
    OddTransp.commutator_eq_top_of_surjective (QuotientGroup.mk'_surjective Q) c.perfect
  have hQZ : Q ≤ zStar H := pCore_le_zStar
  have hZmap : (zStar H).map (QuotientGroup.mk' Q) = Subgroup.center K := by
    rw [zStar, Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective Q)]
  obtain ⟨eH⟩ := c.iso
  have eK : K ⧸ Subgroup.center K ≃* SzModel n :=
    ((QuotientGroup.quotientMulEquivOfEq hZmap.symm).trans
      (QuotientGroup.quotientQuotientEquivQuotient Q (zStar H) hQZ)).trans eH
  exact OddLocal.center_eq_bot_of_sz hperf hodd eK

theorem SzCfg.zStar_eq (c : SzCfg G D d E e n) :
    zStar ↥(Subgroup.closure E) = CFSG.pCore 2 ↥(Subgroup.closure E) := by
  have hZ : Subgroup.center (SzBar E) = ⊥ := center_quotient_pCore_eq_bot c
  rw [zStar, hZ, MonoidHom.comap_bot, QuotientGroup.ker_mk']

theorem SzCfg.iso_bar (c : SzCfg G D d E e n) : Nonempty (SzBar E ≃* SzModel n) := by
  obtain ⟨e⟩ := c.iso
  exact ⟨(QuotientGroup.quotientMulEquivOfEq c.zStar_eq).symm.trans e⟩

theorem SzCfg.isBenderGroup (c : SzCfg G D d E e n) : IsBenderGroup (SzBar E) := by
  obtain ⟨e⟩ := c.iso_bar
  exact IsBenderGroup.isSuzuki n c.one_le e

theorem SzCfg.not_three_dvd (c : SzCfg G D d E e n) :
    ¬ 3 ∣ Nat.card ↥(Subgroup.closure E) := by
  let H : Subgroup G := Subgroup.closure E
  let Q : Subgroup H := CFSG.pCore 2 H
  have hQ3 : ¬ 3 ∣ Nat.card Q := by
    intro h3
    obtain ⟨k, hk⟩ := (IsPGroup.iff_card (p := 2) (G := Q)).mp
      (CFSG.pCore_isPGroup (p := 2) (G := H))
    rw [hk] at h3
    exact absurd (Nat.Prime.dvd_of_dvd_pow Nat.prime_three h3) (by norm_num)
  obtain ⟨e⟩ := c.iso_bar
  have hq3 : ¬ 3 ∣ Nat.card (H ⧸ CFSG.pCore 2 H) := by
    rw [Nat.card_congr e.toEquiv]
    exact RootClosure.not_three_dvd_card_szModel c.one_le
  have hcard := Subgroup.card_eq_card_quotient_mul_card_subgroup (zStar H)
  rw [c.zStar_eq] at hcard
  intro h3
  rw [hcard] at h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h3 with h | h
  · exact hq3 h
  · exact hQ3 h

end CFSG.Timmesfeld.Bridge.OddRoot
