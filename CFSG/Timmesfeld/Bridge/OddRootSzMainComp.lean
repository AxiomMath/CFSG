module

public import CFSG.Timmesfeld.Bridge.OddRootSzMainSetup
public import CFSG.LocalAnalysis.ComponentClassification.AschbacherToolkitBenderBasic
import CFSG.Timmesfeld.Bridge.RootClosureThree
import CFSG.CGT.T75M.SzBorel
import CFSG.StronglyEmbedded.BenderCentre
import CFSG.LocalAnalysis.ComponentClassification.Asc76BenderFactsBasic
public import CFSG.Timmesfeld.Closure.Bender

public section

namespace CFSG.Timmesfeld.Bridge.OddRoot

open CFSG.Timmesfeld CFSG.Timmesfeld.Connectivity CFSG.Timmesfeld.Bridge
  CFSG.Timmesfeld.Bridge.OddTransp
  CFSG.Timmesfeld.Bridge.Asc72 CFSG.BenderSuzuki CFSG.StronglyEmbedded.BenderCentre
  CFSG.ComponentClassification.AschbacherToolkit.Bender

variable {G : Type} [Group G] [Finite G] {D : Set G} {d e : G} {E : Set G} {n : ℕ}

@[expose] def szS (E : Set G) (P : Sylow 2 (SzBar E)) : Subgroup G :=
  ((P : Subgroup (SzBar E)).comap (szMk E)).map (Subgroup.closure E).subtype

@[expose] def szN (E : Set G) (P : Sylow 2 (SzBar E)) : Subgroup G :=
  ((Subgroup.normalizer ((P : Subgroup (SzBar E)) : Set (SzBar E))).comap (szMk E)).map
    (Subgroup.closure E).subtype

theorem mem_szS_iff {P : Sylow 2 (SzBar E)} {x : G} : x ∈ szS E P ↔
    ∃ h : x ∈ Subgroup.closure E, szMk E ⟨x, h⟩ ∈ (P : Subgroup (SzBar E)) := by
  rw [szS, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [Subgroup.mem_comap] at hy
    have hx : x ∈ Subgroup.closure E := hyx ▸ y.2
    refine ⟨hx, ?_⟩
    have hy' : (⟨x, hx⟩ : ↥(Subgroup.closure E)) = y := Subtype.ext hyx.symm
    rwa [hy']
  · rintro ⟨hx, hxP⟩
    exact ⟨⟨x, hx⟩, hxP, rfl⟩

theorem mem_szN_iff {P : Sylow 2 (SzBar E)} {x : G} : x ∈ szN E P ↔
    ∃ h : x ∈ Subgroup.closure E,
      szMk E ⟨x, h⟩ ∈ Subgroup.normalizer ((P : Subgroup (SzBar E)) : Set (SzBar E)) := by
  rw [szN, Subgroup.mem_map]
  constructor
  · rintro ⟨y, hy, hyx⟩
    rw [Subgroup.mem_comap] at hy
    have hx : x ∈ Subgroup.closure E := hyx ▸ y.2
    refine ⟨hx, ?_⟩
    have hy' : (⟨x, hx⟩ : ↥(Subgroup.closure E)) = y := Subtype.ext hyx.symm
    rwa [hy']
  · rintro ⟨hx, hxN⟩
    exact ⟨⟨x, hx⟩, hxN, rfl⟩

theorem szQ_le_szS (E : Set G) (P : Sylow 2 (SzBar E)) : szQ E ≤ szS E P := by
  intro x hx
  rw [mem_szS_iff]
  obtain ⟨hxH, hxQ⟩ := mem_szQ_iff.mp hx
  refine ⟨hxH, ?_⟩
  have h1 : szMk E ⟨x, hxH⟩ = 1 :=
    (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 (Subgroup.closure E)) _).mpr hxQ
  rw [h1]
  exact one_mem _

theorem szS_le_szN (E : Set G) (P : Sylow 2 (SzBar E)) : szS E P ≤ szN E P := by
  intro x hx
  rw [mem_szN_iff]
  obtain ⟨hxH, hxP⟩ := mem_szS_iff.mp hx
  exact ⟨hxH, Subgroup.le_normalizer hxP⟩

theorem szN_le_closure (E : Set G) (P : Sylow 2 (SzBar E)) : szN E P ≤ Subgroup.closure E :=
  fun _ hx => (mem_szN_iff.mp hx).1

theorem isPGroup_szS (E : Set G) (P : Sylow 2 (SzBar E)) : IsPGroup 2 ↥(szS E P) := by
  have hker : IsPGroup 2 (szMk E).ker := by
    rw [szMk, QuotientGroup.ker_mk']
    exact CFSG.pCore_isPGroup (p := 2) (G := Subgroup.closure E)
  have hpre : IsPGroup 2 ↥((P : Subgroup (SzBar E)).comap (szMk E)) :=
    IsPGroup.comap_of_ker_isPGroup P.isPGroup' (szMk E) hker
  change IsPGroup 2 ↥((((P : Subgroup (SzBar E)).comap (szMk E)).map
    (Subgroup.closure E).subtype))
  exact hpre.map (Subgroup.closure E).subtype

theorem conj_mem_szS {P : Sylow 2 (SzBar E)} {h s : G} (hh : h ∈ szN E P)
    (hs : s ∈ szS E P) : h * s * h⁻¹ ∈ szS E P := by
  rw [mem_szS_iff] at hs ⊢
  rw [mem_szN_iff] at hh
  obtain ⟨hsH, hsmem⟩ := hs
  obtain ⟨hhH, hhnorm⟩ := hh
  have hconjH : h * s * h⁻¹ ∈ Subgroup.closure E :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hhH hsH) (Subgroup.inv_mem _ hhH)
  refine ⟨hconjH, ?_⟩
  have hdecomp : (⟨h * s * h⁻¹, hconjH⟩ : ↥(Subgroup.closure E)) =
      ⟨h, hhH⟩ * ⟨s, hsH⟩ * (⟨h, hhH⟩)⁻¹ := rfl
  have himg : szMk E ⟨h * s * h⁻¹, hconjH⟩ =
      szMk E ⟨h, hhH⟩ * szMk E ⟨s, hsH⟩ * (szMk E ⟨h, hhH⟩)⁻¹ := by
    rw [hdecomp, map_mul, map_mul, map_inv]
  rw [himg]
  exact (Subgroup.mem_normalizer_iff.mp hhnorm (szMk E ⟨s, hsH⟩)).mp hsmem

theorem not_two_dvd_index_szS (E : Set G) (P : Sylow 2 (SzBar E)) :
    ¬ 2 ∣ ((szS E P).subgroupOf (szN E P)).index := by
  let H : Subgroup G := Subgroup.closure E
  let SH : Subgroup H := (P : Subgroup (SzBar E)).comap (szMk E)
  let NH : Subgroup H :=
    (Subgroup.normalizer ((P : Subgroup (SzBar E)) : Set (SzBar E))).comap (szMk E)
  have hSmap : SH.map H.subtype = szS E P := rfl
  have hNmap : NH.map H.subtype = szN E P := rfl
  have hkerSH : (szMk E).ker ≤ SH := by
    intro y hy
    show szMk E y ∈ (P : Subgroup (SzBar E))
    rw [show szMk E y = 1 from hy]
    exact one_mem _
  have hkerNH : (szMk E).ker ≤ NH := by
    intro y hy
    show szMk E y ∈ Subgroup.normalizer ((P : Subgroup (SzBar E)) : Set (SzBar E))
    rw [show szMk E y = 1 from hy]
    exact Subgroup.one_mem _
  have hSHmap : SH.map (szMk E) = (P : Subgroup (SzBar E)) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hNHmap : NH.map (szMk E) =
      Subgroup.normalizer ((P : Subgroup (SzBar E)) : Set (SzBar E)) :=
    Subgroup.map_comap_eq_self_of_surjective (QuotientGroup.mk'_surjective _) _
  have hrel1 : (szS E P).relIndex (szN E P) = SH.relIndex NH := by
    rw [← hSmap, ← hNmap]
    exact Subgroup.relIndex_map_map_of_injective (f := H.subtype) SH NH H.subtype_injective
  have hrel2 : SH.relIndex NH =
      (P : Subgroup (SzBar E)).relIndex
        (Subgroup.normalizer ((P : Subgroup (SzBar E)) : Set (SzBar E))) := by
    calc SH.relIndex NH = (SH ⊔ (szMk E).ker).relIndex (NH ⊔ (szMk E).ker) := by
          rw [show SH ⊔ (szMk E).ker = SH from sup_eq_left.mpr hkerSH,
            show NH ⊔ (szMk E).ker = NH from sup_eq_left.mpr hkerNH]
      _ = (SH.map (szMk E)).relIndex (NH.map (szMk E)) :=
          (Subgroup.relIndex_map_map (szMk E) SH NH).symm
      _ = (P : Subgroup (SzBar E)).relIndex
            (Subgroup.normalizer ((P : Subgroup (SzBar E)) : Set (SzBar E))) := by
          rw [hSHmap, hNHmap]
  change ¬ 2 ∣ (szS E P).relIndex (szN E P)
  rw [hrel1, hrel2]
  have hdvd : (P : Subgroup (SzBar E)).relIndex
      (Subgroup.normalizer ((P : Subgroup (SzBar E)) : Set (SzBar E))) ∣
      (P : Subgroup (SzBar E)).index :=
    Subgroup.relIndex_dvd_index_of_le (Subgroup.le_normalizer)
  exact fun h => Sylow.not_dvd_index P (h.trans hdvd)

theorem szMk_eq_one_iff_mem_szQ {x : G} (hx : x ∈ Subgroup.closure E) :
    szMk E ⟨x, hx⟩ = 1 ↔ x ∈ szQ E := by
  rw [szMk]
  constructor
  · intro h
    exact mem_szQ_iff.mpr ⟨hx,
      (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 (Subgroup.closure E)) _).mp h⟩
  · intro hxQ
    obtain ⟨_, hq⟩ := mem_szQ_iff.mp hxQ
    exact (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 (Subgroup.closure E)) _).mpr hq

private theorem szMk_eq_of_inv_mul_mem {u v : G}
    (hu : u ∈ Subgroup.closure E) (hv : v ∈ Subgroup.closure E)
    (h : u⁻¹ * v ∈ szQ E) : szMk E ⟨v, hv⟩ = szMk E ⟨u, hu⟩ := by
  have hker : szMk E ⟨u⁻¹ * v, Subgroup.mul_mem _
    (Subgroup.inv_mem _ hu) hv⟩ = 1 :=
    (szMk_eq_one_iff_mem_szQ (Subgroup.mul_mem _
      (Subgroup.inv_mem _ hu) hv)).mpr h
  have h1 : (szMk E ⟨u, hu⟩)⁻¹ * szMk E ⟨v, hv⟩ = 1 := by
    rw [← map_inv, ← map_mul]
    exact hker
  calc szMk E ⟨v, hv⟩ =
      szMk E ⟨u, hu⟩ * ((szMk E ⟨u, hu⟩)⁻¹ * szMk E ⟨v, hv⟩) := by group
    _ = szMk E ⟨u, hu⟩ := by rw [h1, mul_one]

private theorem szMk_mul_self_eq_one (c : SzCfg G D d E e n) {a : G} (ha : a ∈ E) :
    szMk E ⟨a, Subgroup.subset_closure ha⟩ * szMk E ⟨a, Subgroup.subset_closure ha⟩ = 1 := by
  rw [← map_mul, ← map_one (szMk E)]
  congr 1
  exact Subtype.ext (c.hyp.setup.oddT.mul_self_eq_one (c.subset_commSet ha).1)

private theorem szMk_ne_one (c : SzCfg G D d E e n) {a : G} (ha : a ∈ E) :
    szMk E ⟨a, Subgroup.subset_closure ha⟩ ≠ 1 := fun h =>
  c.not_mem_szQ ha ((szMk_eq_one_iff_mem_szQ (Subgroup.subset_closure ha)).mp h)

theorem SzCfg.exists_szS (c : SzCfg G D d E e n) {a : G} (ha : a ∈ E) :
    ∃ P : Sylow 2 (SzBar E), a ∈ szS E P := by
  let aH : ↥(Subgroup.closure E) := ⟨a, Subgroup.subset_closure ha⟩
  have hP : IsPGroup 2 (Subgroup.zpowers (szMk E aH)) :=
    RootClosure.isPGroup_zpowers_of_mul_self_eq_one (szMk_mul_self_eq_one c ha)
  obtain ⟨P, hle⟩ := hP.exists_le_sylow
  refine ⟨P, ?_⟩
  rw [mem_szS_iff]
  exact ⟨Subgroup.subset_closure ha, hle (Subgroup.mem_zpowers (szMk E aH))⟩

theorem SzCfg.exists_conj_of_inv_mul_mem (c : SzCfg G D d E e n) {u u' : G} (hu : u ∈ E)
    (hu' : u' ∈ E) (h : u⁻¹ * u' ∈ szQ E) : ∃ y ∈ szQ E, y * u * y⁻¹ = u' := by
  let H : Subgroup G := Subgroup.closure E
  have huH : u ∈ H := Subgroup.subset_closure hu
  have hu'H : u' ∈ H := Subgroup.subset_closure hu'
  let uH : H := ⟨u, huH⟩
  let u'H : H := ⟨u', hu'H⟩
  have hcomm : Commute u u' :=
    c.commute_of_inv_mul_mem (c.subset_commSet hu).1 (c.subset_commSet hu').1 huH h
  have hqval : u' * u⁻¹ ∈ szQ E := by
    rw [(hcomm.symm.inv_right).eq]
    exact h
  have hqH : u'H * uH⁻¹ ∈ CFSG.pCore 2 H := by
    have hprod : (⟨u' * u⁻¹, H.mul_mem hu'H (H.inv_mem huH)⟩ : H) = u'H * uH⁻¹ := rfl
    rw [← hprod]
    exact (mem_szQ_iff.mp hqval).2
  obtain ⟨x, hx, hxu⟩ := c.exists_not_commute hu
  let xH : H := ⟨x, Subgroup.subset_closure hx⟩
  have hxuH : ¬ Commute uH xH := fun hc =>
    hxu (((commute_coe_iff (H := H)).mpr hc).symm)
  have hmk' : szMk E ⟨u', hu'H⟩ = szMk E ⟨u, huH⟩ :=
    szMk_eq_of_inv_mul_mem huH hu'H h
  have hxu'H : ¬ Commute u'H xH := fun hc => hxuH (by
    have hcK : Commute (szMk E ⟨u', hu'H⟩) (szMk E ⟨x, Subgroup.subset_closure hx⟩) :=
      (c.commute_mk_iff (u := ⟨u', hu'H⟩) (v := ⟨x, Subgroup.subset_closure hx⟩)
        hu' hx).mpr hc
    have huK : Commute (szMk E ⟨u, huH⟩) (szMk E ⟨x, Subgroup.subset_closure hx⟩) := by
      simpa [hmk'] using hcK
    exact (c.commute_mk_iff (u := ⟨u, huH⟩) (v := ⟨x, Subgroup.subset_closure hx⟩)
      hu hx).mp huK)
  obtain ⟨y, hy, hyu⟩ := OddTransp.exists_conj_of_mul_inv_mem
    (D := szE E) (Q := CFSG.pCore 2 H) c.setup.oddT c.setup.normal
    (CFSG.pCore_isPGroup (p := 2) (G := H)) (show uH ∈ szE E from hu)
    (show xH ∈ szE E from hx) hxuH (show u'H ∈ szE E from hu') hqH hxu'H
  have hyQ : (y : G) ∈ szQ E :=
    mem_szQ_iff.mpr ⟨y.2, Subgroup.commutator_le_left _ _ hy⟩
  refine ⟨(y : G), hyQ, ?_⟩
  have hcoe := congrArg (fun z : H => (z : G)) hyu
  simpa [uH, u'H] using hcoe

private theorem orderOf_szMk_eq_two (c : SzCfg G D d E e n) {a : G} (ha : a ∈ E) :
    orderOf (szMk E ⟨a, Subgroup.subset_closure ha⟩) = 2 :=
  orderOf_eq_prime (by rw [pow_two]; exact szMk_mul_self_eq_one c ha) (szMk_ne_one c ha)

private theorem exists_szN_of_mem_normalizer (E : Set G) (P : Sylow 2 (SzBar E))
    {g : SzBar E}
    (hg : g ∈ Subgroup.normalizer ((P : Subgroup (SzBar E)) : Set (SzBar E))) :
    ∃ h : ↥(Subgroup.closure E), (h : G) ∈ szN E P ∧ szMk E h = g := by
  obtain ⟨h, hh⟩ := QuotientGroup.mk'_surjective
    (CFSG.pCore 2 (Subgroup.closure E)) g
  refine ⟨h, mem_szN_iff.mpr ⟨h.2, ?_⟩, hh⟩
  have hEq : szMk E h = g := hh
  rw [hEq]
  exact hg

theorem SzCfg.mem_szS_iff_commute (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E))
    {a u : G} (ha : a ∈ E) (hu : u ∈ E) (haP : a ∈ szS E P) :
    u ∈ szS E P ↔ Commute u a := by
  let H : Subgroup G := Subgroup.closure E
  have haH : a ∈ H := Subgroup.subset_closure ha
  have huH : u ∈ H := Subgroup.subset_closure hu
  let aH : H := ⟨a, haH⟩
  let uH : H := ⟨u, huH⟩
  have haPK : szMk E aH ∈ (P : Subgroup (SzBar E)) := (mem_szS_iff.mp haP).2
  constructor
  · intro huS
    have huPK : szMk E uH ∈ (P : Subgroup (SzBar E)) := (mem_szS_iff.mp huS).2
    have hu2 : szMk E uH * szMk E uH = 1 := szMk_mul_self_eq_one c hu
    have hcommK : Commute (szMk E uH) (szMk E aH) :=
      (Asc72.IsBenderGroup.commute_of_mul_self_eq_one c.isBenderGroup P huPK hu2
        (szMk E aH) haPK)
    exact (commute_coe_iff (H := H)).mpr
      ((c.commute_mk_iff (u := uH) (v := aH) hu ha).mp hcommK)
  · intro hcomm
    have hcommK : Commute (szMk E uH) (szMk E aH) :=
      (c.commute_mk_iff (u := uH) (v := aH) hu ha).mpr
        ((commute_coe_iff (H := H)).mp hcomm)
    obtain ⟨q, k, hB, -⟩ := Asc72.IsBenderGroup.exists_fusionBenderBorel c.isBenderGroup
    have hSE := (hB P).1
    have haN : szMk E aH ∈
        Subgroup.normalizer ((P : Subgroup (SzBar E)) : Set (SzBar E)) :=
      Subgroup.le_normalizer haPK
    have huN := mem_of_commute_of_stronglyEmbedded hSE haN
      (orderOf_szMk_eq_two c ha) hcommK
    have hu2 : szMk E uH * szMk E uH = 1 := szMk_mul_self_eq_one c hu
    have huZ := CFSG.CGT.T75M.mem_center_of_mem_normalizer_sylow c.isBenderGroup P huN hu2
    have huPK : szMk E uH ∈ (P : Subgroup (SzBar E)) := by
      have hle : (Subgroup.center (P : Subgroup (SzBar E))).map
          (P : Subgroup (SzBar E)).subtype ≤ (P : Subgroup (SzBar E)) := by
        rintro _ ⟨z, -, rfl⟩
        exact z.2
      exact hle huZ
    exact mem_szS_iff.mpr ⟨huH, huPK⟩

theorem SzCfg.mem_szN_of_conj_mem (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E)) {a h : G}
    (ha : a ∈ E) (haP : a ∈ szS E P) (hh : h ∈ Subgroup.closure E)
    (hha : h * a * h⁻¹ ∈ szS E P) : h ∈ szN E P := by
  let H : Subgroup G := Subgroup.closure E
  have haH : a ∈ H := Subgroup.subset_closure ha
  let aH : H := ⟨a, haH⟩
  let hH : H := ⟨h, hh⟩
  have haPK : szMk E aH ∈ (P : Subgroup (SzBar E)) := (mem_szS_iff.mp haP).2
  have hconjH : h * a * h⁻¹ ∈ H :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hh haH) (Subgroup.inv_mem _ hh)
  have hconjP : szMk E ⟨h * a * h⁻¹, hconjH⟩ ∈ (P : Subgroup (SzBar E)) :=
    (mem_szS_iff.mp hha).2
  have hdecomp : (⟨h * a * h⁻¹, hconjH⟩ : H) = hH * aH * hH⁻¹ := rfl
  have hconjEq : szMk E ⟨h * a * h⁻¹, hconjH⟩ =
      szMk E hH * szMk E aH * (szMk E hH)⁻¹ := by
    rw [hdecomp, map_mul, map_mul, map_inv]
  rw [hconjEq] at hconjP
  have hconjNe : szMk E hH * szMk E aH * (szMk E hH)⁻¹ ≠ 1 := by
    intro h1
    apply szMk_ne_one c ha
    calc szMk E aH = (szMk E hH)⁻¹ * (szMk E hH * szMk E aH * (szMk E hH)⁻¹) *
          szMk E hH := by group
      _ = 1 := by rw [h1]; group
  by_contra hgN
  obtain ⟨q, k, hB, -⟩ := Asc72.IsBenderGroup.exists_fusionBenderBorel c.isBenderGroup
  have hne : (szMk E hH) • P ≠ P := fun h1 =>
    hgN (mem_szN_iff.mpr ⟨hh, by
      change szMk E hH ∈ Subgroup.normalizer ((P : Subgroup (SzBar E)) : Set (SzBar E))
      exact Sylow.smul_eq_iff_mem_normalizer.mp h1⟩)
  have hmemgP : szMk E hH * szMk E aH * (szMk E hH)⁻¹ ∈
      (((szMk E hH) • P : Sylow 2 (SzBar E)) : Subgroup (SzBar E)) := by
    rw [CFSG.ComponentClassification.AschbacherToolkit.Bender.Omega.mem_conj_smul_iff]
    have hEq : (szMk E hH)⁻¹ * (szMk E hH * szMk E aH * (szMk E hH)⁻¹) * szMk E hH =
        szMk E aH := by group
    rw [hEq]
    exact haPK
  have hinf : (((szMk E hH) • P : Sylow 2 (SzBar E)) :
      Subgroup (SzBar E)) ⊓ P = ⊥ :=
    CFSG.ComponentClassification.Asc76X.inf_eq_bot_of_fusionBenderBorel hB hne
  have hmem : szMk E hH * szMk E aH * (szMk E hH)⁻¹ ∈
      (((szMk E hH) • P : Sylow 2 (SzBar E)) : Subgroup (SzBar E)) ⊓ P :=
    ⟨hmemgP, hconjP⟩
  rw [hinf] at hmem
  exact hconjNe (by simpa using hmem)

theorem SzCfg.mem_szQ_of_mem_szN (c : SzCfg G D d E e n) {P P' : Sylow 2 (SzBar E)}
    (hne : P ≠ P') {s : G} (hs : s ∈ szS E P) (hs' : s ∈ szN E P') : s ∈ szQ E := by
  obtain ⟨hsH, hsP⟩ := mem_szS_iff.mp hs
  obtain ⟨hsH', hsN⟩ := mem_szN_iff.mp hs'
  have hmem : szMk E ⟨s, hsH⟩ ∈ (P : Subgroup (SzBar E)) ⊓
      Subgroup.normalizer ((P' : Subgroup (SzBar E)) : Set (SzBar E)) := ⟨hsP, hsN⟩
  have hinfN : (P : Subgroup (SzBar E)) ⊓
      Subgroup.normalizer ((P' : Subgroup (SzBar E)) : Set (SzBar E)) =
      (P : Subgroup (SzBar E)) ⊓ P' :=
    IsPGroup.inf_normalizer_sylow P.isPGroup' P'
  rw [hinfN] at hmem
  obtain ⟨q, k, hB, -⟩ := Asc72.IsBenderGroup.exists_fusionBenderBorel c.isBenderGroup
  have hinf : (P : Subgroup (SzBar E)) ⊓ P' = ⊥ :=
    CFSG.ComponentClassification.Asc76X.inf_eq_bot_of_fusionBenderBorel hB hne
  rw [hinf] at hmem
  exact (szMk_eq_one_iff_mem_szQ hsH).mp (by simpa using hmem)

private theorem sylow_exists_not_commute (c : SzCfg G D d E e n)
    (P : Sylow 2 (SzBar E)) :
    ∃ x ∈ (P : Subgroup (SzBar E)), ∃ y ∈ (P : Subgroup (SzBar E)), x * y ≠ y * x := by
  by_contra h
  push Not at h
  have htop : Subgroup.center (P : Subgroup (SzBar E)) = ⊤ := by
    rw [Subgroup.eq_top_iff']
    intro z
    rw [Subgroup.mem_center_iff]
    intro w
    exact Subtype.ext (h w w.2 z z.2)
  obtain ⟨e⟩ := c.iso_bar
  have hB := CFSG.ComponentClassification.Asc76X.fusionBenderBorel_of_mulEquiv_sz c.one_le e
  obtain ⟨-, -, hZ, hPcard⟩ := benderBorel_sylowCenter hB P
  have hZcard : Nat.card (Subgroup.center (P : Subgroup (SzBar E))) = 2 ^ (2 * n + 1) := by
    calc Nat.card (Subgroup.center (P : Subgroup (SzBar E)))
        = Nat.card ((Subgroup.center (P : Subgroup (SzBar E))).map
            (P : Subgroup (SzBar E)).subtype) :=
          (Subgroup.card_map_of_injective (P : Subgroup (SzBar E)).subtype_injective).symm
      _ = Nat.card (sylowCenter (P : Subgroup (SzBar E))) := by
          rw [map_center_eq_sylowCenter]
      _ = 2 ^ (2 * n + 1) := hZ
  have hcardP : Nat.card (P : Subgroup (SzBar E)) = (2 ^ (2 * n + 1)) ^ 2 := hPcard
  have heq : 2 ^ (2 * n + 1) = (2 ^ (2 * n + 1)) ^ 2 := by
    calc 2 ^ (2 * n + 1) = Nat.card (Subgroup.center (P : Subgroup (SzBar E))) := hZcard.symm
      _ = Nat.card (⊤ : Subgroup (P : Subgroup (SzBar E))) := by rw [htop]
      _ = Nat.card (P : Subgroup (SzBar E)) := Subgroup.card_top
      _ = (2 ^ (2 * n + 1)) ^ 2 := hcardP
  have hq4 : 4 ≤ 2 ^ (2 * n + 1) := by
    have hn : 1 ≤ n := c.one_le
    calc 4 = 2 ^ 2 := by norm_num
      _ ≤ 2 ^ (2 * n + 1) :=
          Nat.pow_le_pow_right (by norm_num) (by omega)
  rw [pow_two] at heq
  nlinarith

theorem SzCfg.exists_not_commute_szS (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E)) :
    ∃ s ∈ szS E P, ∃ s' ∈ szS E P, s * s' * s⁻¹ * s'⁻¹ ∉ szQ E := by
  obtain ⟨x, hxP, y, hyP, hxy⟩ := sylow_exists_not_commute c P
  obtain ⟨xH, hxeq⟩ := QuotientGroup.mk'_surjective
    (CFSG.pCore 2 (Subgroup.closure E)) x
  obtain ⟨yH, hyeq⟩ := QuotientGroup.mk'_surjective
    (CFSG.pCore 2 (Subgroup.closure E)) y
  have hxS : (xH : G) ∈ szS E P := mem_szS_iff.mpr ⟨xH.2, by
    change (QuotientGroup.mk' (CFSG.pCore 2 (Subgroup.closure E))) xH ∈
      (P : Subgroup (SzBar E))
    rwa [hxeq]⟩
  have hyS : (yH : G) ∈ szS E P := mem_szS_iff.mpr ⟨yH.2, by
    change (QuotientGroup.mk' (CFSG.pCore 2 (Subgroup.closure E))) yH ∈
      (P : Subgroup (SzBar E))
    rwa [hyeq]⟩
  refine ⟨(xH : G), hxS, (yH : G), hyS, ?_⟩
  intro hQ
  let p : ↥(Subgroup.closure E) := xH * yH * xH⁻¹ * yH⁻¹
  have hxeq' : szMk E xH = x := hxeq
  have hyeq' : szMk E yH = y := hyeq
  have hpimg : szMk E p = x * y * x⁻¹ * y⁻¹ := by
    dsimp [p]
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hxeq', hyeq']
  have hp1 : szMk E p = 1 := (szMk_eq_one_iff_mem_szQ (x := (p : G)) p.2).mpr hQ
  have hcomm1 : x * y * x⁻¹ * y⁻¹ = 1 := by rw [← hpimg, hp1]
  have hcomm : x * y = y * x := by
    have h := congrArg (fun z => z * (y * x)) hcomm1
    simpa [mul_assoc] using h
  exact hxy hcomm

theorem SzCfg.inv_mul_conj_mem_szQ (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E))
    {a s : G} (ha : a ∈ E) (haP : a ∈ szS E P) (hs : s ∈ szS E P) :
    a⁻¹ * (s * a * s⁻¹) ∈ szQ E := by
  let H : Subgroup G := Subgroup.closure E
  have haH : a ∈ H := Subgroup.subset_closure ha
  have hsH : s ∈ H := (mem_szS_iff.mp hs).1
  let aH : H := ⟨a, haH⟩
  let sH : H := ⟨s, hsH⟩
  have haPK : szMk E aH ∈ (P : Subgroup (SzBar E)) := (mem_szS_iff.mp haP).2
  have hsPK : szMk E sH ∈ (P : Subgroup (SzBar E)) := (mem_szS_iff.mp hs).2
  have ha2 : szMk E aH * szMk E aH = 1 := szMk_mul_self_eq_one c ha
  have hcommK : Commute (szMk E sH) (szMk E aH) :=
    (Asc72.IsBenderGroup.commute_of_mul_self_eq_one c.isBenderGroup P haPK ha2
      (szMk E sH) hsPK).symm
  have hconj : szMk E sH * szMk E aH * (szMk E sH)⁻¹ = szMk E aH := by
    rw [hcommK.eq]
    group
  have hvalH : a⁻¹ * (s * a * s⁻¹) ∈ H :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ haH)
      (Subgroup.mul_mem _ (Subgroup.mul_mem _ hsH haH) (Subgroup.inv_mem _ hsH))
  have hdec : (⟨a⁻¹ * (s * a * s⁻¹), hvalH⟩ : H) = aH⁻¹ * (sH * aH * sH⁻¹) := rfl
  have himg : szMk E ⟨a⁻¹ * (s * a * s⁻¹), hvalH⟩ = 1 := by
    rw [hdec, map_mul, map_mul, map_mul, map_inv, map_inv, hconj]
    group
  exact (szMk_eq_one_iff_mem_szQ hvalH).mp himg

theorem SzCfg.mk_mem_sylowCenter (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E))
    {a : ↥(Subgroup.closure E)} (ha : (a : G) ∈ E)
    (haP : szMk E a ∈ (P : Subgroup (SzBar E))) :
    szMk E a ∈ sylowCenter (P : Subgroup (SzBar E)) := by
  have ha2 : szMk E a * szMk E a = 1 := szMk_mul_self_eq_one c ha
  rw [mem_sylowCenter]
  refine ⟨haP, fun y hy => ?_⟩
  exact (Asc72.IsBenderGroup.commute_of_mul_self_eq_one c.isBenderGroup P haP ha2 y hy).symm

theorem SzCfg.exists_comp_of_mem_sylowCenter (c : SzCfg G D d E e n)
    (P : Sylow 2 (SzBar E)) {a : G} (ha : a ∈ E) (haP : a ∈ szS E P) {w : SzBar E}
    (hw : w ∈ sylowCenter (P : Subgroup (SzBar E))) (hw1 : w ≠ 1) :
    ∃ b ∈ szComp E a, ∃ hb : b ∈ Subgroup.closure E, szMk E ⟨b, hb⟩ = w := by
  let H : Subgroup G := Subgroup.closure E
  have haH : a ∈ H := Subgroup.subset_closure ha
  let aH : H := ⟨a, haH⟩
  have haPK : szMk E aH ∈ (P : Subgroup (SzBar E)) := (mem_szS_iff.mp haP).2
  have haZ : szMk E aH ∈ sylowCenter (P : Subgroup (SzBar E)) :=
    c.mk_mem_sylowCenter P ha haPK
  have haZ1 : szMk E aH ≠ 1 := szMk_ne_one c ha
  have haZ' : szMk E aH ∈ (P : Subgroup (SzBar E)) ∧
      ∀ q ∈ (P : Subgroup (SzBar E)), Commute q (szMk E aH) := by
    have h := mem_sylowCenter.mp haZ
    exact ⟨h.1, fun q hq => h.2 q hq⟩
  have hw' : w ∈ (P : Subgroup (SzBar E)) ∧
      ∀ q ∈ (P : Subgroup (SzBar E)), Commute q w := by
    have h := mem_sylowCenter.mp hw
    exact ⟨h.1, fun q hq => h.2 q hq⟩
  obtain ⟨g, hgN, hgconj⟩ :=
    Asc72.IsBenderGroup.exists_normalizer_conj c.isBenderGroup P haZ' haZ1 hw' hw1
  obtain ⟨h, hhN, hhEq⟩ := exists_szN_of_mem_normalizer E P hgN
  have hbE : (h : G) * a * (h : G)⁻¹ ∈ E := c.conj_mem h.2 ha
  have hbH : (h : G) * a * (h : G)⁻¹ ∈ H :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ h.2 haH) (Subgroup.inv_mem _ h.2)
  let b : G := (h : G) * a * (h : G)⁻¹
  have hbimg : szMk E ⟨b, hbH⟩ = w := by
    have hdec : (⟨b, hbH⟩ : H) = h * aH * h⁻¹ := rfl
    rw [hdec, map_mul, map_mul, map_inv, hhEq, hgconj]
  have hbcomm : Commute b a := by
    have hbK : Commute (szMk E ⟨b, hbH⟩) (szMk E aH) := by
      rw [hbimg]
      exact ((mem_sylowCenter.mp hw).2 (szMk E aH) haPK).symm
    exact (commute_coe_iff (H := H)).mpr
      ((c.commute_mk_iff (u := ⟨b, hbH⟩) (v := aH) hbE ha).mp hbK)
  exact ⟨b, ⟨hbE, hbcomm⟩, hbH, hbimg⟩

theorem SzCfg.exists_szN_conj (c : SzCfg G D d E e n) (P : Sylow 2 (SzBar E)) {a b : G}
    (ha : a ∈ E) (hb : b ∈ E) (haP : a ∈ szS E P) (hbP : b ∈ szS E P) :
    ∃ h ∈ szN E P, h * a * h⁻¹ = b := by
  let H : Subgroup G := Subgroup.closure E
  have haH : a ∈ H := Subgroup.subset_closure ha
  have hbH : b ∈ H := Subgroup.subset_closure hb
  let aH : H := ⟨a, haH⟩
  let bH : H := ⟨b, hbH⟩
  have haPK : szMk E aH ∈ (P : Subgroup (SzBar E)) := (mem_szS_iff.mp haP).2
  have hbPK : szMk E bH ∈ (P : Subgroup (SzBar E)) := (mem_szS_iff.mp hbP).2
  have haZ : szMk E aH ∈ sylowCenter (P : Subgroup (SzBar E)) :=
    c.mk_mem_sylowCenter P ha haPK
  have hbZ : szMk E bH ∈ sylowCenter (P : Subgroup (SzBar E)) :=
    c.mk_mem_sylowCenter P hb hbPK
  have haZ1 : szMk E aH ≠ 1 := szMk_ne_one c ha
  have hbZ1 : szMk E bH ≠ 1 := szMk_ne_one c hb
  have haZ' : szMk E aH ∈ (P : Subgroup (SzBar E)) ∧
      ∀ q ∈ (P : Subgroup (SzBar E)), Commute q (szMk E aH) := by
    have h := mem_sylowCenter.mp haZ
    exact ⟨h.1, fun q hq => h.2 q hq⟩
  have hbZ' : szMk E bH ∈ (P : Subgroup (SzBar E)) ∧
      ∀ q ∈ (P : Subgroup (SzBar E)), Commute q (szMk E bH) := by
    have h := mem_sylowCenter.mp hbZ
    exact ⟨h.1, fun q hq => h.2 q hq⟩
  obtain ⟨g, hgN, hgconj⟩ :=
    Asc72.IsBenderGroup.exists_normalizer_conj c.isBenderGroup P haZ' haZ1 hbZ' hbZ1
  obtain ⟨h, hhN, hhEq⟩ := exists_szN_of_mem_normalizer E P hgN
  have hb'E : (h : G) * a * (h : G)⁻¹ ∈ E := c.conj_mem h.2 ha
  have hb'H : (h : G) * a * (h : G)⁻¹ ∈ H :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ h.2 haH) (Subgroup.inv_mem _ h.2)
  let b' : G := (h : G) * a * (h : G)⁻¹
  have hb'img : szMk E ⟨b', hb'H⟩ = szMk E bH := by
    have hdec : (⟨b', hb'H⟩ : H) = h * aH * h⁻¹ := rfl
    rw [hdec, map_mul, map_mul, map_inv, hhEq, hgconj]
  have hq : b'⁻¹ * b ∈ szQ E := by
    have hprod : (⟨b'⁻¹ * b, H.mul_mem (H.inv_mem hb'H) hbH⟩ : H) =
        (⟨b', hb'H⟩ : H)⁻¹ * bH := rfl
    have himg : szMk E ⟨b'⁻¹ * b, H.mul_mem (H.inv_mem hb'H) hbH⟩ = 1 := by
      rw [hprod, map_mul, map_inv, hb'img]
      group
    exact (szMk_eq_one_iff_mem_szQ (H.mul_mem (H.inv_mem hb'H) hbH)).mp himg
  obtain ⟨y, hyQ, hyconj⟩ := c.exists_conj_of_inv_mul_mem hb'E hb hq
  have hyN : (y : G) ∈ szN E P := szS_le_szN E P (szQ_le_szS E P hyQ)
  have hhNG : (h : G) ∈ szN E P := hhN
  refine ⟨(y : G) * (h : G), Subgroup.mul_mem _ hyN hhNG, ?_⟩
  calc (y : G) * (h : G) * a * ((y : G) * (h : G))⁻¹
      = (y : G) * ((h : G) * a * (h : G)⁻¹) * (y : G)⁻¹ := by group
    _ = (y : G) * b' * (y : G)⁻¹ := by rfl
    _ = b := hyconj

private theorem conj_mem_szQ_of_mem_closure {g x : G}
    (hg : g ∈ Subgroup.closure E) (hx : x ∈ szQ E) : g * x * g⁻¹ ∈ szQ E := by
  let H : Subgroup G := Subgroup.closure E
  obtain ⟨hxH, hxQ⟩ := mem_szQ_iff.mp hx
  have hconjH : g * x * g⁻¹ ∈ H :=
    Subgroup.mul_mem _ (Subgroup.mul_mem _ hg hxH) (Subgroup.inv_mem _ hg)
  refine mem_szQ_iff.mpr ⟨hconjH, ?_⟩
  have hcalc : (⟨g * x * g⁻¹, hconjH⟩ : H) = ⟨g, hg⟩ * ⟨x, hxH⟩ * ⟨g, hg⟩⁻¹ := rfl
  rw [hcalc]
  exact (CFSG.pCore_normal (G := H) (p := 2)).conj_mem ⟨x, hxH⟩ hxQ ⟨g, hg⟩

private theorem generation_image_top (c : SzCfg G D d E e n) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) (hab : ¬ Commute a b) :
    ((Subgroup.closure (insert b (szComp E a))).subgroupOf
      (Subgroup.closure E)).map (szMk E) = ⊤ := by
  let H : Subgroup G := Subgroup.closure E
  let H0 : Subgroup G := Subgroup.closure (insert b (szComp E a))
  have haH : a ∈ H := Subgroup.subset_closure ha
  let aH : H := ⟨a, haH⟩
  let bH : H := ⟨b, Subgroup.subset_closure hb⟩
  obtain ⟨P, haP⟩ := c.exists_szS ha
  have haPK : szMk E aH ∈ (P : Subgroup (SzBar E)) := (mem_szS_iff.mp haP).2
  have hL2Sz : IsBenderL2Sz (SzBar E) := Or.inr ⟨n, c.one_le, c.iso_bar⟩
  have hbN : szMk E bH ∉ Subgroup.normalizer ((P : Subgroup (SzBar E)) : Set (SzBar E)) := by
    intro hbNorm
    have hb2 : szMk E bH * szMk E bH = 1 := szMk_mul_self_eq_one c hb
    have hbZ := CFSG.CGT.T75M.mem_center_of_mem_normalizer_sylow c.isBenderGroup P hbNorm hb2
    obtain ⟨z, hz, hzval⟩ := Subgroup.mem_map.mp hbZ
    have hzval' : (z : SzBar E) = szMk E bH := hzval
    have hzcomm : Commute (szMk E aH) (szMk E bH) := by
      have h := congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hz ⟨szMk E aH, haPK⟩)
      change szMk E aH * (z : SzBar E) = (z : SzBar E) * szMk E aH at h
      rw [hzval'] at h
      exact h
    have hcommH : Commute bH aH :=
      (c.commute_mk_iff (u := bH) (v := aH) hb ha).mp hzcomm.symm
    exact hab (((commute_coe_iff (H := H)).mpr hcommH).symm)
  have hgenK : sylowCenter (P : Subgroup (SzBar E)) ⊔
      Subgroup.zpowers (szMk E bH) = ⊤ :=
    sylowCenter_sup_zpowers_eq_top hL2Sz P hbN
  have hZle : sylowCenter (P : Subgroup (SzBar E)) ≤ (H0.subgroupOf H).map (szMk E) := by
    intro w hw
    by_cases hw1 : w = 1
    · rw [hw1]
      exact Subgroup.one_mem _
    · obtain ⟨b', hb'C, hb'H, hb'img⟩ :=
        c.exists_comp_of_mem_sylowCenter P ha haP hw hw1
      have hb'H0 : b' ∈ H0 := Subgroup.subset_closure (Or.inr hb'C)
      have hb'K : (⟨b', hb'H⟩ : H) ∈ H0.subgroupOf H := by
        rw [Subgroup.mem_subgroupOf]
        exact hb'H0
      rw [← hb'img]
      exact Subgroup.mem_map_of_mem (szMk E) hb'K
  have hzple : Subgroup.zpowers (szMk E bH) ≤ (H0.subgroupOf H).map (szMk E) := by
    have hbK : bH ∈ H0.subgroupOf H := by
      rw [Subgroup.mem_subgroupOf]
      exact Subgroup.subset_closure (Or.inl rfl)
    calc Subgroup.zpowers (szMk E bH) = (Subgroup.zpowers bH).map (szMk E) :=
          (MonoidHom.map_zpowers (szMk E) bH).symm
      _ ≤ (H0.subgroupOf H).map (szMk E) :=
          Subgroup.map_mono (Subgroup.zpowers_le.mpr hbK)
  rw [eq_top_iff, ← hgenK]
  exact sup_le hZle hzple

private theorem subset_closure_insert_comp (c : SzCfg G D d E e n) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) (hab : ¬ Commute a b) :
    E ⊆ Subgroup.closure (insert b (szComp E a)) := by
  let H : Subgroup G := Subgroup.closure E
  let H0 : Subgroup G := Subgroup.closure (insert b (szComp E a))
  have haH : a ∈ H := Subgroup.subset_closure ha
  have himg_top : (H0.subgroupOf H).map (szMk E) = ⊤ :=
    generation_image_top c ha hb hab
  intro e he
  obtain ⟨h, hh, hhae⟩ := c.exists_conj ha he
  have hmem : szMk E ⟨h, hh⟩ ∈ (H0.subgroupOf H).map (szMk E) := by
    rw [himg_top]
    exact Subgroup.mem_top _
  obtain ⟨k, hk_mem, hk_eq⟩ := Subgroup.mem_map.mp hmem
  have hk0H0 : (k : G) ∈ H0 := Subgroup.mem_subgroupOf.mp hk_mem
  have hkH : (k : G) ∈ H := k.2
  have hq1H : h * (k : G)⁻¹ ∈ H :=
    Subgroup.mul_mem _ hh (Subgroup.inv_mem _ hkH)
  have hq1 : h * (k : G)⁻¹ ∈ szQ E := by
    have hdec : (⟨h * (k : G)⁻¹, hq1H⟩ : H) = ⟨h, hh⟩ * k⁻¹ := rfl
    have himg : szMk E ⟨h * (k : G)⁻¹, hq1H⟩ = 1 := by
      rw [hdec, map_mul, map_inv, hk_eq]
      group
    exact (szMk_eq_one_iff_mem_szQ hq1H).mp himg
  have hkInvH : ((k : G)⁻¹) ∈ H := Subgroup.inv_mem _ hkH
  let q : G := (k : G)⁻¹ * (h * (k : G)⁻¹) * (k : G)
  have hq : q ∈ szQ E := by
    have := conj_mem_szQ_of_mem_closure hkInvH hq1
    simpa [q] using this
  have hqkH : q ∈ H := szQ_le_closure E hq
  have hq_eq : h = (k : G) * q := by
    dsimp [q]
    group
  have hc0E : q * a * q⁻¹ ∈ E := c.conj_mem hqkH ha
  have haInvH : a⁻¹ ∈ H := Subgroup.inv_mem _ haH
  have hqconj : a⁻¹ * q * a ∈ szQ E := by
    have := conj_mem_szQ_of_mem_closure haInvH hq
    simpa using this
  have hqcomp : q * a * q⁻¹ ∈ szComp E a := by
    refine ⟨hc0E, ?_⟩
    have hv : a⁻¹ * (q * a * q⁻¹) ∈ szQ E := by
      have heq : a⁻¹ * (q * a * q⁻¹) = (a⁻¹ * q * a) * q⁻¹ := by group
      rw [heq]
      exact Subgroup.mul_mem _ hqconj (Subgroup.inv_mem _ hq)
    exact (c.commute_of_inv_mul_mem (c.subset_commSet ha).1
      (c.subset_commSet hc0E).1 haH hv).symm
  have hc0H0 : q * a * q⁻¹ ∈ H0 := Subgroup.subset_closure (Or.inr hqcomp)
  have heq : e = (k : G) * (q * a * q⁻¹) * (k : G)⁻¹ := by
    rw [← hhae, hq_eq]
    group
  rw [heq]
  exact H0.mul_mem (H0.mul_mem hk0H0 hc0H0) (H0.inv_mem hk0H0)

theorem SzCfg.closure_insert_comp (c : SzCfg G D d E e n) {a b : G} (ha : a ∈ E)
    (hb : b ∈ E) (hab : ¬ Commute a b) :
    Subgroup.closure (insert b (szComp E a)) = Subgroup.closure E := by
  apply le_antisymm
  · rw [Subgroup.closure_le]
    intro x hx
    rcases hx with rfl | ⟨hxE, -⟩
    · exact Subgroup.subset_closure hb
    · exact Subgroup.subset_closure hxE
  · rw [Subgroup.closure_le]
    exact subset_closure_insert_comp c ha hb hab

theorem SzCfg.closure_insert_comp_top (c : SzCfg G D d E e n) {a b : ↥(Subgroup.closure E)}
    (ha : (a : G) ∈ E) (hb : (b : G) ∈ E) (hab : ¬ Commute a b) :
    Subgroup.closure (insert b {f | f ∈ szE E ∧ Commute f a}) = ⊤ := by
  let H : Subgroup G := Subgroup.closure E
  have hG := c.closure_insert_comp ha hb (fun h => hab ((commute_coe_iff (H := H)).mp h))
  have hset : ((↑) : H → G) '' (insert b {f | f ∈ szE E ∧ Commute f a}) =
      insert (b : G) (szComp E a) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      rcases hy with rfl | ⟨hyE, hycomm⟩
      · exact Or.inl rfl
      · exact Or.inr ⟨hyE, (commute_coe_iff (H := H)).mpr hycomm⟩
    · intro hx
      rcases hx with rfl | ⟨hxE, hxcomm⟩
      · exact ⟨b, Or.inl rfl, rfl⟩
      · exact ⟨⟨x, Subgroup.subset_closure hxE⟩,
          Or.inr ⟨hxE, (commute_coe_iff (H := H)).mp hxcomm⟩, rfl⟩
  have hmap : (Subgroup.closure (insert b {f | f ∈ szE E ∧ Commute f a})).map H.subtype = H := by
    rw [MonoidHom.map_closure]
    change Subgroup.closure (((↑) : H → G) '' insert b {f | f ∈ szE E ∧ Commute f a}) = H
    rw [hset, hG]
  have htopmap : (⊤ : Subgroup H).map H.subtype = H := by
    simpa using Subgroup.map_subgroupOf_eq_of_le (H := H) (K := H) le_rfl
  exact Subgroup.map_subtype_inj.mp (hmap.trans htopmap.symm)

end CFSG.Timmesfeld.Bridge.OddRoot
