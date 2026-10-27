module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneL227
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneLbar
import CFSG.Foundations.SteinbergCADefinitionNodes
import CFSG.GroupTheory.WielandtProductAux

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (K4a K4b)

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {D : Data G}

namespace Ctx82E3

noncomputable abbrev lbarAction (c : Ctx82E3 D) : ↥D.M →* MulAut c.Lbar :=
  CFSG.GroupTheory.conjModPCore 2 c.L D.M c.le_normalizer_L

abbrev lbarInn (c : Ctx82E3 D) : Subgroup (MulAut c.Lbar) :=
  (MulAut.conj : c.Lbar →* MulAut c.Lbar).range

theorem disjoint_map_ker_of_isPGroup (c : Ctx82E3 D)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {Q : Subgroup G} (hQM : Q ≤ D.M)
    (hQ : IsPGroup 3 Q) :
    Disjoint Q ((c.lbarAction).ker.map D.M.subtype) := by
  refine Subgroup.disjoint_of_coprime_natCard ?_
  obtain ⟨n, hn⟩ := hQ.exists_card_eq
  rw [hn]
  have h3' := not_three_dvd_card_map_ker c hZ
  exact Nat.Coprime.pow_left n
    ((Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).2 h3')

theorem eq_of_map_eq_of_isPGroup (c : Ctx82E3 D)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {Q : Subgroup G} (hQM : Q ≤ D.M)
    (hQ : IsPGroup 3 Q) {u v : G} (hu : u ∈ Q) (hv : v ∈ Q)
    (h : (c.lbarAction) ⟨u, hQM hu⟩ = (c.lbarAction) ⟨v, hQM hv⟩) : u = v := by
  have hdisj := disjoint_map_ker_of_isPGroup c hZ hQM hQ
  have hker : (⟨u, hQM hu⟩ * (⟨v, hQM hv⟩)⁻¹ : ↥D.M) ∈ (c.lbarAction).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv, h, mul_inv_cancel]
  have hmem : u * v⁻¹ ∈ Q ⊓ (c.lbarAction).ker.map D.M.subtype :=
    ⟨Q.mul_mem hu (Q.inv_mem hv), Subgroup.mem_map.mpr ⟨_, hker, rfl⟩⟩
  rw [hdisj.eq_bot, Subgroup.mem_bot] at hmem
  exact mul_inv_eq_one.mp hmem

theorem card_map_subgroupOf_of_isPGroup (c : Ctx82E3 D)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {Q : Subgroup G} (hQM : Q ≤ D.M)
    (hQ : IsPGroup 3 Q) :
    Nat.card ↥((Q.subgroupOf D.M).map c.lbarAction) = Nat.card Q := by
  classical
  let f : ↥Q →* MulAut c.Lbar := (c.lbarAction).comp (Subgroup.inclusion hQM)
  have hinj : Function.Injective f := by
    intro u v huv
    change (c.lbarAction) ((Subgroup.inclusion hQM) u) =
      (c.lbarAction) ((Subgroup.inclusion hQM) v) at huv
    have hcongr : (Subgroup.inclusion hQM) u = ⟨(u : G), hQM u.2⟩ :=
      Subtype.ext (Subgroup.coe_inclusion hQM u)
    have hcongr' : (Subgroup.inclusion hQM) v = ⟨(v : G), hQM v.2⟩ :=
      Subtype.ext (Subgroup.coe_inclusion hQM v)
    rw [hcongr, hcongr'] at huv
    exact Subtype.ext (eq_of_map_eq_of_isPGroup c hZ hQM hQ u.2 v.2 huv)
  have hrange : f.range = (Q.subgroupOf D.M).map c.lbarAction := by
    ext y
    constructor
    · rintro ⟨u, rfl⟩
      exact Subgroup.mem_map.mpr ⟨⟨u, hQM u.2⟩, Subgroup.mem_subgroupOf.mpr u.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  calc Nat.card ↥((Q.subgroupOf D.M).map c.lbarAction) = Nat.card ↥f.range := by rw [hrange]
    _ = Nat.card ↥Q := Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

theorem eq_one_of_map_eq_one_of_orderOf_eq_three (c : Ctx82E3 D)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {u : G} (huM : u ∈ D.M)
    (hu3 : orderOf u = 3) (h : (c.lbarAction) ⟨u, huM⟩ = 1) : u = 1 := by
  have hker : (⟨u, huM⟩ : ↥D.M) ∈ (c.lbarAction).ker := h
  have hle : Subgroup.zpowers u ≤ (c.lbarAction).ker.map D.M.subtype :=
    Subgroup.zpowers_le.mpr (Subgroup.mem_map.mpr ⟨⟨u, huM⟩, hker, rfl⟩)
  have h3 : Nat.card ↥(Subgroup.zpowers u) = 3 := by rw [Nat.card_zpowers, hu3]
  have hdvd : 3 ∣ Nat.card ((c.lbarAction).ker.map D.M.subtype) := by
    rw [← h3]
    exact Subgroup.card_dvd_of_le hle
  exact absurd hdvd (not_three_dvd_card_map_ker c hZ)

theorem map_zpowers_le_inn_of_mem_inn (c : Ctx82E3 D) {y : G} (hyM : y ∈ D.M)
    (hin : (c.lbarAction) ⟨y, hyM⟩ ∈ c.lbarInn) :
    ((Subgroup.zpowers y).subgroupOf D.M).map c.lbarAction ≤ c.lbarInn := by
  intro w hw
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hw
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (Subgroup.mem_subgroupOf.mp hu)
  have hu_eq : u = (⟨y, hyM⟩ : ↥D.M) ^ k := Subtype.ext (by simpa using hk.symm)
  rw [hu_eq, map_zpow]
  exact c.lbarInn.zpow_mem hin k

theorem lbarInn_le_range (c : Ctx82E3 D) : c.lbarInn ≤ (c.lbarAction).range := by
  rintro _ ⟨q, rfl⟩
  obtain ⟨l, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.Open.pCore 2 ↥c.L) q
  refine ⟨⟨(l : G), c.hyp81.1 l.2⟩, ?_⟩
  rw [CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 c.L D.M c.le_normalizer_L
    (c.hyp81.1 l.2) l.2, QuotientGroup.mk'_apply]

theorem three_dvd_relIndex_inn (c : Ctx82E3 D)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {P : Subgroup G} (hPM : P ≤ D.M)
    (hP : IsPGroup 3 P) {y : G} (hyP : y ∈ P) (hyL : y ∉ c.L) (hy3 : orderOf y = 3) :
    3 ∣ (c.lbarInn).relIndex (c.lbarAction).range := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  by_contra h3
  have hyM : y ∈ D.M := hPM hyP
  have hord0 : orderOf ((c.lbarAction) ⟨y, hyM⟩) ∣ 3 := by
    have h1 : orderOf ((c.lbarAction) ⟨y, hyM⟩) ∣ orderOf (⟨y, hyM⟩ : ↥D.M) :=
      orderOf_map_dvd _ _
    have h2 : orderOf (⟨y, hyM⟩ : ↥D.M) = 3 := by
      rw [← Subgroup.orderOf_coe, hy3]
    rwa [h2] at h1
  set x : ↥(c.lbarAction).range :=
    ⟨(c.lbarAction) ⟨y, hyM⟩, MonoidHom.mem_range.mpr ⟨⟨y, hyM⟩, rfl⟩⟩ with hx
  have hxval : (x : MulAut c.Lbar) = (c.lbarAction) ⟨y, hyM⟩ := rfl
  have hord : orderOf x ∣ 3 := by
    have h : orderOf x = orderOf ((c.lbarAction) ⟨y, hyM⟩) := by
      rw [← Subgroup.orderOf_coe x, hxval]
    rw [h]
    exact hord0
  have hin' : (x : MulAut c.Lbar) ∈ c.lbarInn := by
    haveI : (c.lbarInn.subgroupOf (c.lbarAction).range).Normal :=
      (Subgroup.normal_subgroupOf_iff (lbarInn_le_range c)).mpr
        (fun h k hh _ => Subgroup.Normal.conj_mem (inferInstance : c.lbarInn.Normal) h hh k)
    have hidx : (c.lbarInn.subgroupOf (c.lbarAction).range).index =
        (c.lbarInn).relIndex (c.lbarAction).range := by
      have h := Subgroup.relIndex_subgroupOf (G := MulAut c.Lbar) (H := c.lbarInn)
        (K := (c.lbarAction).range) (L := (c.lbarAction).range) le_rfl
      rwa [Subgroup.subgroupOf_self, Subgroup.relIndex_top_right] at h
    have hcop : Nat.Coprime (Nat.card ↥(Subgroup.zpowers x))
        (c.lbarInn.subgroupOf (c.lbarAction).range).index := by
      rw [hidx, Nat.card_zpowers]
      rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hord with h1 | h1
      · rw [h1]
        exact Nat.coprime_one_left _
      · rw [h1]
        exact (Nat.Prime.coprime_iff_not_dvd (by norm_num : Nat.Prime 3)).2 h3
    have hle : Subgroup.zpowers x ≤ c.lbarInn.subgroupOf (c.lbarAction).range :=
      CFSG.GroupTheory.WielandtProduct.le_of_coprime_index hcop
    exact Subgroup.mem_subgroupOf.mp (hle (Subgroup.mem_zpowers x))
  have hin : (c.lbarAction) ⟨y, hyM⟩ ∈ c.lbarInn := by
    rw [← hxval]
    exact hin'
  exact hyL (le_L_of_map_le_innAut c hZ (Subgroup.zpowers_le.mpr hyM)
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hy3]; norm_num))
    (map_zpowers_le_inn_of_mem_inn c hyM hin) (Subgroup.mem_zpowers y))

theorem eq_of_map_eq_of_mem_subgroupOf (c : Ctx82E3 D)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {Q : Subgroup G} (hQM : Q ≤ D.M)
    (hQ : IsPGroup 3 Q) {u v : ↥D.M} (hu : u ∈ Q.subgroupOf D.M)
    (hv : v ∈ Q.subgroupOf D.M) (h : (c.lbarAction) u = (c.lbarAction) v) : u = v := by
  have hu' : u = ⟨(u : G), hQM (Subgroup.mem_subgroupOf.mp hu)⟩ := Subtype.ext rfl
  have hv' : v = ⟨(v : G), hQM (Subgroup.mem_subgroupOf.mp hv)⟩ := Subtype.ext rfl
  rw [hu', hv'] at h
  exact Subtype.ext (eq_of_map_eq_of_isPGroup c hZ hQM hQ
    (Subgroup.mem_subgroupOf.mp hu) (Subgroup.mem_subgroupOf.mp hv) h)

theorem map_inf_L_eq_inf_inn (c : Ctx82E3 D)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {Q : Subgroup G} (hQM : Q ≤ D.M)
    (hQ : IsPGroup 3 Q) :
    ((Q ⊓ c.L).subgroupOf D.M).map c.lbarAction =
      (Q.subgroupOf D.M).map c.lbarAction ⊓ c.lbarInn := by
  ext y
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨huQ, huL⟩ := Subgroup.mem_subgroupOf.mp hu
    refine ⟨Subgroup.mem_map.mpr ⟨u, Subgroup.mem_subgroupOf.mpr huQ, rfl⟩, ?_⟩
    rw [CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 c.L D.M c.le_normalizer_L
      (c.hyp81.1 huL) huL]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  · rintro ⟨hyR, hyInn⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hyR
    have huQ : (u : G) ∈ Q := Subgroup.mem_subgroupOf.mp hu
    have hin : (c.lbarAction) u ∈ c.lbarInn := hyInn
    have hzmem : (u : G) ∈ c.L :=
      le_L_of_map_le_innAut c hZ (Subgroup.zpowers_le.mpr (hQM huQ))
        (hQ.to_le (Subgroup.zpowers_le.mpr huQ))
        (map_zpowers_le_inn_of_mem_inn c (hQM huQ) hin) (Subgroup.mem_zpowers _)
    exact Subgroup.mem_map.mpr ⟨u, Subgroup.mem_subgroupOf.mpr ⟨huQ, hzmem⟩, rfl⟩

theorem isSylowOf_map_range (c : Ctx82E3 D) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) :
    CFSG.ABGLocalTools.IsSylowOf 3 ((P.subgroupOf D.M).map c.lbarAction)
      (c.lbarAction).range := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  obtain ⟨Q, hQ⟩ := hP.exists_sylow_eq_subgroupOf
  refine ⟨Q.mapSurjective (MonoidHom.rangeRestrict_surjective c.lbarAction), ?_⟩
  rw [Sylow.coe_mapSurjective, Subgroup.map_map, hQ]
  rfl

theorem k4b_second (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4b : K4b)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {y : G} (hyP : y ∈ P) (hyL : y ∉ c.L)
    (hy3 : orderOf y = 3) :
    ∀ R : Subgroup (MulAut c.Lbar),
      CFSG.ABGLocalTools.IsSylowOf 3 R (c.lbarAction).range →
      Nat.card R = 81 ∧ CFSG.Open.IsElemAbelian 3 (R ⊓ c.lbarInn) ∧
      Nat.card ↥(R ⊓ c.lbarInn) = 27 ∧
      (∀ E : Subgroup (MulAut c.Lbar), E ≤ R → CFSG.Open.IsElemAbelian 3 E →
        Nat.card E = 27 → E = R ⊓ c.lbarInn) ∧
      (∃ z ∈ R, z ∉ c.lbarInn ∧ orderOf z = 3) ∧
      Nat.card ↥(R ⊓ Subgroup.centralizer (R : Set (MulAut c.Lbar))) = 3 ∧
      ∀ z ∈ R, z ∉ c.lbarInn → orderOf z = 3 →
        R ⊓ c.lbarInn ⊓ Subgroup.centralizer ({z} : Set (MulAut c.Lbar)) =
          R ⊓ Subgroup.centralizer (R : Set (MulAut c.Lbar)) ∧
        Nat.card ↥(R ⊓ Subgroup.centralizer ({z} : Set (MulAut c.Lbar))) = 9 ∧
        (∃ s ∈ R ⊓ c.lbarInn, ⁅z, ⁅z, s⁆⁆ ≠ 1) ∧
        (∀ x : MulAut c.Lbar, z⁻¹ * x ∈ R ⊓ c.lbarInn → orderOf x = 3 →
          ∃ s ∈ R ⊓ c.lbarInn, x = s * z * s⁻¹) ∧
        Nat.card {x : MulAut c.Lbar // z⁻¹ * x ∈ R ⊓ c.lbarInn ∧ orderOf x = 3} = 9 := by
  intro R hR
  have hqs : CFSG.IsQuasisimple c.Lbar :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff c.Lbar).2.2.1.mpr (isQuasisimple_lbar c h811)
  exact (hK4b c.Lbar hqs (odd_card_center_lbar c) h227).2 (c.lbarAction).range
    (lbarInn_le_range c)
    (three_dvd_relIndex_inn c hZ hP.le hP.isPGroup hyP hyL hy3) R hR

theorem card_eq_81_of_L227 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4b : K4b)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {y : G} (hyP : y ∈ P) (hyL : y ∉ c.L)
    (hy3 : orderOf y = 3) : Nat.card P = 81 := by
  have h := (k4b_second c h811 hK4b h227 hZ hP hyP hyL hy3 _
    (isSylowOf_map_range c hP)).1
  rw [← card_map_subgroupOf_of_isPGroup c hZ hP.le hP.isPGroup]
  exact h

theorem isElemAbelian_inf_L_of_L227 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4b : K4b)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {y : G} (hyP : y ∈ P) (hyL : y ∉ c.L)
    (hy3 : orderOf y = 3) : CFSG.Open.IsElemAbelian 3 (P ⊓ c.L) := by
  have hK := (k4b_second c h811 hK4b h227 hZ hP hyP hyL hy3 _
    (isSylowOf_map_range c hP)).2.1
  rw [← map_inf_L_eq_inf_inn c hZ hP.le hP.isPGroup] at hK
  let hSM : P ⊓ c.L ≤ D.M := inf_le_left.trans hP.le
  let f : ↥(P ⊓ c.L) →* MulAut c.Lbar := (c.lbarAction).comp (Subgroup.inclusion hSM)
  have hinj : Function.Injective f := by
    intro u v huv
    apply Subtype.ext
    exact eq_of_map_eq_of_isPGroup c hZ hP.le hP.isPGroup u.2.1 v.2.1 huv
  have hrange : f.range = ((P ⊓ c.L).subgroupOf D.M).map c.lbarAction := by
    ext w
    constructor
    · rintro ⟨u, rfl⟩
      exact Subgroup.mem_map.mpr ⟨Subgroup.inclusion hSM u,
        Subgroup.mem_subgroupOf.mpr u.2, rfl⟩
    · rintro ⟨x, hx, rfl⟩
      exact ⟨⟨(x : G), Subgroup.mem_subgroupOf.mp hx⟩, rfl⟩
  rw [← hrange] at hK
  have htop : CFSG.Open.IsElemAbelian 3 (⊤ : Subgroup ↥(P ⊓ c.L)) := by
    have h := hK.comap hinj
    rwa [show (f.range).comap f = ⊤ from by
      ext x
      simp [Subgroup.mem_comap]] at h
  have hfinal := htop.map (P ⊓ c.L).subtype
  simpa [Subgroup.map_top, Subgroup.range_subtype] using hfinal

theorem map_inf_centralizer_zpowers_eq (c : Ctx82E3 D)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {Q : Subgroup G} (hQM : Q ≤ D.M)
    (hQ : IsPGroup 3 Q) {x : G} (hx : x ∈ Q) :
    ((Q ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf D.M).map c.lbarAction =
      (Q.subgroupOf D.M).map c.lbarAction ⊓
        Subgroup.centralizer ({(c.lbarAction) ⟨x, hQM hx⟩} : Set (MulAut c.Lbar)) := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨huQ, hux⟩ := Subgroup.mem_subgroupOf.mp hu
    refine ⟨Subgroup.mem_map.mpr ⟨u, Subgroup.mem_subgroupOf.mpr huQ, rfl⟩, ?_⟩
    refine Subgroup.mem_centralizer_singleton_iff.mpr ?_
    have hcomm : x * (u : G) = (u : G) * x :=
      Subgroup.mem_centralizer_iff.mp hux x (Set.mem_singleton x)
    have hcommM : (⟨x, hQM hx⟩ : ↥D.M) * u = u * ⟨x, hQM hx⟩ := Subtype.ext hcomm
    have h := congrArg c.lbarAction hcommM
    simpa only [map_mul] using h.symm
  · rintro ⟨hwR, hwC⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hwR
    have huQ : (u : G) ∈ Q := Subgroup.mem_subgroupOf.mp hu
    have hcomm : (c.lbarAction) u * (c.lbarAction) ⟨x, hQM hx⟩ =
        (c.lbarAction) ⟨x, hQM hx⟩ * (c.lbarAction) u :=
      Subgroup.mem_centralizer_singleton_iff.mp hwC
    have hcommM : u * ⟨x, hQM hx⟩ = ⟨x, hQM hx⟩ * u := by
      refine eq_of_map_eq_of_mem_subgroupOf c hZ hQM hQ (Q.mul_mem huQ hx) (Q.mul_mem hx huQ) ?_
      rw [map_mul, map_mul]
      exact hcomm
    have hcommG : (u : G) * x = x * (u : G) := congrArg Subtype.val hcommM
    exact Subgroup.mem_map.mpr ⟨u, Subgroup.mem_subgroupOf.mpr
      ⟨huQ, Subgroup.mem_centralizer_iff.mpr (fun g hg => by
        rw [Set.mem_singleton_iff] at hg
        subst hg
        exact hcommG.symm)⟩, rfl⟩

theorem map_inf_centralizer_self_eq (c : Ctx82E3 D)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {Q : Subgroup G} (hQM : Q ≤ D.M)
    (hQ : IsPGroup 3 Q) :
    ((Q ⊓ Subgroup.centralizer (Q : Set G)).subgroupOf D.M).map c.lbarAction =
      (Q.subgroupOf D.M).map c.lbarAction ⊓
        Subgroup.centralizer ((Q.subgroupOf D.M).map c.lbarAction : Set (MulAut c.Lbar)) := by
  ext w
  constructor
  · rintro ⟨u, hu, rfl⟩
    obtain ⟨huQ, huC⟩ := Subgroup.mem_subgroupOf.mp hu
    refine ⟨Subgroup.mem_map.mpr ⟨u, Subgroup.mem_subgroupOf.mpr huQ, rfl⟩, ?_⟩
    refine Subgroup.mem_centralizer_iff.mpr ?_
    intro a ha
    obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp ha
    have hvQ : (v : G) ∈ Q := Subgroup.mem_subgroupOf.mp hv
    have hcomm : (v : G) * (u : G) = (u : G) * (v : G) :=
      Subgroup.mem_centralizer_iff.mp huC (v : G) hvQ
    have hcommM : v * u = u * v := Subtype.ext hcomm
    have h := congrArg c.lbarAction hcommM
    simpa only [map_mul] using h
  · rintro ⟨hwR, hwC⟩
    obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.mp hwR
    have huQ : (u : G) ∈ Q := Subgroup.mem_subgroupOf.mp hu
    have huC : (u : G) ∈ Subgroup.centralizer (Q : Set G) := by
      rw [Subgroup.mem_centralizer_iff]
      intro g hg
      have hgR : (c.lbarAction) ⟨g, hQM hg⟩ ∈ (Q.subgroupOf D.M).map c.lbarAction :=
        Subgroup.mem_map.mpr ⟨⟨g, hQM hg⟩, Subgroup.mem_subgroupOf.mpr hg, rfl⟩
      have hc : (c.lbarAction) ⟨g, hQM hg⟩ * (c.lbarAction) u =
          (c.lbarAction) u * (c.lbarAction) ⟨g, hQM hg⟩ :=
        Subgroup.mem_centralizer_iff.mp hwC _ hgR
      have hcM : (⟨g, hQM hg⟩ : ↥D.M) * u = u * ⟨g, hQM hg⟩ := by
        refine eq_of_map_eq_of_mem_subgroupOf c hZ hQM hQ (Q.mul_mem hg huQ) (Q.mul_mem huQ hg) ?_
        rw [map_mul, map_mul]
        exact hc
      exact congrArg Subtype.val hcM
    exact Subgroup.mem_map.mpr ⟨u, Subgroup.mem_subgroupOf.mpr ⟨huQ, huC⟩, rfl⟩

theorem eq_of_map_eq_of_le_isPGroup (c : Ctx82E3 D)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {Q A B : Subgroup G} (hQM : Q ≤ D.M)
    (hQ : IsPGroup 3 Q) (hAQ : A ≤ Q) (hBQ : B ≤ Q)
    (h : (A.subgroupOf D.M).map c.lbarAction = (B.subgroupOf D.M).map c.lbarAction) :
    A = B := by
  ext x
  constructor
  · intro hx
    have hxM : x ∈ D.M := hQM (hAQ hx)
    have hmem : (c.lbarAction) ⟨x, hxM⟩ ∈ (B.subgroupOf D.M).map c.lbarAction := by
      rw [← h]
      exact Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    obtain ⟨u, hu, hφu⟩ := Subgroup.mem_map.mp hmem
    have huB : (u : G) ∈ B := Subgroup.mem_subgroupOf.mp hu
    have huQ : (u : G) ∈ Q := hBQ huB
    have huQ' : u ∈ Q.subgroupOf D.M := Subgroup.subgroupOf_mono D.M hBQ hu
    have heq : (⟨x, hxM⟩ : ↥D.M) = u :=
      eq_of_map_eq_of_mem_subgroupOf c hZ hQM hQ (Subgroup.mem_subgroupOf.mpr (hAQ hx)) huQ'
        hφu.symm
    have hxB : x = (u : G) := congrArg Subtype.val heq
    rw [hxB]
    exact huB
  · intro hx
    have hxM : x ∈ D.M := hQM (hBQ hx)
    have hmem : (c.lbarAction) ⟨x, hxM⟩ ∈ (A.subgroupOf D.M).map c.lbarAction := by
      rw [h]
      exact Subgroup.mem_map.mpr ⟨⟨x, hxM⟩, Subgroup.mem_subgroupOf.mpr hx, rfl⟩
    obtain ⟨u, hu, hφu⟩ := Subgroup.mem_map.mp hmem
    have huA : (u : G) ∈ A := Subgroup.mem_subgroupOf.mp hu
    have huQ : (u : G) ∈ Q := hAQ huA
    have huQ' : u ∈ Q.subgroupOf D.M := Subgroup.subgroupOf_mono D.M hAQ hu
    have heq : (⟨x, hxM⟩ : ↥D.M) = u :=
      eq_of_map_eq_of_mem_subgroupOf c hZ hQM hQ (Subgroup.mem_subgroupOf.mpr (hBQ hx)) huQ'
        hφu.symm
    have hxB : x = (u : G) := congrArg Subtype.val heq
    rw [hxB]
    exact huA

theorem card_inf_L_eq_27_of_L227 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4b : K4b)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {y : G} (hyP : y ∈ P) (hyL : y ∉ c.L)
    (hy3 : orderOf y = 3) : Nat.card ↥(P ⊓ c.L) = 27 := by
  have h := (k4b_second c h811 hK4b h227 hZ hP hyP hyL hy3 _
    (isSylowOf_map_range c hP)).2.2.1
  rw [← map_inf_L_eq_inf_inn c hZ hP.le hP.isPGroup] at h
  rw [card_map_subgroupOf_of_isPGroup c hZ (inf_le_left.trans hP.le)
    (hP.isPGroup.to_le inf_le_left)] at h
  exact h

theorem unique_of_L227 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4b : K4b)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {y : G} (hyP : y ∈ P) (hyL : y ∉ c.L)
    (hy3 : orderOf y = 3) :
    ∀ E : Subgroup G, E ≤ P → CFSG.Open.IsElemAbelian 3 E → Nat.card E = 27 →
      E = P ⊓ c.L := by
  intro E hEP hEab hEcard
  have hEM : E ≤ D.M := hEP.trans hP.le
  have hE3 : IsPGroup 3 E := hEab.isPGroup
  have hR := (k4b_second c h811 hK4b h227 hZ hP hyP hyL hy3 _
    (isSylowOf_map_range c hP))
  have himg_le : (E.subgroupOf D.M).map c.lbarAction ≤ (P.subgroupOf D.M).map c.lbarAction :=
    Subgroup.map_mono (Subgroup.subgroupOf_mono D.M hEP)
  have himg_ab : CFSG.Open.IsElemAbelian 3 ((E.subgroupOf D.M).map c.lbarAction) :=
    (hEab.subgroupOf D.M).map c.lbarAction
  have himg_card : Nat.card ↥((E.subgroupOf D.M).map c.lbarAction) = 27 := by
    rw [card_map_subgroupOf_of_isPGroup c hZ hEM hE3]
    exact hEcard
  have hEq : (E.subgroupOf D.M).map c.lbarAction =
      (P.subgroupOf D.M).map c.lbarAction ⊓ c.lbarInn :=
    hR.2.2.2.1 _ himg_le himg_ab himg_card
  rw [← map_inf_L_eq_inf_inn c hZ hP.le hP.isPGroup] at hEq
  exact eq_of_map_eq_of_le_isPGroup c hZ hP.le hP.isPGroup hEP inf_le_left hEq

theorem card_inf_centralizer_self_of_L227 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4b : K4b)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {y : G} (hyP : y ∈ P) (hyL : y ∉ c.L)
    (hy3 : orderOf y = 3) : Nat.card ↥(P ⊓ Subgroup.centralizer (P : Set G)) = 3 := by
  have h := (k4b_second c h811 hK4b h227 hZ hP hyP hyL hy3 _
    (isSylowOf_map_range c hP)).2.2.2.2.2.1
  rw [← map_inf_centralizer_self_eq c hZ hP.le hP.isPGroup] at h
  rw [card_map_subgroupOf_of_isPGroup c hZ (inf_le_left.trans hP.le)
    (hP.isPGroup.to_le inf_le_left)] at h
  exact h

theorem exists_center_eq_zpowers_of_L227 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4b : K4b)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {y : G} (hyP : y ∈ P) (hyL : y ∉ c.L)
    (hy3 : orderOf y = 3) :
    ∃ z : G, P ⊓ Subgroup.centralizer (P : Set G) = Subgroup.zpowers z ∧ orderOf z = 3 := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hcard := card_inf_centralizer_self_of_L227 c h811 hK4b h227 hZ hP hyP hyL hy3
  have hdvd : 3 ∣ Nat.card ↥(P ⊓ Subgroup.centralizer (P : Set G)) := by rw [hcard]
  obtain ⟨zC, hzC⟩ :=
    exists_prime_orderOf_dvd_card' (G := ↥(P ⊓ Subgroup.centralizer (P : Set G))) 3 hdvd
  refine ⟨(zC : G), ?_, ?_⟩
  · have hmem : (zC : G) ∈ P ⊓ Subgroup.centralizer (P : Set G) := zC.2
    have hle : Subgroup.zpowers (zC : G) ≤ P ⊓ Subgroup.centralizer (P : Set G) :=
      Subgroup.zpowers_le.mpr hmem
    have hzc : Nat.card ↥(Subgroup.zpowers (zC : G)) = 3 := by
      rw [Nat.card_zpowers, Subgroup.orderOf_coe, hzC]
    exact (Subgroup.eq_of_le_of_card_ge hle (by rw [hcard, hzc])).symm
  · rw [Subgroup.orderOf_coe]
    exact hzC

theorem map_not_mem_inn_of_L227 (c : Ctx82E3 D)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {x : G} (hxP : x ∈ P) (hxL : x ∉ c.L)
    (hx3 : orderOf x = 3) : (c.lbarAction) ⟨x, hP.le hxP⟩ ∉ c.lbarInn := by
  intro hin
  exact hxL (le_L_of_map_le_innAut c hZ (Subgroup.zpowers_le.mpr (hP.le hxP))
    (IsPGroup.of_card (n := 1) (by rw [Nat.card_zpowers, hx3]; norm_num))
    (map_zpowers_le_inn_of_mem_inn c (hP.le hxP) hin) (Subgroup.mem_zpowers x))

theorem orderOf_map_of_L227 (c : Ctx82E3 D)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {x : G} (hxP : x ∈ P) (hxL : x ∉ c.L)
    (hx3 : orderOf x = 3) : orderOf ((c.lbarAction) ⟨x, hP.le hxP⟩) = 3 := by
  have hdvd : orderOf ((c.lbarAction) ⟨x, hP.le hxP⟩) ∣ 3 := by
    have h1 := orderOf_map_dvd (c.lbarAction) (⟨x, hP.le hxP⟩ : ↥D.M)
    have h2 : orderOf (⟨x, hP.le hxP⟩ : ↥D.M) = 3 := by
      rw [← Subgroup.orderOf_coe, hx3]
    rwa [h2] at h1
  have hne : orderOf ((c.lbarAction) ⟨x, hP.le hxP⟩) ≠ 1 := by
    intro h1
    have hx1 : x = 1 := eq_one_of_map_eq_one_of_orderOf_eq_three c hZ (hP.le hxP) hx3
      (orderOf_eq_one_iff.mp h1)
    rw [hx1] at hx3
    simp at hx3
  rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hdvd with h | h
  · exact absurd h hne
  · exact h

theorem center_le_L_of_L227 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4b : K4b)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {y : G} (hyP : y ∈ P) (hyL : y ∉ c.L)
    (hy3 : orderOf y = 3) {x : G} (hxP : x ∈ P) (hxL : x ∉ c.L) (hx3 : orderOf x = 3) :
    P ⊓ Subgroup.centralizer (P : Set G) ≤ c.L := by
  have hx'R : (c.lbarAction) ⟨x, hP.le hxP⟩ ∈ (P.subgroupOf D.M).map c.lbarAction :=
    Subgroup.mem_map.mpr ⟨⟨x, hP.le hxP⟩, Subgroup.mem_subgroupOf.mpr hxP, rfl⟩
  have hx'notInn := map_not_mem_inn_of_L227 c hZ hP hxP hxL hx3
  have hx'ord := orderOf_map_of_L227 c hZ hP hxP hxL hx3
  have hclause := ((k4b_second c h811 hK4b h227 hZ hP hyP hyL hy3 _
    (isSylowOf_map_range c hP)).2.2.2.2.2.2) _ hx'R hx'notInn hx'ord
  refine le_L_of_map_le_innAut c hZ (inf_le_left.trans hP.le) (hP.isPGroup.to_le inf_le_left) ?_
  rw [map_inf_centralizer_self_eq c hZ hP.le hP.isPGroup, ← hclause.1]
  exact inf_le_left.trans inf_le_right

theorem exists_conj_of_L227 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4b : K4b)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {y : G} (hyP : y ∈ P) (hyL : y ∉ c.L)
    (hy3 : orderOf y = 3) :
    ∀ x ∈ P, x ∉ c.L → orderOf x = 3 → ∀ w : G, x⁻¹ * w ∈ P ⊓ c.L → orderOf w = 3 →
      ∃ s ∈ P ⊓ c.L, w = s * x * s⁻¹ := by
  intro x hxP hxL hx3 w hwS hw3
  let xM : ↥D.M := ⟨x, hP.le hxP⟩
  have hwP : w ∈ P := by
    rw [show w = x * (x⁻¹ * w) by group]
    exact P.mul_mem hxP hwS.1
  have hwM : w ∈ D.M := hP.le hwP
  let wM : ↥D.M := ⟨w, hwM⟩
  have hx'R : (c.lbarAction) xM ∈ (P.subgroupOf D.M).map c.lbarAction :=
    Subgroup.mem_map.mpr ⟨xM, Subgroup.mem_subgroupOf.mpr hxP, rfl⟩
  have hx'notInn : (c.lbarAction) xM ∉ c.lbarInn :=
    map_not_mem_inn_of_L227 c hZ hP hxP hxL hx3
  have hx'ord : orderOf ((c.lbarAction) xM) = 3 :=
    orderOf_map_of_L227 c hZ hP hxP hxL hx3
  have hw3' : orderOf ((c.lbarAction) wM) = 3 := by
    have hdvd : orderOf ((c.lbarAction) wM) ∣ 3 := by
      have h1 := orderOf_map_dvd (c.lbarAction) wM
      have h2 : orderOf wM = 3 := by rw [← Subgroup.orderOf_coe, hw3]
      rwa [h2] at h1
    have hne : orderOf ((c.lbarAction) wM) ≠ 1 := by
      intro h1
      have hw1 : w = 1 := eq_one_of_map_eq_one_of_orderOf_eq_three c hZ hwM hw3
        (orderOf_eq_one_iff.mp h1)
      rw [hw1] at hw3
      simp at hw3
    rcases (Nat.dvd_prime (by norm_num : Nat.Prime 3)).1 hdvd with h | h
    · exact absurd h hne
    · exact h
  have hmemR : ((c.lbarAction) xM)⁻¹ * (c.lbarAction) wM ∈
      (P.subgroupOf D.M).map c.lbarAction := by
    rw [← map_inv, ← map_mul]
    exact Subgroup.mem_map.mpr ⟨xM⁻¹ * wM,
      Subgroup.mem_subgroupOf.mpr (by simpa using hwS.1), rfl⟩
  have hmemInn : ((c.lbarAction) xM)⁻¹ * (c.lbarAction) wM ∈ c.lbarInn := by
    rw [← map_inv, ← map_mul]
    have hval : (xM⁻¹ * wM : ↥D.M) = ⟨x⁻¹ * w, (inf_le_left.trans hP.le) hwS⟩ :=
      Subtype.ext rfl
    rw [hval, CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 c.L D.M c.le_normalizer_L
      ((inf_le_left.trans hP.le) hwS) hwS.2]
    exact MonoidHom.mem_range.mpr ⟨_, rfl⟩
  have hclause := ((k4b_second c h811 hK4b h227 hZ hP hyP hyL hy3 _
    (isSylowOf_map_range c hP)).2.2.2.2.2.2) _ hx'R hx'notInn hx'ord
  obtain ⟨sbar, hsbar, hsbar_eq⟩ := hclause.2.2.2.1 ((c.lbarAction) wM) ⟨hmemR, hmemInn⟩ hw3'
  have hsbarS : sbar ∈ ((P ⊓ c.L).subgroupOf D.M).map c.lbarAction := by
    rw [map_inf_L_eq_inf_inn c hZ hP.le hP.isPGroup]
    exact hsbar
  obtain ⟨sM, hsM, hφs⟩ := Subgroup.mem_map.mp hsbarS
  have hsP : (sM : G) ∈ P := (Subgroup.mem_subgroupOf.mp hsM).1
  have heq_aut : (c.lbarAction) wM = (c.lbarAction) (sM * xM * sM⁻¹) := by
    rw [map_mul, map_mul, map_inv, hφs]
    exact hsbar_eq
  have hmemS : sM * xM * sM⁻¹ ∈ P.subgroupOf D.M := by
    rw [Subgroup.mem_subgroupOf]
    simpa using P.mul_mem (P.mul_mem hsP hxP) (P.inv_mem hsP)
  have heqM : wM = sM * xM * sM⁻¹ :=
    eq_of_map_eq_of_mem_subgroupOf c hZ hP.le hP.isPGroup (Subgroup.mem_subgroupOf.mpr hwP)
      hmemS heq_aut
  exact ⟨(sM : G), Subgroup.mem_subgroupOf.mp hsM, by simpa using congrArg Subtype.val heqM⟩

theorem exists_conj_eq_mul_of_L227 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4b : K4b)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {y : G} (hyP : y ∈ P) (hyL : y ∉ c.L)
    (hy3 : orderOf y = 3) {z : G}
    (hzC : P ⊓ Subgroup.centralizer (P : Set G) = Subgroup.zpowers z) (hzord : orderOf z = 3)
    {x : G} (hxP : x ∈ P) (hxL : x ∉ c.L) (hx3 : orderOf x = 3) :
    ∃ s ∈ P ⊓ c.L, s * x * s⁻¹ = x * z ∨ s * x * s⁻¹ = x * z⁻¹ := by
  have hzmem : z ∈ P ⊓ Subgroup.centralizer (P : Set G) := by
    rw [hzC]
    exact Subgroup.mem_zpowers z
  have hzP : z ∈ P := hzmem.1
  have hzL : z ∈ c.L := center_le_L_of_L227 c h811 hK4b h227 hZ hP hyP hyL hy3 hxP hxL hx3 hzmem
  have hcomm : Commute x z := (Subgroup.mem_centralizer_iff.mp hzmem.2 x hxP)
  have hxzS : x⁻¹ * (x * z) ∈ P ⊓ c.L := by
    rw [show x⁻¹ * (x * z) = z by group]
    exact ⟨hzP, hzL⟩
  have hxz3 : orderOf (x * z) = 3 := by
    refine orderOf_eq_prime ?_ ?_
    · rw [hcomm.mul_pow]
      rw [show x ^ 3 = 1 from by rw [← hx3]; exact pow_orderOf_eq_one x,
        show z ^ 3 = 1 from by rw [← hzord]; exact pow_orderOf_eq_one z, mul_one]
    · intro h1
      have hxeq : x = z⁻¹ := mul_eq_one_iff_eq_inv.mp h1
      exact hxL (hxeq ▸ c.L.inv_mem hzL)
  obtain ⟨s, hs, hseq⟩ :=
    exists_conj_of_L227 c h811 hK4b h227 hZ hP hyP hyL hy3 x hxP hxL hx3 (x * z) hxzS hxz3
  exact ⟨s, hs, hseq.symm ▸ Or.inl rfl⟩

theorem inf_centralizer_eq_of_L227 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4b : K4b)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {y : G} (hyP : y ∈ P) (hyL : y ∉ c.L)
    (hy3 : orderOf y = 3) {z : G}
    (hzC : P ⊓ Subgroup.centralizer (P : Set G) = Subgroup.zpowers z)
    {x : G} (hxP : x ∈ P) (hxL : x ∉ c.L) (hx3 : orderOf x = 3) :
    P ⊓ c.L ⊓ Subgroup.centralizer ({x} : Set G) = Subgroup.zpowers z := by
  let xM : ↥D.M := ⟨x, hP.le hxP⟩
  have hQ : P ⊓ Subgroup.centralizer ({x} : Set G) ≤ D.M :=
    (inf_le_left.trans hP.le)
  have hQ3 : IsPGroup 3 ↥(P ⊓ Subgroup.centralizer ({x} : Set G)) :=
    hP.isPGroup.to_le inf_le_left
  have hmap1 : ((P ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf D.M).map c.lbarAction =
      (P.subgroupOf D.M).map c.lbarAction ⊓
        Subgroup.centralizer ({(c.lbarAction) xM} : Set (MulAut c.Lbar)) :=
    map_inf_centralizer_zpowers_eq c hZ hP.le hP.isPGroup hxP
  have hmap2 : ((P ⊓ c.L ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf D.M).map
        c.lbarAction =
      (((P ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf D.M).map c.lbarAction) ⊓
        c.lbarInn := by
    rw [show P ⊓ c.L ⊓ Subgroup.centralizer ({x} : Set G) =
      (P ⊓ Subgroup.centralizer ({x} : Set G)) ⊓ c.L from by ac_rfl]
    exact map_inf_L_eq_inf_inn c hZ hQ hQ3
  have hzmap : ((Subgroup.zpowers z).subgroupOf D.M).map c.lbarAction =
      (P.subgroupOf D.M).map c.lbarAction ⊓
        Subgroup.centralizer ((P.subgroupOf D.M).map c.lbarAction :
          Set (MulAut c.Lbar)) := by
    rw [← hzC]
    exact map_inf_centralizer_self_eq c hZ hP.le hP.isPGroup
  have hx'R : (c.lbarAction) xM ∈ (P.subgroupOf D.M).map c.lbarAction :=
    Subgroup.mem_map.mpr ⟨xM, Subgroup.mem_subgroupOf.mpr hxP, rfl⟩
  have hx'notInn : (c.lbarAction) xM ∉ c.lbarInn :=
    map_not_mem_inn_of_L227 c hZ hP hxP hxL hx3
  have hx'ord : orderOf ((c.lbarAction) xM) = 3 :=
    orderOf_map_of_L227 c hZ hP hxP hxL hx3
  have hclause := ((k4b_second c h811 hK4b h227 hZ hP hyP hyL hy3 _
    (isSylowOf_map_range c hP)).2.2.2.2.2.2) _ hx'R hx'notInn hx'ord
  have hzP : z ∈ P := by
    have hmem : z ∈ P ⊓ Subgroup.centralizer (P : Set G) := by
      rw [hzC]
      exact Subgroup.mem_zpowers z
    exact hmem.1
  have hle : P ⊓ c.L ⊓ Subgroup.centralizer ({x} : Set G) ≤ P := inf_le_left.trans inf_le_left
  refine eq_of_map_eq_of_le_isPGroup c hZ hP.le hP.isPGroup hle
    (Subgroup.zpowers_le.mpr hzP) ?_
  rw [hmap2, hmap1, hzmap]
  rw [show ((P.subgroupOf D.M).map c.lbarAction ⊓
      Subgroup.centralizer ({(c.lbarAction) xM} : Set (MulAut c.Lbar))) ⊓ c.lbarInn =
    (P.subgroupOf D.M).map c.lbarAction ⊓ c.lbarInn ⊓
      Subgroup.centralizer ({(c.lbarAction) xM} : Set (MulAut c.Lbar)) from by ac_rfl]
  rw [hclause.1]

theorem card_inf_centralizer_of_L227 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4b : K4b)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {y : G} (hyP : y ∈ P) (hyL : y ∉ c.L)
    (hy3 : orderOf y = 3) {x : G} (hxP : x ∈ P) (hxL : x ∉ c.L) (hx3 : orderOf x = 3) :
    Nat.card ↥(P ⊓ Subgroup.centralizer ({x} : Set G)) = 9 := by
  let xM : ↥D.M := ⟨x, hP.le hxP⟩
  have hx'R : (c.lbarAction) xM ∈ (P.subgroupOf D.M).map c.lbarAction :=
    Subgroup.mem_map.mpr ⟨xM, Subgroup.mem_subgroupOf.mpr hxP, rfl⟩
  have hx'notInn : (c.lbarAction) xM ∉ c.lbarInn :=
    map_not_mem_inn_of_L227 c hZ hP hxP hxL hx3
  have hx'ord : orderOf ((c.lbarAction) xM) = 3 :=
    orderOf_map_of_L227 c hZ hP hxP hxL hx3
  have h9 := (((k4b_second c h811 hK4b h227 hZ hP hyP hyL hy3 _
    (isSylowOf_map_range c hP)).2.2.2.2.2.2) _ hx'R hx'notInn hx'ord).2.1
  have hmap1 : ((P ⊓ Subgroup.centralizer ({x} : Set G)).subgroupOf D.M).map c.lbarAction =
      (P.subgroupOf D.M).map c.lbarAction ⊓
        Subgroup.centralizer ({(c.lbarAction) xM} : Set (MulAut c.Lbar)) :=
    map_inf_centralizer_zpowers_eq c hZ hP.le hP.isPGroup hxP
  rw [← hmap1] at h9
  rw [card_map_subgroupOf_of_isPGroup c hZ (inf_le_left.trans hP.le)
    (hP.isPGroup.to_le inf_le_left)] at h9
  exact h9

theorem mul_conj_not_mem_L_of_L227 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4a : K4a)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {y : G} (hyM : y ∈ D.M) (hyL : y ∉ c.L)
    (hy3 : orderOf y = 3) {m : G} (hm : m ∈ D.M) : y * (m * y * m⁻¹) ∉ c.L := by
  classical
  letI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  intro hmem
  set l : G := y * (m * y * m⁻¹) with hl
  have hlM : l ∈ D.M := c.hyp81.1 hmem
  have hEqM : (⟨m, hm⟩ * ⟨y, hyM⟩ * ⟨m, hm⟩⁻¹ : ↥D.M) = ⟨y, hyM⟩⁻¹ * ⟨l, hlM⟩ := by
    apply Subtype.ext
    show m * y * m⁻¹ = y⁻¹ * (y * (m * y * m⁻¹))
    group
  have hφeq : (c.lbarAction) ⟨m, hm⟩ * (c.lbarAction) ⟨y, hyM⟩ * ((c.lbarAction) ⟨m, hm⟩)⁻¹ =
      ((c.lbarAction) ⟨y, hyM⟩)⁻¹ * (c.lbarAction) ⟨l, hlM⟩ := by
    have h := congrArg (c.lbarAction) hEqM
    simpa only [map_mul, map_inv] using h
  have hqs : CFSG.IsQuasisimple c.Lbar :=
    (CFSG.Foundations.SteinbergCA.quasisimple_iff c.Lbar).2.2.1.mpr (isQuasisimple_lbar c h811)
  obtain ⟨-, -, hcomm, -⟩ := hK4a c.Lbar hqs (odd_card_center_lbar c) h227
  have hinner : (c.lbarAction) ⟨m, hm⟩ * (c.lbarAction) ⟨y, hyM⟩ *
      ((c.lbarAction) ⟨m, hm⟩)⁻¹ * ((c.lbarAction) ⟨y, hyM⟩)⁻¹ ∈ c.lbarInn := hcomm _ _
  rw [hφeq] at hinner
  have hφl : (c.lbarAction) ⟨l, hlM⟩ =
      MulAut.conj (QuotientGroup.mk (s := CFSG.Open.pCore 2 ↥c.L) ⟨l, hmem⟩) :=
    CFSG.GroupTheory.conjModPCore_apply_eq_conj_mk 2 c.L D.M c.le_normalizer_L hlM hmem
  have hlinner : (c.lbarAction) ⟨l, hlM⟩ ∈ c.lbarInn :=
    MonoidHom.mem_range.mpr ⟨_, hφl.symm⟩
  have hsq : ((c.lbarAction) ⟨y, hyM⟩) ^ 2 ∈ c.lbarInn := by
    have hconj : ((c.lbarAction) ⟨y, hyM⟩)⁻¹ * (c.lbarAction) ⟨l, hlM⟩ *
        (c.lbarAction) ⟨y, hyM⟩ ∈ c.lbarInn :=
      Subgroup.Normal.conj_mem (inferInstance : c.lbarInn.Normal) _ hlinner _
    have hprod := c.lbarInn.mul_mem (c.lbarInn.inv_mem hconj) hinner
    have hEq : (((c.lbarAction) ⟨y, hyM⟩)⁻¹ * (c.lbarAction) ⟨l, hlM⟩ *
          (c.lbarAction) ⟨y, hyM⟩)⁻¹ *
        (((c.lbarAction) ⟨y, hyM⟩)⁻¹ * (c.lbarAction) ⟨l, hlM⟩ *
          ((c.lbarAction) ⟨y, hyM⟩)⁻¹) = (((c.lbarAction) ⟨y, hyM⟩) ^ 2)⁻¹ := by
      group
    rw [hEq] at hprod
    exact c.lbarInn.inv_mem hprod
  have ha3 : (c.lbarAction) ⟨y, hyM⟩ ^ 3 = 1 := by
    rw [← map_pow]
    have h : (⟨y, hyM⟩ : ↥D.M) ^ 3 = 1 := by
      apply Subtype.ext
      show y ^ 3 = 1
      rw [← hy3]
      exact pow_orderOf_eq_one y
    rw [h, map_one]
  have hayinner : (c.lbarAction) ⟨y, hyM⟩ ∈ c.lbarInn := by
    have h4 : ((c.lbarAction) ⟨y, hyM⟩ ^ 2) ^ 2 = (c.lbarAction) ⟨y, hyM⟩ := by
      rw [← pow_mul, show 2 * 2 = 3 + 1 by norm_num, pow_add, ha3, one_mul, pow_one]
    rw [← h4]
    exact c.lbarInn.pow_mem hsq 2
  have hQ : IsPGroup 3 (Subgroup.zpowers y) := by
    refine IsPGroup.of_card (n := 1) ?_
    rw [Nat.card_zpowers, hy3]
    norm_num
  exact hyL (le_L_of_map_le_innAut c hZ (Subgroup.zpowers_le.mpr hyM) hQ
    (map_zpowers_le_inn_of_mem_inn c hyM hayinner) (Subgroup.mem_zpowers y))

theorem not_conj_inv_of_L227 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4a : K4a)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar)) {P : Subgroup G}
    (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {y : G} (hyP : y ∈ P) (hyL : y ∉ c.L)
    (hy3 : orderOf y = 3) :
    ∀ m ∈ D.M, y * (m * y * m⁻¹) ∉ P ⊓ c.L := by
  intro m hm hmem
  exact mul_conj_not_mem_L_of_L227 c h811 hK4a h227 hZ (hP.le hyP) hyL hy3 hm hmem.2

theorem exists_case811L227 (c : Ctx82E3 D)
    (h811 : CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L) (hK4a : K4a) (hK4b : K4b)
    (h227 : CFSG.Blueprint.LieModel (c.Lbar ⧸ Subgroup.center c.Lbar) .PSL 2 3 3)
    (hZ : ¬ 3 ∣ Nat.card (Subgroup.center c.Lbar))
    {P : Subgroup G} (hP : CFSG.ABGLocalTools.IsSylowOf 3 P D.M) {y : G}
    (hyP : y ∈ P) (hyL : y ∉ c.L) (hy3 : orderOf y = 3)
    (hN : ∀ Y : Subgroup G, Y ≤ P ⊓ c.L → Y ≠ ⊥ → Subgroup.normalizer (Y : Set G) ≤ D.M) :
    ∃ t : Case811L227 c, t.P = P ∧ t.y = y := by
  obtain ⟨z, hzC, hzord⟩ :=
    exists_center_eq_zpowers_of_L227 c h811 hK4b h227 hZ hP hyP hyL hy3
  refine ⟨?_, ?_, ?_⟩
  · exact
    { P := P,
      sylow := hP,
      card_P := card_eq_81_of_L227 c h811 hK4b h227 hZ hP hyP hyL hy3,
      elemAbelian_S := isElemAbelian_inf_L_of_L227 c h811 hK4b h227 hZ hP hyP hyL hy3,
      card_S := card_inf_L_eq_27_of_L227 c h811 hK4b h227 hZ hP hyP hyL hy3,
      unique := unique_of_L227 c h811 hK4b h227 hZ hP hyP hyL hy3,
      z := z,
      center_eq := hzC,
      orderOf_z := hzord,
      y := y,
      y_mem := hyP,
      y_not_mem_L := hyL,
      orderOf_y := hy3,
      inf_centralizer_eq := fun x hxP hxL hx3 =>
        inf_centralizer_eq_of_L227 c h811 hK4b h227 hZ hP hyP hyL hy3 hzC hxP hxL hx3,
      card_inf_centralizer := fun x hxP hxL hx3 =>
        card_inf_centralizer_of_L227 c h811 hK4b h227 hZ hP hyP hyL hy3 hxP hxL hx3,
      exists_conj_eq_mul := fun x hxP hxL hx3 =>
        exists_conj_eq_mul_of_L227 c h811 hK4b h227 hZ hP hyP hyL hy3 hzC hzord hxP hxL hx3,
      exists_conj := fun x hxP hxL hx3 w hw hw3 =>
        exists_conj_of_L227 c h811 hK4b h227 hZ hP hyP hyL hy3 x hxP hxL hx3 w hw hw3,
      normalizer_le := hN,
      not_conj_inv := fun m hm =>
        not_conj_inv_of_L227 c h811 hK4a h227 hZ hP hyP hyL hy3 m hm }
  · rfl
  · rfl

end Ctx82E3

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
