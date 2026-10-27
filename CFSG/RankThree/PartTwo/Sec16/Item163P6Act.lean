module

public import CFSG.GroupTheory.PCore.QuotMulAut
public import CFSG.Open.LocalVocabulary
import CFSG.GroupTheory.PCore.OpenTransport
import CFSG.LieType.BorelTits.Basic

public section

namespace CFSG.RankThree.PartTwo.Sec16.Proof163P6

open CFSG
open scoped Pointwise

variable {G : Type} [Group G]

@[expose] noncomputable def actQ (Y : Subgroup G) :
    Subgroup.normalizer (Y : Set G) →* MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y) :=
  (CFSG.pCoreQuotMulAut ↥Y).comp Y.normalizerMonoidHom

theorem actQ_mk {Y : Subgroup G} (m : Subgroup.normalizer (Y : Set G)) (y : ↥Y) :
    actQ Y m (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y) =
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (Y.normalizerMonoidHom m y) :=
  rfl

theorem actQ_of_mem {Y : Subgroup G} (y : ↥Y) :
    actQ Y ⟨y, Y.le_normalizer y.2⟩ =
      MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y) := by
  refine MulEquiv.ext fun q => ?_
  induction q using QuotientGroup.induction_on with
  | H x =>
    change actQ Y ⟨y, Y.le_normalizer y.2⟩
        (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) x) =
      MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y)
        (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) x)
    rw [actQ_mk, MulAut.conj_apply, ← map_inv, ← map_mul, ← map_mul]
    congr 1

theorem mem_pCoreOf_of_actQ_eq_one {Y : Subgroup G}
    (hZ : Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥) {y : G} (hy : y ∈ Y)
    (h1 : actQ Y ⟨y, Subgroup.le_normalizer hy⟩ = 1) :
    y ∈ CFSG.Open.pCoreOf 2 Y := by
  have hconj : MulAut.conj (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨y, hy⟩) = 1 := by
    rw [← actQ_of_mem (Y := Y) ⟨y, hy⟩]
    exact h1
  have hc : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) ⟨y, hy⟩ ∈
      Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h := congrArg (fun φ : MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y) => φ z) hconj
    simp only [MulAut.conj_apply, MulAut.one_apply] at h
    rw [mul_inv_eq_iff_eq_mul] at h
    exact h.symm
  rw [hZ, Subgroup.mem_bot] at hc
  exact (CFSG.mem_openPCoreOf_iff ⟨y, hy⟩).mpr
    ((QuotientGroup.eq_one_iff (⟨y, hy⟩ : ↥Y)).mp (by simpa using hc))

private theorem eq_one_of_actQ_eq_one_of_mem {Y M : Subgroup G}
    (hZ : Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥) (hMY : M ≤ Y)
    (hM : M ⊓ CFSG.Open.pCoreOf 2 Y = ⊥) {m : G} (hmM : m ∈ M)
    (hm : actQ Y ⟨m, Subgroup.le_normalizer (hMY hmM)⟩ = 1) : m = 1 := by
  have hQ : m ∈ CFSG.Open.pCoreOf 2 Y :=
    mem_pCoreOf_of_actQ_eq_one hZ (hMY hmM) hm
  have hbot : m ∈ (⊥ : Subgroup G) := by
    rw [← hM]
    exact Subgroup.mem_inf.mpr ⟨hmM, hQ⟩
  simpa using hbot

theorem card_map_actQ_eq {Y M : Subgroup G}
    (hZ : Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥) (hMY : M ≤ Y)
    (hM : M ⊓ CFSG.Open.pCoreOf 2 Y = ⊥) :
    Nat.card ((M.subgroupOf (Subgroup.normalizer (Y : Set G))).map
      (actQ Y)) = Nat.card M := by
  set N := Subgroup.normalizer (Y : Set G) with hN
  set D := M.subgroupOf N with hD
  have hMN : M ≤ N := hMY.trans Subgroup.le_normalizer
  have hDM : Nat.card D = Nat.card M :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hMN).toEquiv
  have hker : ((actQ Y).subgroupMap D).ker = ⊥ := by
    rw [MonoidHom.ker_eq_bot_iff]
    intro a b hab
    have hg : (actQ Y).subgroupMap D (a⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    have h1 : actQ Y ((a⁻¹ * b : ↥D).1 : ↥N) = 1 := by
      have hval : ((a⁻¹ * b : ↥D).1 : ↥N) = a.1⁻¹ * b.1 := rfl
      rw [hval, map_mul, map_inv]
      have hab' : actQ Y a.1 = actQ Y b.1 := by
        simpa using congrArg (fun z : ↥(D.map (actQ Y)) =>
          (z : MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y))) hab
      rw [hab', inv_mul_cancel]
    have hmM : ((a⁻¹ * b : ↥D).1 : G) ∈ M :=
      Subgroup.mem_subgroupOf.mp (a⁻¹ * b).2
    have hmY : ((a⁻¹ * b : ↥D).1 : G) ∈ Y := hMY hmM
    have h1' : actQ Y ⟨((a⁻¹ * b : ↥D).1 : G), Subgroup.le_normalizer hmY⟩ = 1 := by
      rw [show (⟨((a⁻¹ * b : ↥D).1 : G), Subgroup.le_normalizer hmY⟩ : ↥N) =
          ((a⁻¹ * b : ↥D).1 : ↥N) from Subtype.ext rfl]
      exact h1
    have heq : ((a⁻¹ * b : ↥D).1 : G) = 1 :=
      eq_one_of_actQ_eq_one_of_mem hZ hMY hM hmM h1'
    have hab1 : a⁻¹ * b = 1 := by
      apply Subtype.ext
      apply Subtype.ext
      exact heq
    have hb : b = a := by
      calc b = a * (a⁻¹ * b) := by group
        _ = a * 1 := by rw [hab1]
        _ = a := mul_one a
    exact hb.symm
  have hcard := Subgroup.card_ker_mul_card_of_surjective
    ((actQ Y).subgroupMap_surjective D)
  rw [hker, Subgroup.card_bot, one_mul] at hcard
  exact hcard.trans hDM

theorem exists_actQ_eq_one_of_card_lt {Y R : Subgroup G}
    (hRY : R ≤ Subgroup.normalizer (Y : Set G))
    (hlt : Nat.card ((R.subgroupOf (Subgroup.normalizer (Y : Set G))).map
      (actQ Y)) < Nat.card R) :
    ∃ r ∈ R, r ≠ 1 ∧ ∃ hr : r ∈ Subgroup.normalizer (Y : Set G),
      actQ Y ⟨r, hr⟩ = 1 := by
  set N := Subgroup.normalizer (Y : Set G) with hN
  set D := R.subgroupOf N with hD
  have hDR : Nat.card D = Nat.card R :=
    Nat.card_congr (Subgroup.subgroupOfEquivOfLe hRY).toEquiv
  have hltD : Nat.card (D.map (actQ Y)) < Nat.card D := by rwa [← hDR] at hlt
  by_contra h
  have hinj : Function.Injective ((actQ Y).subgroupMap D) := by
    intro a b hab
    by_contra hne
    have hg : (actQ Y).subgroupMap D (a⁻¹ * b) = 1 := by
      rw [map_mul, map_inv, hab, inv_mul_cancel]
    have h1 : actQ Y ((a⁻¹ * b : ↥D).1 : ↥N) = 1 := by
      have hval : ((a⁻¹ * b : ↥D).1 : ↥N) = a.1⁻¹ * b.1 := rfl
      rw [hval, map_mul, map_inv]
      have hab' : actQ Y a.1 = actQ Y b.1 := by
        simpa using congrArg (fun z : ↥(D.map (actQ Y)) =>
          (z : MulAut (↥Y ⧸ CFSG.pCore 2 ↥Y))) hab
      rw [hab', inv_mul_cancel]
    set x : ↥D := a⁻¹ * b with hx
    have hxR : (x.1 : G) ∈ R := Subgroup.mem_subgroupOf.mp x.2
    have hxN : (x.1 : G) ∈ N := x.1.2
    have hx1 : (x.1 : G) ≠ 1 := by
      intro hzero
      apply hne
      have hxone : x = 1 := by
        apply Subtype.ext
        apply Subtype.ext
        exact hzero
      have hb : b = a := by
        calc b = a * (a⁻¹ * b) := by group
          _ = a * 1 := by rw [← hx, hxone]
          _ = a := mul_one a
      exact hb.symm
    have hxρ : actQ Y ⟨(x.1 : G), hxN⟩ = 1 := by
      have harg : (⟨(x.1 : G), hxN⟩ : ↥N) = ((a⁻¹ * b : ↥D).1 : ↥N) := by
        apply Subtype.ext
        exact congrArg (fun z : ↥D => (z.1 : G)) hx
      rw [harg]
      exact h1
    exact h ⟨(x.1 : G), hxR, hx1, hxN, hxρ⟩
  have hcard := Subgroup.card_ker_mul_card_of_surjective
    ((actQ Y).subgroupMap_surjective D)
  rw [MonoidHom.ker_eq_bot ((actQ Y).subgroupMap D) hinj, Subgroup.card_bot, one_mul] at hcard
  exact hltD.ne hcard

@[expose] noncomputable def kerActQ (Y : Subgroup G) : Subgroup G :=
  (actQ Y).ker.map (Subgroup.subtype (Subgroup.normalizer (Y : Set G)))

theorem mem_kerActQ_iff {Y : Subgroup G} {x : G} :
    x ∈ kerActQ Y ↔ ∃ hx : x ∈ Subgroup.normalizer (Y : Set G),
      actQ Y ⟨x, hx⟩ = 1 := by
  rw [kerActQ, Subgroup.mem_map]
  constructor
  · rintro ⟨n, hn, hnx⟩
    rw [← hnx]
    exact ⟨n.2, MonoidHom.mem_ker.mp hn⟩
  · rintro ⟨hx, hx1⟩
    exact ⟨⟨x, hx⟩, MonoidHom.mem_ker.mpr hx1, rfl⟩

private theorem le_normalizer_kerActQ (Y : Subgroup G) :
    Subgroup.normalizer (Y : Set G) ≤
      Subgroup.normalizer (kerActQ Y : Set G) := by
  set N := Subgroup.normalizer (Y : Set G) with hN
  have h := Subgroup.le_normalizer_map (H := (actQ Y).ker) (f := Subgroup.subtype N)
  have htop : Subgroup.normalizer ((actQ Y).ker : Set ↥N) = ⊤ := by
    rw [Subgroup.normalizer_eq_top_iff]
    infer_instance
  have hmap : (⊤ : Subgroup ↥N).map (Subgroup.subtype N) = N := by
    simpa using Subgroup.subgroupOf_map_subtype (⊤ : Subgroup G) N
  rw [htop, hmap] at h
  exact h

private theorem exists_pow_mem_of_mem_sup {R Y : Subgroup G} (hR2 : IsPGroup 2 R)
    (hRY : R ≤ Subgroup.normalizer (Y : Set G)) {x : G} (hx : x ∈ R ⊔ Y) :
    ∃ k : ℕ, x ^ 2 ^ k ∈ Y := by
  have hx' : x ∈ (R : Set G) * (Y : Set G) := by
    rw [← Subgroup.coe_mul_of_left_le_normalizer_right R Y hRY]
    exact hx
  obtain ⟨r, hr, y, hy, hxy⟩ := hx'
  obtain ⟨k, hk⟩ := hR2 ⟨r, hr⟩
  have hrk : r ^ 2 ^ k = 1 := by
    simpa using congrArg (fun z : ↥R => (z : G)) hk
  set N := Subgroup.normalizer (Y : Set G) with hN
  have hsupN : R ⊔ Y ≤ N := sup_le hRY Subgroup.le_normalizer
  have hxN : x ∈ N := hsupN hx
  have hrN : r ∈ N := hRY hr
  have hyN : y ∈ N := Subgroup.le_normalizer hy
  have hrNpow : (⟨r, hrN⟩ : ↥N) ^ 2 ^ k = 1 := by
    apply Subtype.ext
    simpa using hrk
  have hxyN : (⟨x, hxN⟩ : ↥N) = ⟨r, hrN⟩ * ⟨y, hyN⟩ := by
    apply Subtype.ext
    simpa using hxy.symm
  have hπy : QuotientGroup.mk' (Y.subgroupOf N) (⟨y, hyN⟩ : ↥N) = 1 := by
    simpa using (QuotientGroup.eq_one_iff (N := Y.subgroupOf N) (⟨y, hyN⟩ : ↥N)).mpr
      (show (⟨y, hyN⟩ : ↥N) ∈ Y.subgroupOf N from hy)
  refine ⟨k, ?_⟩
  have h1 : (⟨x, hxN⟩ : ↥N) ^ 2 ^ k ∈ Y.subgroupOf N := by
    rw [← QuotientGroup.eq_one_iff]
    calc QuotientGroup.mk' (Y.subgroupOf N) ((⟨x, hxN⟩ : ↥N) ^ 2 ^ k)
        = (QuotientGroup.mk' (Y.subgroupOf N) ⟨x, hxN⟩) ^ 2 ^ k := by rw [map_pow]
      _ = (QuotientGroup.mk' (Y.subgroupOf N) (⟨r, hrN⟩ * ⟨y, hyN⟩)) ^ 2 ^ k := by
            rw [hxyN]
      _ = ((QuotientGroup.mk' (Y.subgroupOf N) ⟨r, hrN⟩) *
            (QuotientGroup.mk' (Y.subgroupOf N) ⟨y, hyN⟩)) ^ 2 ^ k := by rw [map_mul]
      _ = (QuotientGroup.mk' (Y.subgroupOf N) ⟨r, hrN⟩) ^ 2 ^ k := by rw [hπy, mul_one]
      _ = QuotientGroup.mk' (Y.subgroupOf N) ((⟨r, hrN⟩ : ↥N) ^ 2 ^ k) := by
            rw [map_pow]
      _ = 1 := by rw [hrNpow, map_one]
  change x ^ 2 ^ k ∈ Y at h1
  exact h1

theorem isPGroup_inf_kerActQ {Y R L : Subgroup G} (hR2 : IsPGroup 2 R)
    (hRY : R ≤ Subgroup.normalizer (Y : Set G)) (hLY : L ≤ Y)
    (hZ : Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥) :
    IsPGroup 2 ↥((R ⊔ L) ⊓ kerActQ Y) := by
  intro x
  obtain ⟨hxH, hxK⟩ := Subgroup.mem_inf.mp x.2
  obtain ⟨hxN, hxact⟩ := (mem_kerActQ_iff (Y := Y)).mp hxK
  have hxRY : (x : G) ∈ R ⊔ Y := (sup_le_sup_left hLY R) hxH
  obtain ⟨k, hkY⟩ := exists_pow_mem_of_mem_sup hR2 hRY hxRY
  have hxpowact : actQ Y ⟨(x : G) ^ 2 ^ k, Subgroup.le_normalizer hkY⟩ = 1 := by
    have h1 : actQ Y ((⟨(x : G), hxN⟩ : ↥(Subgroup.normalizer (Y : Set G))) ^ 2 ^ k) = 1 := by
      rw [map_pow, hxact, one_pow]
    have h2 : (⟨(x : G), hxN⟩ : ↥(Subgroup.normalizer (Y : Set G))) ^ 2 ^ k =
        ⟨(x : G) ^ 2 ^ k, Subgroup.le_normalizer hkY⟩ := by
      apply Subtype.ext
      simp
    rwa [h2] at h1
  have hxpowQ : (x : G) ^ 2 ^ k ∈ CFSG.Open.pCoreOf 2 Y :=
    mem_pCoreOf_of_actQ_eq_one hZ hkY hxpowact
  have hQ2 : IsPGroup 2 ↥((CFSG.pCore 2 ↥Y).map Y.subtype) :=
    (CFSG.pCore_isPGroup (G := ↥Y) (p := 2)).map Y.subtype
  obtain ⟨j, hj⟩ := hQ2 ⟨(x : G) ^ 2 ^ k, hxpowQ⟩
  refine ⟨k + j, ?_⟩
  apply Subtype.ext
  calc (x : G) ^ 2 ^ (k + j) = ((x : G) ^ 2 ^ k) ^ 2 ^ j := by
        rw [pow_add, pow_mul]
    _ = 1 := by
        simpa using congrArg (fun z : ↥((CFSG.pCore 2 ↥Y).map Y.subtype) => (z : G)) hj

theorem pCoreOf_sup_ne_bot_of_actQ_eq_one {Y R L : Subgroup G} (hR2 : IsPGroup 2 R)
    (hRY : R ≤ Subgroup.normalizer (Y : Set G)) (hLY : L ≤ Y)
    (hZ : Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥) {r : G} (hr : r ∈ R) (hr1 : r ≠ 1)
    (hrN : r ∈ Subgroup.normalizer (Y : Set G))
    (hρ : actQ Y ⟨r, hrN⟩ = 1) :
    CFSG.Open.pCoreOf 2 (R ⊔ L) ≠ ⊥ := by
  let H : Subgroup G := R ⊔ L
  let K : Subgroup G := kerActQ Y
  let N : Subgroup G := H ⊓ K
  change CFSG.Open.pCoreOf 2 H ≠ ⊥
  have hHN : H ≤ Subgroup.normalizer (Y : Set G) :=
    sup_le hRY (hLY.trans Subgroup.le_normalizer)
  have hrH : r ∈ H := Subgroup.mem_sup_left hr
  have hrK : r ∈ K := (mem_kerActQ_iff (Y := Y)).mpr ⟨hrN, hρ⟩
  have hrN' : r ∈ N := Subgroup.mem_inf.mpr ⟨hrH, hrK⟩
  have hnorm : H ≤ Subgroup.normalizer (N : Set G) := by
    have hHK : H ≤ Subgroup.normalizer (K : Set G) :=
      hHN.trans (le_normalizer_kerActQ Y)
    intro h hh
    exact (Subgroup.inf_normalizer_le_normalizer_inf (H := H) (K := K))
      (Subgroup.mem_inf.mpr ⟨Subgroup.le_normalizer hh, hHK hh⟩)
  have hle : N ≤ CFSG.Open.pCoreOf 2 H :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left hnorm
      (isPGroup_inf_kerActQ hR2 hRY hLY hZ)
  intro hbot
  have hmem : r ∈ CFSG.Open.pCoreOf 2 H := hle hrN'
  rw [hbot] at hmem
  exact hr1 (by simpa using hmem)

@[expose] noncomputable def quotEquiv {Y L : Subgroup G} (hLY : L ≤ Y)
    (hY : Y = L ⊔ CFSG.Open.pCoreOf 2 Y) (hL : L ⊓ CFSG.Open.pCoreOf 2 Y = ⊥) :
    ↥L ≃* ↥Y ⧸ CFSG.pCore 2 ↥Y :=
  MulEquiv.ofBijective
    ((QuotientGroup.mk' (CFSG.pCore 2 ↥Y)).comp (Subgroup.inclusion hLY)) (by
    constructor
    · intro l1 l2 h
      have hdiv : Subgroup.inclusion hLY l1 / Subgroup.inclusion hLY l2 ∈
          CFSG.pCore 2 ↥Y :=
        (QuotientGroup.eq_iff_div_mem).mp h
      have hQ : ((Subgroup.inclusion hLY l1 / Subgroup.inclusion hLY l2 : ↥Y) : G) ∈
          CFSG.Open.pCoreOf 2 Y :=
        (CFSG.mem_openPCoreOf_iff _).mpr hdiv
      have hmem : (l1 : G) * (l2 : G)⁻¹ ∈ L ⊓ CFSG.Open.pCoreOf 2 Y := by
        refine Subgroup.mem_inf.mpr ⟨L.mul_mem l1.2 (L.inv_mem l2.2), ?_⟩
        simpa [div_eq_mul_inv] using hQ
      have h1 : (l1 : G) * (l2 : G)⁻¹ = 1 := by
        rw [hL] at hmem
        simpa using hmem
      exact Subtype.ext (mul_inv_eq_one.mp h1)
    · intro z
      obtain ⟨y, rfl⟩ := QuotientGroup.mk'_surjective (CFSG.pCore 2 ↥Y) z
      have hy' : (y : G) ∈ (L : Set G) * (CFSG.Open.pCoreOf 2 Y : Set G) := by
        rw [← Subgroup.coe_mul_of_left_le_normalizer_right L (CFSG.Open.pCoreOf 2 Y)
          (hLY.trans (CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y)), ← hY]
        exact y.2
      obtain ⟨l, hl, q, hq, hlq⟩ := hy'
      have hqY : q ∈ Y := CFSG.openPCoreOf_le 2 Y hq
      have hq1 : QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (⟨q, hqY⟩ : ↥Y) = 1 := by
        simpa using (QuotientGroup.eq_one_iff (N := CFSG.pCore 2 ↥Y)
          (⟨q, hqY⟩ : ↥Y)).mpr
          ((CFSG.mem_openPCoreOf_iff (p := 2) (⟨q, hqY⟩ : ↥Y)).mp (by simpa using hq))
      refine ⟨⟨l, hl⟩, ?_⟩
      show QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (Subgroup.inclusion hLY ⟨l, hl⟩) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y
      have hy : Subgroup.inclusion hLY ⟨l, hl⟩ * (⟨q, hqY⟩ : ↥Y) = y := Subtype.ext hlq
      rw [← hy, map_mul, hq1, mul_one])

theorem quotEquiv_apply {Y L : Subgroup G} (hLY : L ≤ Y)
    (hY : Y = L ⊔ CFSG.Open.pCoreOf 2 Y) (hL : L ⊓ CFSG.Open.pCoreOf 2 Y = ⊥)
    (l : ↥L) :
    quotEquiv hLY hY hL l =
      QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (Subgroup.inclusion hLY l) := rfl

@[expose] noncomputable def actL {Y L : Subgroup G} (hLY : L ≤ Y)
    (hY : Y = L ⊔ CFSG.Open.pCoreOf 2 Y) (hL : L ⊓ CFSG.Open.pCoreOf 2 Y = ⊥) :
    Subgroup.normalizer (Y : Set G) →* MulAut ↥L :=
  (MulAut.congr (quotEquiv hLY hY hL).symm).toMonoidHom.comp (actQ Y)

theorem actL_of_mem {Y L : Subgroup G} (hLY : L ≤ Y)
    (hY : Y = L ⊔ CFSG.Open.pCoreOf 2 Y) (hL : L ⊓ CFSG.Open.pCoreOf 2 Y = ⊥)
    {l : G} (hl : l ∈ L) :
    actL hLY hY hL ⟨l, Subgroup.le_normalizer (hLY hl)⟩ = MulAut.conj ⟨l, hl⟩ := by
  have h1 : actQ Y ⟨l, Subgroup.le_normalizer (hLY hl)⟩ =
      MulAut.conj (quotEquiv hLY hY hL ⟨l, hl⟩) := by
    rw [actQ_of_mem (Y := Y) ⟨l, hLY hl⟩]
    congr 1
  rw [actL, MonoidHom.comp_apply, h1]
  change MulAut.congr (quotEquiv hLY hY hL).symm
      (MulAut.conj (quotEquiv hLY hY hL ⟨l, hl⟩)) = MulAut.conj ⟨l, hl⟩
  ext x
  rw [MulAut.congr_apply]
  simp only [MulEquiv.trans_apply, MulEquiv.symm_apply_apply]
  rw [MulAut.conj_apply, MulAut.conj_apply]
  rw [show (quotEquiv hLY hY hL).symm.symm x = (quotEquiv hLY hY hL) x from rfl]
  rw [show (quotEquiv hLY hY hL ⟨l, hl⟩) * (quotEquiv hLY hY hL) x *
        (quotEquiv hLY hY hL ⟨l, hl⟩)⁻¹ =
      (quotEquiv hLY hY hL) (⟨l, hl⟩ * x * ⟨l, hl⟩⁻¹) by
    rw [map_mul, map_mul, map_inv]]
  rw [MulEquiv.symm_apply_apply]

theorem actL_eq_one_iff {Y L : Subgroup G} (hLY : L ≤ Y)
    (hY : Y = L ⊔ CFSG.Open.pCoreOf 2 Y) (hL : L ⊓ CFSG.Open.pCoreOf 2 Y = ⊥)
    (g : Subgroup.normalizer (Y : Set G)) :
    actL hLY hY hL g = 1 ↔ actQ Y g = 1 := by
  rw [actL, MonoidHom.comp_apply]
  exact (MulAut.congr (quotEquiv hLY hY hL).symm).map_eq_one_iff

theorem center_quot_eq_bot {Y L : Subgroup G} (hLY : L ≤ Y)
    (hY : Y = L ⊔ CFSG.Open.pCoreOf 2 Y) (hL : L ⊓ CFSG.Open.pCoreOf 2 Y = ⊥)
    (hZL : Subgroup.center ↥L = ⊥) :
    Subgroup.center (↥Y ⧸ CFSG.pCore 2 ↥Y) = ⊥ := by
  rw [← Subgroup.map_center_eq (quotEquiv hLY hY hL), hZL, Subgroup.map_bot]

end CFSG.RankThree.PartTwo.Sec16.Proof163P6

end
