module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight65InversionG2
public import CFSG.RankThree.PartTwo.Sec12.Hering129HOrders

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open Subgroup
open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.AlgebraicGroups
open CFSG.AGLEmbedding.KFactProofs.G2Q
open scoped commutatorElement


variable {L : Type} [Field L]

@[expose] def tzPart (m : ℕ) : Subgroup (ModGL .G2 L) where
  carrier := {g | ∃ s t : Lˣ, s ^ m = 1 ∧ t ^ m = 1 ∧ g = tz s t}
  mul_mem' := by
    rintro _ _ ⟨s, t, hs, ht, rfl⟩ ⟨s', t', hs', ht', rfl⟩
    exact ⟨s * s', t * t', by rw [mul_pow, hs, hs', one_mul],
      by rw [mul_pow, ht, ht', one_mul], tz_mul s t s' t'⟩
  one_mem' := ⟨1, 1, one_pow _, one_pow _, tz_one_one.symm⟩
  inv_mem' := by
    rintro _ ⟨s, t, hs, ht, rfl⟩
    exact ⟨s⁻¹, t⁻¹, by rw [inv_pow, hs, inv_one], by rw [inv_pow, ht, inv_one], tz_inv s t⟩

theorem mem_tzPart {m : ℕ} {g : ModGL .G2 L} :
    g ∈ tzPart m ↔ ∃ s t : Lˣ, s ^ m = 1 ∧ t ^ m = 1 ∧ g = tz s t := Iff.rfl

theorem tz_mem_tzPart {m : ℕ} {s t : Lˣ} (hs : s ^ m = 1) (ht : t ^ m = 1) :
    (tz s t : ModGL .G2 L) ∈ tzPart m := ⟨s, t, hs, ht, rfl⟩

theorem tzPart_le_torusGroup (m : ℕ) : tzPart m ≤ torusGroup .G2 L := by
  rintro _ ⟨s, t, -, -, rfl⟩
  exact tz_mem_torusGroup s t

theorem card_tzPart (m : ℕ) (hm : m ≠ 0) {ζ : L} (hζ : IsPrimitiveRoot ζ m) :
    Nat.card (tzPart m : Subgroup (ModGL .G2 L)) = m ^ 2 := by
  haveI : NeZero m := ⟨hm⟩
  let f : (rootsOfUnity m L × rootsOfUnity m L) → (tzPart m : Subgroup (ModGL .G2 L)) :=
    fun p => ⟨tz p.1 p.2, ⟨p.1, p.2, p.1.2, p.2.2, rfl⟩⟩
  have hf_inj : Function.Injective f := by
    rintro ⟨⟨s, hs⟩, ⟨t, ht⟩⟩ ⟨⟨s', hs'⟩, ⟨t', ht'⟩⟩ h
    have hst : (tz s t : ModGL .G2 L) = tz s' t' := congrArg Subtype.val h
    obtain ⟨h1, h2⟩ := tz_injective hst
    exact Prod.ext (Subtype.ext h1) (Subtype.ext h2)
  have hf_surj : Function.Surjective f := by
    rintro ⟨g, s, t, hs, ht, hg⟩
    exact ⟨(⟨s, hs⟩, ⟨t, ht⟩), Subtype.ext hg.symm⟩
  have hcard : Nat.card (tzPart m : Subgroup (ModGL .G2 L)) =
      Nat.card (rootsOfUnity m L × rootsOfUnity m L) :=
    Nat.card_congr (Equiv.ofBijective f ⟨hf_inj, hf_surj⟩).symm
  rw [Nat.card_prod, IsPrimitiveRoot.card_rootsOfUnity hζ] at hcard
  simpa [pow_two] using hcard

theorem yq_not_mem_tzPart {m : ℕ} {g : Lˣ} (hg : g ≠ 1) :
    (yq : ModGL .G2 L) ∉ tzPart m := by
  intro h
  obtain ⟨s, t, -, -, hst⟩ := h
  exact yq_not_mem_torusGroup hg (hst ▸ tz_mem_torusGroup s t)

theorem yq_conj_mem_tzPart {m : ℕ} :
    ∀ x ∈ tzPart m, (yq : ModGL .G2 L) * x * yq⁻¹ ∈ tzPart m := by
  rintro _ ⟨s, u, hs, hu, rfl⟩
  refine ⟨s * (u ^ 3)⁻¹, s * (u ^ 2)⁻¹, ?_, ?_, yq_tz s u⟩
  · rw [mul_pow, hs, one_mul, inv_pow, ← pow_mul, mul_comm 3 m, pow_mul, hu, one_pow,
      inv_one]
  · rw [mul_pow, hs, one_mul, inv_pow, ← pow_mul, mul_comm 2 m, pow_mul, hu, one_pow,
      inv_one]

theorem ext3_tzPart {m : ℕ} {g : Lˣ} (hg : g ≠ 1) :
    Ext3 (tzPart (L := L) m) (yq : ModGL .G2 L) where
  pow_three := yq_pow_three
  normal := yq_conj_mem_tzPart (L := L)
  not_mem := yq_not_mem_tzPart (L := L) hg

theorem tz_fixed_by_yq {s t : Lˣ} (h : (yq : ModGL .G2 L) * tz s t * yq⁻¹ = tz s t) :
    s = 1 ∧ t ^ 3 = 1 := by
  rw [yq_tz] at h
  obtain ⟨h1, h2⟩ := tz_injective h
  have ht3 : t ^ 3 = 1 := by
    have h1' : (t ^ 3)⁻¹ = 1 := mul_eq_left.1 h1
    simpa using h1'
  refine ⟨?_, ht3⟩
  have ht2 : (t ^ 2)⁻¹ = t := by
    refine inv_eq_of_mul_eq_one_right ?_
    rw [← pow_succ, show 2 + 1 = 3 by norm_num, ht3]
  rw [ht2] at h2
  exact mul_eq_right.1 h2

theorem mem_zpowers_of_yq_fixed_tzPart {m : ℕ} (hm3 : 3 ∣ m) {ω : Lˣ} (hω3 : ω ^ 3 = 1)
    (hω : IsPrimitiveRoot (ω : L) 3) {x : ModGL .G2 L} (hx : x ∈ tzPart m)
    (hfix : (yq : ModGL .G2 L) * x * yq⁻¹ = x) : x ∈ Subgroup.zpowers (tz 1 ω) := by
  obtain ⟨s, t, hs, ht, rfl⟩ := hx
  obtain ⟨rfl, ht3⟩ := tz_fixed_by_yq hfix
  have htL : (t : L) ^ 3 = 1 := by simpa using congrArg (Units.val) ht3
  obtain ⟨j, -, hj⟩ := hω.eq_pow_of_pow_eq_one htL
  have htj : ω ^ j = t := Units.ext (by simpa using hj)
  have hpow : (tz 1 (ω ^ j) : ModGL .G2 L) = (tz 1 ω) ^ j := by
    simpa using (tz_pow 1 ω j).symm
  rw [← htj, hpow]
  exact Subgroup.pow_mem _ (Subgroup.mem_zpowers _) j

theorem fixed_tzPart_le_zpowers {m : ℕ} (hm3 : 3 ∣ m) {ω : Lˣ} (hω3 : ω ^ 3 = 1)
    (hω : IsPrimitiveRoot (ω : L) 3) :
    ∀ x ∈ tzPart m, (yq : ModGL .G2 L) * x * yq⁻¹ = x →
      x ∈ Subgroup.zpowers (tz 1 ω) :=
  fun _ hx hfix => mem_zpowers_of_yq_fixed_tzPart hm3 hω3 hω hx hfix

theorem yq_pow_conj_tz_one_ne {ω : Lˣ} (hω1 : ω ≠ 1) {k : ℕ} (hk0 : k ≠ 0) (hk : k < 3) :
    (yq : ModGL .G2 L) ^ k * tz ω 1 * ((yq : ModGL .G2 L) ^ k)⁻¹ ≠ tz ω 1 := by
  intro h
  have hyq3 : (yq : ModGL .G2 L) ^ 3 = 1 := yq_pow_three
  have h' : (yq : ModGL .G2 L) * tz ω 1 * yq⁻¹ = tz ω 1 := by
    interval_cases k
    · exact absurd rfl hk0
    · simpa using h
    · calc (yq : ModGL .G2 L) * tz ω 1 * yq⁻¹
          = yq * (yq ^ 2 * tz ω 1 * (yq ^ 2)⁻¹) * yq⁻¹ :=
              congrArg (fun z : ModGL .G2 L => yq * z * yq⁻¹) h.symm
        _ = yq ^ 3 * tz ω 1 * (yq ^ 3)⁻¹ := by group
        _ = tz ω 1 := by rw [hyq3]; group
  rw [yq_tz] at h'
  have h2 : ω = 1 := by
    simpa only [one_pow, inv_one, mul_one] using (tz_injective h').2
  exact hω1 h2


theorem center_extSub_tzPart_le {m : ℕ} (hm3 : 3 ∣ m) {ω : Lˣ} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (hω : IsPrimitiveRoot (ω : L) 3) :
    ∀ x : ↥(extSub (ext3_tzPart (L := L) (m := m) hω1)),
      x ∈ Subgroup.center ↥(extSub (ext3_tzPart (L := L) (m := m) hω1)) →
      (x : ModGL .G2 L) ∈ Subgroup.zpowers (tz 1 ω⁻¹) := by
  intro x hx
  obtain ⟨t, ht, k, hk, hxval⟩ :=
    (mem_extSub_iff_lt (ext3_tzPart (L := L) (m := m) hω1)).1 x.2
  have hcomm : (yq : ModGL .G2 L) * (t * yq ^ k) = (t * yq ^ k) * yq := by
    have h := congrArg Subtype.val
      (Subgroup.mem_center_iff.mp hx
        ⟨(yq : ModGL .G2 L), y_mem_extSub (ext3_tzPart (L := L) (m := m) hω1)⟩)
    simpa [hxval, mul_assoc] using h
  have htcomm : (yq : ModGL .G2 L) * t = t * yq := by
    have h' : ((yq : ModGL .G2 L) * t) * yq ^ k = (t * yq) * yq ^ k := by
      calc ((yq : ModGL .G2 L) * t) * yq ^ k = yq * (t * yq ^ k) := by group
        _ = (t * yq ^ k) * yq := hcomm
        _ = (t * yq) * yq ^ k := by group
    exact mul_right_cancel h'
  have hfix : (yq : ModGL .G2 L) * t * yq⁻¹ = t := by rw [htcomm]; group
  have hωm : (ω : Lˣ) ^ m = 1 := by
    obtain ⟨c, hc⟩ := hm3
    rw [hc, pow_mul, hω3, one_pow]
  have hv : (tz ω 1 : ModGL .G2 L) ∈
      extSub (ext3_tzPart (L := L) (m := m) hω1) :=
    le_extSub _ (tz_mem_tzPart (m := m) (by simpa using hωm) (by simp))
  have hk0 : k = 0 := by
    by_contra hkne
    have hcentv : (tz ω 1 : ModGL .G2 L) * (x : ModGL .G2 L) =
        (x : ModGL .G2 L) * tz ω 1 :=
      congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hx ⟨(tz ω 1 : ModGL .G2 L), hv⟩)
    obtain ⟨s, u, hs, hu, hst⟩ := ht
    rw [hst] at hfix
    obtain ⟨hs1, hu3⟩ := tz_fixed_by_yq hfix
    rw [hxval, hst, hs1] at hcentv
    have hstep : (tz ω 1 : ModGL .G2 L) * yq ^ k = yq ^ k * tz ω 1 := by
      have h' : (tz 1 u : ModGL .G2 L) * ((tz ω 1) * yq ^ k) =
          (tz 1 u) * (yq ^ k * tz ω 1) := by
        calc (tz 1 u : ModGL .G2 L) * ((tz ω 1) * yq ^ k)
            = ((tz 1 u) * tz ω 1) * yq ^ k := by group
          _ = ((tz ω 1) * tz 1 u) * yq ^ k := by rw [tz_mul_comm]
          _ = (tz ω 1) * (tz 1 u * yq ^ k) := by group
          _ = (tz 1 u * yq ^ k) * tz ω 1 := hcentv
          _ = (tz 1 u) * (yq ^ k * tz ω 1) := by group
      exact mul_left_cancel h'
    have hconj : (yq : ModGL .G2 L) ^ k * tz ω 1 * ((yq : ModGL .G2 L) ^ k)⁻¹ =
        tz ω 1 := by
      rw [← hstep]; group
    exact yq_pow_conj_tz_one_ne hω1 hkne hk hconj
  have hzp : Subgroup.zpowers (tz 1 ω) = Subgroup.zpowers (tz 1 ω⁻¹) := by
    rw [show (tz 1 ω⁻¹ : ModGL .G2 L) = (tz 1 ω)⁻¹ from (tz_inv 1 ω).symm,
      Subgroup.zpowers_inv]
  have hmem : t ∈ Subgroup.zpowers (tz 1 ω) :=
    mem_zpowers_of_yq_fixed_tzPart hm3 hω3 hω ht hfix
  rw [hzp] at hmem
  rw [hxval, hk0, pow_zero, mul_one]
  exact hmem

theorem mem_center_extSub_tzPart_iff {m : ℕ} (hm3 : 3 ∣ m) {ω : Lˣ} (hω3 : ω ^ 3 = 1)
    (hω1 : ω ≠ 1) (hω : IsPrimitiveRoot (ω : L) 3)
    (x : ↥(extSub (ext3_tzPart (L := L) (m := m) hω1))) :
    x ∈ Subgroup.center ↥(extSub (ext3_tzPart (L := L) (m := m) hω1)) ↔
      (x : ModGL .G2 L) ∈ Subgroup.zpowers (tz 1 ω⁻¹) := by
  constructor
  · exact center_extSub_tzPart_le hm3 hω3 hω1 hω x
  · intro hx
    have hωinv3 : (ω⁻¹) ^ 3 = 1 := by rw [inv_pow, hω3, inv_one]
    have hωinvm : (ω⁻¹ : Lˣ) ^ m = 1 := by
      obtain ⟨c, hc⟩ := hm3
      rw [hc, pow_mul, hωinv3, one_pow]
    have hmem : (tz 1 ω⁻¹ : ModGL .G2 L) ∈
        extSub (ext3_tzPart (L := L) (m := m) hω1) :=
      le_extSub _ (tz_mem_tzPart (m := m) (by simp) hωinvm)
    have hcomm_yq : (tz 1 ω⁻¹ : ModGL .G2 L) * yq = yq * tz 1 ω⁻¹ := by
      have h := yq_fix_tz_center ω hω3
      calc (tz 1 ω⁻¹ : ModGL .G2 L) * yq = (yq * tz 1 ω⁻¹ * yq⁻¹) * yq := by
            rw [h]
        _ = yq * tz 1 ω⁻¹ := by group
    have hcomm_yqpow : ∀ j : ℕ, (yq : ModGL .G2 L) ^ j * tz 1 ω⁻¹ =
        tz 1 ω⁻¹ * yq ^ j := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc (yq : ModGL .G2 L) ^ (j + 1) * tz 1 ω⁻¹
            = (yq ^ j * yq) * tz 1 ω⁻¹ := by rw [pow_succ]
          _ = yq ^ j * (yq * tz 1 ω⁻¹) := by group
          _ = yq ^ j * (tz 1 ω⁻¹ * yq) := by rw [← hcomm_yq]
          _ = (yq ^ j * tz 1 ω⁻¹) * yq := by group
          _ = (tz 1 ω⁻¹ * yq ^ j) * yq := by rw [ih]
          _ = tz 1 ω⁻¹ * (yq ^ j * yq) := by group
          _ = tz 1 ω⁻¹ * yq ^ (j + 1) := by rw [pow_succ]
    have hz0_comm : ∀ y : ↥(extSub (ext3_tzPart (L := L) (m := m) hω1)),
        (y : ModGL .G2 L) * tz 1 ω⁻¹ = tz 1 ω⁻¹ * (y : ModGL .G2 L) := by
      intro y
      obtain ⟨t, ht, j, hj, hyval⟩ :=
        (mem_extSub_iff_lt (ext3_tzPart (L := L) (m := m) hω1)).1 y.2
      obtain ⟨s, u, hs, hu, hst⟩ := ht
      rw [hyval, hst]
      calc (tz s u * yq ^ j : ModGL .G2 L) * tz 1 ω⁻¹
          = tz s u * (yq ^ j * tz 1 ω⁻¹) := by group
        _ = tz s u * (tz 1 ω⁻¹ * yq ^ j) := by rw [hcomm_yqpow]
        _ = (tz s u * tz 1 ω⁻¹) * yq ^ j := by group
        _ = (tz 1 ω⁻¹ * tz s u) * yq ^ j := by rw [tz_mul_comm]
        _ = tz 1 ω⁻¹ * (tz s u * yq ^ j) := by group
    have hz0c : (⟨tz 1 ω⁻¹, hmem⟩ : ↥(extSub (ext3_tzPart (L := L) (m := m) hω1))) ∈
        Subgroup.center ↥(extSub (ext3_tzPart (L := L) (m := m) hω1)) := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      change (y : ModGL .G2 L) * tz 1 ω⁻¹ = tz 1 ω⁻¹ * (y : ModGL .G2 L)
      exact hz0_comm y
    obtain ⟨n, hn⟩ := Subgroup.mem_zpowers_iff.mp hx
    have hxeq : x = (⟨tz 1 ω⁻¹, hmem⟩ :
        ↥(extSub (ext3_tzPart (L := L) (m := m) hω1))) ^ n := by
      apply Subtype.ext
      simpa using hn.symm
    rw [hxeq]
    exact Subgroup.zpow_mem (K := Subgroup.center ↥(extSub (ext3_tzPart (L := L) (m := m) hω1))) hz0c n


theorem sylow_center_inversion_transport
    {G : Type} [Group G] [Finite G]
    (S : Subgroup G) (hSsyl : ∃ P : Sylow 3 G, (P : Subgroup G) = S)
    (z : ↥S) (hzcenter : Subgroup.center ↥S = Subgroup.zpowers z)
    (t : G) (ht2 : orderOf t = 2)
    (htinv : t * (z : G) * t⁻¹ = (z : G)⁻¹) :
    ∀ (Q : Sylow 3 G) (w : G),
      w ∈ (Q : Subgroup G) → w ∈ Subgroup.centralizer ((Q : Subgroup G) : Set G) →
      orderOf w = 3 → ∃ u : G, orderOf u = 2 ∧ u * w * u⁻¹ = w⁻¹ := by
  classical
  obtain ⟨SylS, hSylS⟩ := hSsyl
  intro Q w hwQ hwc hw3
  obtain ⟨g, hg⟩ := MulAction.exists_smul_eq G SylS Q
  have hQ : (Q : Subgroup G) = S.map (MulAut.conj g).toMonoidHom := by
    rw [← hg, Sylow.coe_subgroup_smul, Subgroup.pointwise_smul_def, hSylS]
    ext x
    constructor <;> rintro ⟨y, hy, rfl⟩ <;> exact ⟨y, hy, rfl⟩
  let w' : G := g⁻¹ * w * g
  have hwS : w ∈ S.map (MulAut.conj g).toMonoidHom := by
    rw [hQ] at hwQ
    exact hwQ
  obtain ⟨s, hs, hsw⟩ := Subgroup.mem_map.mp hwS
  have hw'S : w' ∈ S := by
    have hw'eq : w' = s := by
      dsimp [w']
      rw [← hsw]
      change g⁻¹ * (g * s * g⁻¹) * g = s
      group
    rwa [hw'eq]
  let wS : ↥S := ⟨w', hw'S⟩
  have hw'center : wS ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro s
    apply Subtype.ext
    have hgs : g * (s : G) * g⁻¹ ∈ (Q : Subgroup G) := by
      rw [hQ]
      exact Subgroup.mem_map_of_mem (MulAut.conj g).toMonoidHom s.2
    have hcomm := Subgroup.mem_centralizer_iff.mp hwc (g * (s : G) * g⁻¹) hgs
    have hconj : g * ((s : G) * w') * g⁻¹ = g * (w' * (s : G)) * g⁻¹ := by
      calc g * ((s : G) * w') * g⁻¹ = (g * (s : G) * g⁻¹) * w := by
            dsimp [w']
            group
        _ = w * (g * (s : G) * g⁻¹) := hcomm
        _ = g * (w' * (s : G)) * g⁻¹ := by
            dsimp [w']
            group
    exact (MulAut.conj g).injective hconj
  obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp (by rw [← hzcenter]; exact hw'center)
  have hwk : w' = (z : G) ^ k := by
    have h := congrArg Subtype.val hk
    simpa [wS] using h.symm
  have hw'inv : t * w' * t⁻¹ = w'⁻¹ := by
    rw [hwk]
    calc t * z ^ k * t⁻¹ = (t * z * t⁻¹) ^ k := by rw [conj_zpow]
      _ = (z⁻¹) ^ k := by rw [htinv]; simp
      _ = (z ^ k)⁻¹ := by simp
  refine ⟨g * t * g⁻¹, ?_, ?_⟩
  · change orderOf ((MulAut.conj g) t) = 2
    exact ((MulAut.conj g).orderOf_eq t).trans ht2
  · calc (g * t * g⁻¹) * w * (g * t * g⁻¹)⁻¹ = g * (t * w' * t⁻¹) * g⁻¹ := by
          dsimp [w']
          group
      _ = g * w'⁻¹ * g⁻¹ := by rw [hw'inv]
      _ = w⁻¹ := by
          dsimp [w']
          group


theorem padicValNat_three_sq_sub_one_of_mod_one {q : ℕ} (hq : 3 ≤ q) (hmod : q % 3 = 1) :
    padicValNat 3 (q ^ 2 - 1) = padicValNat 3 (q - 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq1 : q - 1 ≠ 0 := by omega
  have hq1' : q + 1 ≠ 0 := by omega
  have h3q1 : ¬ 3 ∣ q + 1 := by
    intro h
    have : (q + 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    omega
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rw [pow_two, mul_self_tsub_one]
    ring
  rw [hfac, padicValNat.mul hq1 hq1',
    padicValNat.eq_zero_of_not_dvd h3q1, add_zero]

theorem padicValNat_three_sq_sub_one_of_mod_two {q : ℕ} (hq : 3 ≤ q) (hmod : q % 3 = 2) :
    padicValNat 3 (q ^ 2 - 1) = padicValNat 3 (q + 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq1 : q - 1 ≠ 0 := by omega
  have hq1' : q + 1 ≠ 0 := by omega
  have h3q1 : ¬ 3 ∣ q - 1 := by
    intro h
    have : (q - 1) % 3 = 0 := Nat.mod_eq_zero_of_dvd h
    omega
  have hfac : q ^ 2 - 1 = (q - 1) * (q + 1) := by
    rw [pow_two, mul_self_tsub_one]
    ring
  rw [hfac, padicValNat.mul hq1 hq1',
    padicValNat.eq_zero_of_not_dvd h3q1, zero_add]

theorem pow_padicValNat_three_sq_sub_one_dvd_of_mod_one {q : ℕ} (hq : 3 ≤ q)
    (hmod : q % 3 = 1) :
    3 ^ padicValNat 3 (q ^ 2 - 1) ∣ q - 1 := by
  rw [padicValNat_three_sq_sub_one_of_mod_one hq hmod]
  exact pow_padicValNat_dvd (p := 3) (n := q - 1)

theorem pow_padicValNat_three_sq_sub_one_dvd_of_mod_two {q : ℕ} (hq : 3 ≤ q)
    (hmod : q % 3 = 2) :
    3 ^ padicValNat 3 (q ^ 2 - 1) ∣ q + 1 := by
  rw [padicValNat_three_sq_sub_one_of_mod_two hq hmod]
  exact pow_padicValNat_dvd (p := 3) (n := q + 1)

theorem one_le_padicValNat_three_sq_sub_one {q : ℕ} (h3 : ¬ 3 ∣ q) (hq : 2 ≤ q) :
    1 ≤ padicValNat 3 (q ^ 2 - 1) := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hq1 : q ^ 2 - 1 ≠ 0 := by
    have : 1 < q ^ 2 := Nat.one_lt_pow (by norm_num) (by omega)
    omega
  have hdvd : 3 ∣ q ^ 2 - 1 := CFSG.RankThree.PartTwo.Sec12.OrdG2D4.three_dvd_sq_sub_one h3
  exact one_le_padicValNat_of_dvd hq1 hdvd



theorem ne_inv_of_primitiveRoot_odd {t : Lˣ} {n : ℕ} (hn : Odd n) (hn1 : 1 < n)
    (h : IsPrimitiveRoot (t : L) n) : t ≠ t⁻¹ := by
  intro heq
  have ht2u : t ^ 2 = 1 := by
    have : t * t = 1 := by
      nth_rewrite 1 [heq]
      exact inv_mul_cancel t
    simpa [pow_two] using this
  have ht2L : (t : L) ^ 2 = 1 := by simpa using congrArg Units.val ht2u
  obtain ⟨k, hk⟩ := hn
  have hpow : (t : L) ^ n = 1 := h.pow_eq_one
  rw [hk, pow_add, pow_mul, ht2L, one_pow, one_mul, pow_one] at hpow
  exact h.ne_one hn1 hpow

theorem nw0_ne_one {t : Lˣ} (ht : t ≠ t⁻¹) : (nw0 : ModGL .G2 L) ≠ 1 := by
  intro h
  have h1 : (tz t 1 : ModGL .G2 L) = tz t⁻¹ 1 := by
    calc tz t 1 = nw0 * tz t 1 * nw0⁻¹ := by rw [h]; group
      _ = tz t⁻¹ 1 := nw0_tz t 1
  exact ht (tz_injective h1).1

theorem orderOf_tz_one {ω : Lˣ} (hω3 : ω ^ 3 = 1) (hω1 : ω ≠ 1) :
    orderOf (tz 1 ω : ModGL .G2 L) = 3 := by
  refine orderOf_eq_prime ?_ ?_
  · rw [tz_pow, hω3]
    simpa using tz_one_one
  · intro h
    have h' : (tz 1 ω : ModGL .G2 L) = tz 1 1 := h.trans tz_one_one.symm
    exact hω1 (tz_injective h').2

theorem g2_exists_sylow_inversion_data
    {K : Type} [Field K] [Finite K] (h3 : ¬ 3 ∣ Nat.card K) (hq3 : 3 ≤ Nat.card K) :
    ∃ Q0 : Subgroup (adjointGroup .G2 K),
      (∃ P : Sylow 3 (adjointGroup .G2 K), (P : Subgroup (adjointGroup .G2 K)) = Q0) ∧
      ∃ z0 : ↥Q0,
        Subgroup.center ↥Q0 = Subgroup.zpowers z0 ∧
        orderOf (z0 : adjointGroup .G2 K) = 3 ∧
        ∃ t0 : adjointGroup .G2 K, orderOf t0 = 2 ∧
          t0 * (z0 : adjointGroup .G2 K) * t0⁻¹ = (z0 : adjointGroup .G2 K)⁻¹ := by
  classical
  let q := Nat.card K
  let b := padicValNat 3 (q ^ 2 - 1)
  have hq2 : 2 ≤ q := by omega
  have hb1 : 1 ≤ b := one_le_padicValNat_three_sq_sub_one (q := q) h3 hq2
  have hb0 : 3 ^ b ≠ 0 := pow_ne_zero b (by norm_num)
  have hbpos : 0 < b := by omega
  have h3b1 : 1 < 3 ^ b := one_lt_pow' (by norm_num) (by omega)
  have h3bdvd : 3 ∣ 3 ^ b := by
    obtain ⟨c, hc⟩ : ∃ c, 3 ^ b = 3 * c := by
      refine ⟨3 ^ (b - 1), ?_⟩
      have hb : b = (b - 1) + 1 := by omega
      calc 3 ^ b = 3 ^ ((b - 1) + 1) := congrArg (fun n => 3 ^ n) hb
        _ = 3 ^ (b - 1) * 3 := pow_succ _ _
        _ = 3 * 3 ^ (b - 1) := by ring
    exact ⟨c, hc⟩
  let L := AlgebraicClosure K
  have h3K : (3 : K) ≠ 0 := by
    intro h
    apply h3
    have hℓ : (ringChar K).Prime := CharP.char_is_prime K (ringChar K)
    have hp3 : ringChar K = 3 := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1
      ((CharP.cast_eq_zero_iff K (ringChar K) 3).1 (by exact_mod_cast h))
    have : Fintype K := Fintype.ofFinite K
    obtain ⟨e, -, hqe⟩ := FiniteField.card K (ringChar K)
    rw [Nat.card_eq_fintype_card, hqe, hp3]
    exact dvd_pow_self 3 e.ne_zero
  have h3L : (3 : L) ≠ 0 := by
    intro h
    apply h3K
    have h' : (algebraMap K L) (3 : K) = 0 := by
      rw [show (3 : K) = ((3 : ℕ) : K) by norm_num, map_natCast]
      exact h
    exact (algebraMap K L).injective (h'.trans (map_zero _).symm)
  haveI : NeZero ((3 : ℕ) : L) := ⟨h3L⟩
  haveI : NeZero ((3 ^ b : ℕ) : L) := ⟨by
    rw [Nat.cast_pow]
    exact pow_ne_zero b h3L⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := 3 ^ b)
  let ζu : Lˣ := (hζ.isUnit hb0).unit
  have hζu : IsPrimitiveRoot (ζu : L) (3 ^ b) := by simpa [ζu] using hζ
  have hζu_ne1 : ζu ≠ 1 := fun h => hζu.ne_one h3b1 (congrArg Units.val h)
  obtain ⟨ω, hω⟩ := HasEnoughRootsOfUnity.prim (M := L) (n := 3)
  let ωu : Lˣ := (hω.isUnit (by norm_num)).unit
  have hωu : IsPrimitiveRoot (ωu : L) 3 := by simpa [ωu] using hω
  have hωu3 : ωu ^ 3 = 1 := Units.ext (by simpa [ωu] using hω.pow_eq_one)
  have hωu1 : ωu ≠ 1 := fun h => hωu.ne_one (by norm_num) (congrArg Units.val h)
  obtain ⟨F, hF, hTW⟩ := exists_rational_conj_fixed K
  let n : ModGL .G2 L := if q % 3 = 1 then 1 else nw0
  have hn_mem : n ∈ adjointGroup .G2 L := by
    by_cases hmod : q % 3 = 1
    · have hn : n = (1 : ModGL .G2 L) := by simp [n, hmod]
      rw [hn]; exact one_mem _
    · have hn : n = (nw0 : ModGL .G2 L) := by simp [n, hmod]
      rw [hn]; exact nw0_mem_adjointGroup
  have hn_y : n * Units.map (entrywiseHom F) (yq : ModGL .G2 L) * n⁻¹ = yq := by
    rw [frob_yq]
    by_cases hmod : q % 3 = 1
    · have hn : n = (1 : ModGL .G2 L) := by simp [n, hmod]
      rw [hn]; simp
    · have hn : n = (nw0 : ModGL .G2 L) := by simp [n, hmod]
      rw [hn]
      calc nw0 * yq * nw0⁻¹ = yq * nw0 * nw0⁻¹ := by rw [nw0_comm_yq]
        _ = yq := by group
  have hn_twist : ∀ s u : Lˣ, s ^ (3 ^ b) = 1 → u ^ (3 ^ b) = 1 →
      n * Units.map (entrywiseHom F) (tz s u : ModGL .G2 L) * n⁻¹ = tz s u := by
    intro s u hs hu
    have hFs : Units.map (F : L →* L) s = s ^ q := Units.ext (by
      rw [Units.coe_map, Units.val_pow_eq_pow_val]
      simp [hF, q])
    have hFu : Units.map (F : L →* L) u = u ^ q := Units.ext (by
      rw [Units.coe_map, Units.val_pow_eq_pow_val]
      simp [hF, q])
    rw [frob_tz, hFs, hFu]
    by_cases hmod : q % 3 = 1
    · have hdvd : 3 ^ b ∣ q - 1 :=
        pow_padicValNat_three_sq_sub_one_dvd_of_mod_one (q := q) hq3 hmod
      obtain ⟨c, hc⟩ := hdvd
      have hsfix : s ^ q = s := by
        rw [show q = 3 ^ b * c + 1 by omega, pow_add, pow_mul, hs, one_pow, one_mul, pow_one]
      have hufix : u ^ q = u := by
        rw [show q = 3 ^ b * c + 1 by omega, pow_add, pow_mul, hu, one_pow, one_mul, pow_one]
      have hn : n = (1 : ModGL .G2 L) := by simp [n, hmod]
      rw [hn, hsfix, hufix]
      simp
    · have hmod2 : q % 3 = 2 := by
        have := Nat.mod_lt q (by norm_num : 0 < 3)
        omega
      have hdvd : 3 ^ b ∣ q + 1 :=
        pow_padicValNat_three_sq_sub_one_dvd_of_mod_two (q := q) hq3 hmod2
      obtain ⟨c, hc⟩ := hdvd
      have hsfix : s ^ q = s⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        have hsq1 : s ^ (q + 1) = 1 := by rw [hc, pow_mul, hs, one_pow]
        rwa [pow_succ] at hsq1
      have hufix : u ^ q = u⁻¹ := by
        refine eq_inv_of_mul_eq_one_left ?_
        have huq1 : u ^ (q + 1) = 1 := by rw [hc, pow_mul, hu, one_pow]
        rwa [pow_succ] at huq1
      have hn : n = (nw0 : ModGL .G2 L) := by simp [n, hmod]
      rw [hn, hsfix, hufix, nw0_tz]
      simp
  obtain ⟨g, hg, hFg, hrat⟩ := hTW n hn_mem
  let T : Subgroup (ModGL .G2 L) := tzPart (3 ^ b)
  let hExt : Ext3 T (yq : ModGL .G2 L) := ext3_tzPart (L := L) (m := 3 ^ b) hζu_ne1
  let H : Subgroup (ModGL .G2 L) := extSub hExt
  let S : Subgroup (ModGL .G2 L) := H.map (MulAut.conj g).toMonoidHom
  have hcardT : Nat.card T = 3 ^ (2 * b) := by
    calc Nat.card T = Nat.card (tzPart (3 ^ b) : Subgroup (ModGL .G2 L)) := rfl
      _ = (3 ^ b) ^ 2 := card_tzPart (L := L) (3 ^ b) hb0 hζu
      _ = 3 ^ (2 * b) := by rw [← pow_mul]; congr 1; omega
  have hcardH : Nat.card H = 3 ^ (2 * b + 1) := by
    calc Nat.card H = 3 * Nat.card T := card_extSub hExt
      _ = 3 * 3 ^ (2 * b) := by rw [hcardT]
      _ = 3 ^ (2 * b + 1) := by rw [mul_comm, pow_succ]
  have hHle : S ≤ (adjointGroup .G2 K).map (baseChangeGL (algebraMap K L)) := by
    have hH : H = Subgroup.closure (T ∪ ({yq} : Set (ModGL .G2 L))) := extSub_eq_closure hExt
    rw [show S = H.map (MulAut.conj g).toMonoidHom from rfl, hH, MonoidHom.map_closure]
    refine (Subgroup.closure_le _).2 ?_
    rintro x ⟨y, hy, rfl⟩
    rw [Set.mem_union] at hy
    rcases hy with hy | hy
    · obtain ⟨s, u, hs, hu, rfl⟩ := hy
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hrat (tz s u) (tz_mem_adjointGroup s u) (hn_twist s u hs hu)
    · rw [Set.mem_singleton_iff] at hy
      subst hy
      rw [MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
      exact hrat yq yq_mem_adjointGroup hn_y
  let φ : adjointGroup .G2 K →* ModGL .G2 L :=
    (baseChangeGL (algebraMap K L)).comp (adjointGroup .G2 K).subtype
  have hφinj : Function.Injective φ :=
    (baseChangeGL_injective (τ := .G2) (algebraMap K L)).comp Subtype.val_injective
  have hrange : φ.range = (adjointGroup .G2 K).map (baseChangeGL (algebraMap K L)) := by
    rw [show φ = (baseChangeGL (algebraMap K L)).comp
      (adjointGroup .G2 K).subtype from rfl, MonoidHom.range_comp, Subgroup.range_subtype]
  have hSle : S ≤ φ.range := by rw [hrange]; exact hHle
  let Q0 : Subgroup (adjointGroup .G2 K) := S.comap φ
  have hmapQ : Q0.map φ = S := Subgroup.map_comap_eq_self hSle
  have hcardS : Nat.card S = 3 ^ (2 * b + 1) := by
    calc Nat.card S = Nat.card (H.map (MulAut.conj g).toMonoidHom) := rfl
      _ = Nat.card H := Subgroup.card_map_of_injective (MulAut.conj g).injective
      _ = 3 ^ (2 * b + 1) := hcardH
  have hcardQ : Nat.card Q0 = 3 ^ (2 * b + 1) := by
    rw [← Subgroup.card_map_of_injective (K := Q0) hφinj, hmapQ, hcardS]
  have hind : ¬ 3 ∣ Q0.index := by
    intro hdvd
    have hmul : Q0.index * Nat.card Q0 = Nat.card (adjointGroup .G2 K) :=
      Subgroup.index_mul_card Q0
    rw [hcardQ, CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2] at hmul
    have hidx0 : Q0.index ≠ 0 := by
      intro h0
      rw [h0, zero_mul] at hmul
      have hpos : 0 < CFSG.Open.ordG2 (Nat.card K) := by
        rw [← CFSG.Timmesfeld.ExceptionalOrders.card_adjointGroup_G2]
        exact Nat.card_pos
      omega
    have hv3 : padicValNat 3 (CFSG.Open.ordG2 q) = 2 * b + 1 := by
      simpa [b, q] using CFSG.RankThree.PartTwo.Sec12.OrdG2D4.v3_ordG2_of_not_dvd (a := q) hq3 h3
    have hmul' : Q0.index * 3 ^ (2 * b + 1) = CFSG.Open.ordG2 q := by
      simpa [q] using hmul
    have hv : padicValNat 3 (Q0.index * 3 ^ (2 * b + 1)) = 2 * b + 1 := by rw [hmul', hv3]
    rw [padicValNat.mul hidx0 (pow_ne_zero (2 * b + 1) (by norm_num)),
      padicValNat.prime_pow] at hv
    have hle : 1 ≤ padicValNat 3 Q0.index := one_le_padicValNat_of_dvd hidx0 hdvd
    omega
  have hQ0syl : ∃ P : Sylow 3 (adjointGroup .G2 K),
      (P : Subgroup (adjointGroup .G2 K)) = Q0 :=
    ⟨(IsPGroup.of_card (n := 2 * b + 1) hcardQ).toSylow hind, rfl⟩
  let z0val : ModGL .G2 L := tz 1 ωu⁻¹
  have hωu_inv_pow : (ωu⁻¹ : Lˣ) ^ (3 ^ b) = 1 := by
    have h3inv : (ωu⁻¹) ^ 3 = 1 := by rw [inv_pow, hωu3, inv_one]
    obtain ⟨c, hc⟩ := h3bdvd
    rw [hc, pow_mul, h3inv, one_pow]
  have hzHmem : z0val ∈ H :=
    le_extSub hExt (tz_mem_tzPart (m := 3 ^ b) (by simp) hωu_inv_pow)
  let zH : ↥H := ⟨z0val, hzHmem⟩
  have hzHval : (zH : ModGL .G2 L) = z0val := rfl
  have hzH_order_val : orderOf z0val = 3 := by
    have h := orderOf_tz_one (L := L) (ω := ωu⁻¹)
      (by rw [inv_pow, hωu3, inv_one]) (by simpa using hωu1)
    simpa [z0val] using h
  have hzH_order : orderOf zH = 3 := by
    rw [← Subgroup.orderOf_coe zH, hzHval, hzH_order_val]
  have hcenterH : Subgroup.center ↥H = Subgroup.zpowers zH := by
    apply le_antisymm
    · intro x hx
      have hxv :=
        (mem_center_extSub_tzPart_iff (L := L) (m := 3 ^ b) h3bdvd hωu3 hωu1 hωu x).mp hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hxv
      exact Subgroup.mem_zpowers_iff.mpr ⟨k, Subtype.ext hk⟩
    · intro x hx
      obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.mp hx
      have hzHc : zH ∈ Subgroup.center ↥H :=
        (mem_center_extSub_tzPart_iff (L := L) (m := 3 ^ b) h3bdvd hωu3 hωu1 hωu zH).mpr
          (Subgroup.mem_zpowers z0val)
      rw [← hk]
      exact Subgroup.zpow_mem (K := Subgroup.center ↥H) hzHc k
  let eH : ↥H ≃* ↥S := (MulAut.conj g).subgroupMap H
  have hcardCenterH : Nat.card (Subgroup.center ↥H) = 3 := by
    rw [hcenterH, Nat.card_zpowers, hzH_order]
  have hzSval : ((eH zH : ↥S) : ModGL .G2 L) = g * z0val * g⁻¹ := by
    rw [show ((eH zH : ↥S) : ModGL .G2 L) =
      (MulAut.conj g) ((zH : ↥H) : ModGL .G2 L) from
        MulEquiv.coe_subgroupMap_apply (MulAut.conj g) H zH]
    rw [MulAut.conj_apply, hzHval]
  have hzS_center : eH zH ∈ Subgroup.center ↥S := by
    rw [Subgroup.mem_center_iff]
    intro s
    have hzHc : zH ∈ Subgroup.center ↥H := by
      rw [hcenterH]
      exact Subgroup.mem_zpowers _
    have h := Subgroup.mem_center_iff.mp hzHc (eH.symm s)
    calc s * eH zH = eH (eH.symm s) * eH zH := by rw [eH.apply_symm_apply]
      _ = eH (eH.symm s * zH) := by rw [map_mul]
      _ = eH (zH * eH.symm s) := by rw [h]
      _ = eH zH * eH (eH.symm s) := by rw [map_mul]
      _ = eH zH * s := by rw [eH.apply_symm_apply]
  have hcardCenterS : Nat.card (Subgroup.center ↥S) = 3 := by
    have h : Nat.card ((Subgroup.center ↥H).map (eH : ↥H →* ↥S)) =
        Nat.card (Subgroup.center ↥H) :=
      Subgroup.card_map_of_injective (K := Subgroup.center ↥H) (f := (eH : ↥H →* ↥S))
        eH.injective
    rw [Subgroup.map_center_eq eH] at h
    rw [h, hcardCenterH]
  have hzSval_mem : ((eH zH : ↥S) : ModGL .G2 L) ∈ S := (eH zH).2
  have hzSval_mem' : ((eH zH : ↥S) : ModGL .G2 L) ∈ Q0.map φ := by
    rw [hmapQ]; exact hzSval_mem
  obtain ⟨z0, hz0Q, hφz0⟩ := Subgroup.mem_map.mp hzSval_mem'
  have hz0_order : orderOf z0 = 3 := by
    have hφinjQ : Function.Injective (φ.comp Q0.subtype) := hφinj.comp Subtype.val_injective
    show orderOf ((⟨z0, hz0Q⟩ : ↥Q0) : ↥(adjointGroup .G2 K)) = 3
    rw [Subgroup.orderOf_coe (⟨z0, hz0Q⟩ : ↥Q0),
      ← orderOf_injective (φ.comp Q0.subtype) hφinjQ ⟨z0, hz0Q⟩]
    change orderOf (φ z0) = 3
    rw [hφz0, Subgroup.orderOf_coe, eH.orderOf_eq zH, hzH_order]
  have hcenterQ : Subgroup.center ↥Q0 = Subgroup.zpowers ⟨z0, hz0Q⟩ := by
    have hz0c : (⟨z0, hz0Q⟩ : ↥Q0) ∈ Subgroup.center ↥Q0 := by
      rw [Subgroup.mem_center_iff]
      intro y
      apply Subtype.ext
      apply hφinj
      rw [show ((y * ⟨z0, hz0Q⟩ : ↥Q0) : ↥(adjointGroup .G2 K)) =
            (y : ↥(adjointGroup .G2 K)) * z0 from map_mul Q0.subtype y ⟨z0, hz0Q⟩,
          show ((⟨z0, hz0Q⟩ * y : ↥Q0) : ↥(adjointGroup .G2 K)) =
            z0 * (y : ↥(adjointGroup .G2 K)) from map_mul Q0.subtype ⟨z0, hz0Q⟩ y,
          map_mul, map_mul, hφz0]
      have hyS : φ (y : ↥(adjointGroup .G2 K)) ∈ S := Subgroup.mem_comap.mp y.2
      exact congrArg Subtype.val
        (Subgroup.mem_center_iff.mp hzS_center ⟨φ y, hyS⟩)
    let eQ : ↥Q0 ≃* ↥S :=
      (Subgroup.equivMapOfInjective Q0 φ hφinj).trans (MulEquiv.subgroupCongr hmapQ)
    have heQz : eQ ⟨z0, hz0Q⟩ = eH zH := by
      apply Subtype.ext
      change φ z0 = ((eH zH : ↥S) : ModGL .G2 L)
      exact hφz0
    have hcardCenterQ : Nat.card (Subgroup.center ↥Q0) = 3 := by
      have h : Nat.card ((Subgroup.center ↥Q0).map (eQ : ↥Q0 →* ↥S)) =
          Nat.card (Subgroup.center ↥Q0) :=
        Subgroup.card_map_of_injective (K := Subgroup.center ↥Q0)
          (f := (eQ : ↥Q0 →* ↥S)) eQ.injective
      rw [Subgroup.map_center_eq eQ] at h
      rw [← h, hcardCenterS]
    have hzord : orderOf (⟨z0, hz0Q⟩ : ↥Q0) = 3 := by
      rw [← eQ.orderOf_eq ⟨z0, hz0Q⟩, heQz, eH.orderOf_eq zH, hzH_order]
    have hle : Subgroup.zpowers (⟨z0, hz0Q⟩ : ↥Q0) ≤ Subgroup.center ↥Q0 :=
      Subgroup.zpowers_le.mpr hz0c
    have heq : Nat.card (Subgroup.center ↥Q0) =
        Nat.card (Subgroup.zpowers (⟨z0, hz0Q⟩ : ↥Q0)) := by
      rw [hcardCenterQ, Nat.card_zpowers, hzord]
    exact (Subgroup.eq_of_le_of_card_ge hle heq.le).symm
  let tL : ModGL .G2 L := g * nw0 * g⁻¹
  have htL_adj : tL ∈ adjointGroup .G2 L :=
    mul_mem (mul_mem hg nw0_mem_adjointGroup) (inv_mem hg)
  have htL_fix : Units.map (entrywiseHom F) tL = tL := by
    rw [show tL = g * nw0 * g⁻¹ from rfl, map_mul, map_mul, map_inv, hFg, frob_nw0]
    have hn_nw0 : n * (nw0 : ModGL .G2 L) * n⁻¹ = nw0 := by
      by_cases hmod : q % 3 = 1
      · have hn : n = (1 : ModGL .G2 L) := by simp [n, hmod]
        rw [hn]; simp
      · have hn : n = (nw0 : ModGL .G2 L) := by simp [n, hmod]
        rw [hn]
        calc nw0 * nw0 * nw0⁻¹ = (nw0 * nw0) * nw0⁻¹ := by group
          _ = 1 * nw0⁻¹ := by rw [← pow_two, nw0_sq]
          _ = nw0 := by
            rw [one_mul]
            calc nw0⁻¹ = (nw0 * nw0) * nw0⁻¹ := by rw [← pow_two, nw0_sq, one_mul]
              _ = nw0 * (nw0 * nw0⁻¹) := by group
              _ = nw0 := by rw [mul_inv_cancel, mul_one]
    calc g * n * nw0 * (g * n)⁻¹ = g * (n * nw0 * n⁻¹) * g⁻¹ := by group
      _ = g * nw0 * g⁻¹ := by rw [hn_nw0]
  have htL_mem_map : tL ∈ (adjointGroup .G2 K).map (baseChangeGL (algebraMap K L)) := by
    rw [← (CFSG.RankThree.Chevalley.G2_F4_exact_finite_field_fixed_root_matrices
      (τ := .G2) (Or.inl rfl) K L F hF).1]
    exact Subgroup.mem_inf.mpr ⟨htL_adj, htL_fix⟩
  have htL_range : tL ∈ φ.range := by rw [hrange]; exact htL_mem_map
  obtain ⟨t0, hφt0⟩ := MonoidHom.mem_range.mp htL_range
  have hnw0_ne : (nw0 : ModGL .G2 L) ≠ 1 := by
    refine nw0_ne_one (L := L) (t := ζu) ?_
    have hodd : Odd (3 ^ b) := Odd.pow (n := b) (by norm_num)
    exact ne_inv_of_primitiveRoot_odd hodd h3b1 hζu
  have htL_order : orderOf tL = 2 := by
    have hsq : tL ^ 2 = 1 := by
      rw [show tL = g * nw0 * g⁻¹ from rfl]
      calc (g * nw0 * g⁻¹) ^ 2 = g * (nw0 * nw0) * g⁻¹ := by rw [pow_two]; group
        _ = g * nw0 ^ 2 * g⁻¹ := by rw [pow_two]
        _ = 1 := by rw [nw0_sq]; group
    have hne : tL ≠ 1 := by
      intro h
      have : (nw0 : ModGL .G2 L) = 1 := by
        have := congrArg (fun z : ModGL .G2 L => g⁻¹ * z * g) h
        simpa [tL, mul_assoc] using this
      exact hnw0_ne this
    exact orderOf_eq_prime hsq hne
  have ht0_order : orderOf t0 = 2 := by
    rw [← orderOf_injective φ hφinj t0, hφt0, htL_order]
  have hz0val_inv : z0val⁻¹ = tz 1 ωu := by
    rw [show z0val = (tz 1 ωu⁻¹ : ModGL .G2 L) from rfl, tz_inv]
    simp
  have ht0inv : t0 * (z0 : adjointGroup .G2 K) * t0⁻¹ = (z0 : adjointGroup .G2 K)⁻¹ := by
    apply hφinj
    rw [map_mul, map_mul, map_inv, map_inv, hφt0, hφz0, hzSval]
    rw [show tL = g * nw0 * g⁻¹ from rfl]
    calc (g * nw0 * g⁻¹) * (g * z0val * g⁻¹) * (g * nw0 * g⁻¹)⁻¹
        = g * (nw0 * z0val * nw0⁻¹) * g⁻¹ := by group
      _ = g * z0val⁻¹ * g⁻¹ := by
          rw [show z0val = (tz 1 ωu⁻¹ : ModGL .G2 L) from rfl, nw0_tz,
            show ((tz 1 ωu⁻¹ : ModGL .G2 L))⁻¹ = tz 1 ωu from by rw [tz_inv]; simp]
          simp
      _ = (g * z0val * g⁻¹)⁻¹ := by
          rw [show z0val = (tz 1 ωu⁻¹ : ModGL .G2 L) from rfl]
          group
  exact ⟨Q0, hQ0syl, ⟨z0, hz0Q⟩, hcenterQ, hz0_order, t0, ht0_order, ht0inv⟩


theorem g2_sylow_inversion_of_not_dvd
    {K : Type} [Field K] [Finite K] (h3 : ¬ 3 ∣ Nat.card K) (hq3 : 3 ≤ Nat.card K) :
    ∀ (Q : Sylow 3 (adjointGroup .G2 K)) (z : adjointGroup .G2 K),
      z ∈ (Q : Subgroup (adjointGroup .G2 K)) →
      z ∈ Subgroup.centralizer ((Q : Subgroup (adjointGroup .G2 K)) :
        Set (adjointGroup .G2 K)) →
      orderOf z = 3 → ∃ t : adjointGroup .G2 K, orderOf t = 2 ∧
        t * z * t⁻¹ = z⁻¹ := by
  obtain ⟨Q0, hQ0syl, z0, hcenter, -, t0, ht0ord, ht0inv⟩ :=
    g2_exists_sylow_inversion_data h3 hq3
  exact sylow_center_inversion_transport Q0 hQ0syl z0 hcenter t0 ht0ord ht0inv

theorem g2_inverting_of_lieModel
    {X : Type} [Group X] [Finite X] {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2) (hp3 : p ≠ 3)
    (hX : CFSG.Blueprint.LieModel X .G2 0 p 1)
    (Q : Sylow 3 X) {z : X}
    (hzQ : z ∈ (Q : Subgroup X))
    (hzc : z ∈ Subgroup.centralizer ((Q : Subgroup X) : Set X))
    (hz3 : orderOf z = 3) :
    ∃ t : X, orderOf t = 2 ∧ t * z * t⁻¹ = z⁻¹ := by
  classical
  have hc : CFSG.Blueprint.ChevalleyExceptionalModel X .G2 p 1 :=
    CFSG.Blueprint.LieModel.chevalleyExceptionalModel hX (by decide)
  have hm : CFSG.Blueprint.UntwistedChevalleyModel X .G2 (p ^ 1) := hc.2
  obtain ⟨K, hKfield, hKfinite, hKcard, ⟨eX⟩⟩ :=
    CFSG.LieType.Chevalley.nonempty_mulEquiv_adjointGroup (τ := .G2) hm
  letI : Field K := hKfield
  letI : Finite K := hKfinite
  have hKp : Nat.card K = p := by simpa using hKcard
  have hq3 : 3 ≤ Nat.card K := by
    rw [hKp]
    have := hp.one_lt
    omega
  have h3 : ¬ 3 ∣ Nat.card K := by
    rw [hKp]
    intro h
    have h3p : 3 = p := (Nat.prime_dvd_prime_iff_eq Nat.prime_three hp).1 h
    exact hp3 h3p.symm
  let Q' : Sylow 3 (adjointGroup .G2 K) :=
    Sylow.mapSurjective (f := eX.toMonoidHom) eX.surjective Q
  let z' : adjointGroup .G2 K := eX z
  have hQ' : (Q' : Subgroup (adjointGroup .G2 K)) =
      (Q : Subgroup X).map eX.toMonoidHom := by
    simp [Q']
  have hzQ' : z' ∈ (Q' : Subgroup (adjointGroup .G2 K)) := by
    rw [hQ']
    exact Subgroup.mem_map_of_mem eX.toMonoidHom hzQ
  have hzc' : z' ∈ Subgroup.centralizer
      ((Q' : Subgroup (adjointGroup .G2 K)) : Set (adjointGroup .G2 K)) := by
    rw [Subgroup.mem_centralizer_iff] at hzc ⊢
    intro y hy
    rw [hQ'] at hy
    obtain ⟨q, hq, rfl⟩ := hy
    simpa only [map_mul, z', MulEquiv.coe_toMonoidHom] using congrArg eX.toMonoidHom
      (Subgroup.mem_centralizer_iff.mp hzc q hq)
  have hz3' : orderOf z' = 3 := by
    simpa [z'] using (MulEquiv.orderOf_eq eX z).trans hz3
  obtain ⟨t', ht'2, ht'inv⟩ :=
    g2_sylow_inversion_of_not_dvd h3 hq3 Q' z' hzQ' hzc' hz3'
  refine ⟨eX.symm t', ?_, ?_⟩
  · rw [← (MulEquiv.orderOf_eq eX (eX.symm t')), eX.apply_symm_apply, ht'2]
  · apply eX.injective
    rw [map_mul, map_mul, map_inv, eX.apply_symm_apply, map_inv]
    exact ht'inv

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
