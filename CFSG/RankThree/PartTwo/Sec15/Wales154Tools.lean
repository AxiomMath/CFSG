module

public import CFSG.RankThree.PartTwo.Sec15.Wales154Reduce
import CFSG.RankThree.PartTwo.Sec6.Item612Plus
import CFSG.GroupTheory.PCore.OpenTransport

public section

namespace CFSG.RankThree.PartTwo.Sec15.Wales154

open CFSG CFSG.RankThree CFSG.RankThree.PartTwo CFSG.GH74.GLS
open scoped commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem card_quot_mul_dvd {X Y : Subgroup G} (hXY : X ≤ Y) :
    Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) *
        (CFSG.Open.pCoreOf 2 X ⊓ CFSG.Open.pCoreOf 2 Y).relIndex (CFSG.Open.pCoreOf 2 X) *
        ((X ⊔ CFSG.Open.pCoreOf 2 Y).relIndex Y : ℕ) =
      Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set D := CFSG.Open.pCoreOf 2 Y with hD
  set P := CFSG.Open.pCoreOf 2 X with hP
  have hDY : D ≤ Y := CFSG.LieType.BorelTits.pCoreOf_le 2 Y
  have hPX : P ≤ X := CFSG.LieType.BorelTits.pCoreOf_le 2 X
  have hYD : Y ≤ Subgroup.normalizer (D : Set G) := CFSG.LieType.BorelTits.le_normalizer_pCoreOf 2 Y
  have hD2 : IsPGroup 2 D := CFSG.LieType.BorelTits.pCoreOf_isPGroup 2 Y
  have hXDP : X ⊓ D ≤ P :=
    CFSG.LieType.BorelTits.le_pCoreOf_of_le_normalizer 2 inf_le_left
      (Late.le_normalizer_inf Subgroup.le_normalizer (hXY.trans hYD)) (hD2.to_le inf_le_right)
  have hXD_eq : X ⊓ D = P ⊓ D := le_antisymm (le_inf hXDP inf_le_right) (inf_le_inf_right D hPX)
  have h1 := Sec6.card_sup_mul_card_inf (hXY.trans hYD)
  have h2 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥X)
  have h3 := Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥Y)
  have hcD : Nat.card (CFSG.pCore 2 ↥Y) = Nat.card D := by
    rw [hD, CFSG.Open.pCoreOf, Subgroup.card_map_of_injective Y.subtype_injective]
  have hcP : Nat.card (CFSG.pCore 2 ↥X) = Nat.card P := by
    rw [hP, CFSG.Open.pCoreOf, Subgroup.card_map_of_injective X.subtype_injective]
  rw [hcP] at h2
  rw [hcD] at h3
  have h4 := Subgroup.relIndex_mul_card (P ⊓ D) P
  rw [inf_eq_left.mpr (inf_le_left : P ⊓ D ≤ P)] at h4
  have h5 := Subgroup.relIndex_mul_card (X ⊔ D) Y
  rw [inf_eq_left.mpr (sup_le hXY hDY)] at h5
  rw [hXD_eq] at h1
  have hpos : 0 < Nat.card (P ⊓ D : Subgroup G) * Nat.card D :=
    Nat.mul_pos Nat.card_pos Nat.card_pos
  refine Nat.eq_of_mul_eq_mul_right hpos ?_
  calc Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) * (P ⊓ D).relIndex P * (X ⊔ D).relIndex Y *
        (Nat.card (P ⊓ D : Subgroup G) * Nat.card D)
      = (X ⊔ D).relIndex Y * (Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) *
          ((P ⊓ D).relIndex P * Nat.card (P ⊓ D : Subgroup G)) * Nat.card D) := by ring
    _ = (X ⊔ D).relIndex Y * (Nat.card X * Nat.card D) := by rw [h4, ← h2]
    _ = (X ⊔ D).relIndex Y * (Nat.card (X ⊔ D : Subgroup G) * Nat.card (P ⊓ D : Subgroup G)) := by
        rw [h1]
    _ = Nat.card Y * Nat.card (P ⊓ D : Subgroup G) := by rw [← h5]; ring
    _ = Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) * (Nat.card (P ⊓ D : Subgroup G) * Nat.card D) := by
        rw [h3]; ring

theorem card_quot_dvd {X Y : Subgroup G} (hXY : X ≤ Y) :
    Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) ∣ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  rw [← card_quot_mul_dvd hXY, mul_assoc]
  exact dvd_mul_right _ _

theorem two_mul_card_quot_le {X Y : Subgroup G} (hXY : X ≤ Y)
    (hne : Y ≠ X ⊔ CFSG.Open.pCoreOf 2 Y) :
    2 * Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) ≤ Nat.card (↥Y ⧸ CFSG.pCore 2 ↥Y) := by
  have hle : X ⊔ CFSG.Open.pCoreOf 2 Y ≤ Y := sup_le hXY (CFSG.LieType.BorelTits.pCoreOf_le 2 Y)
  have hi : 2 ≤ (X ⊔ CFSG.Open.pCoreOf 2 Y).relIndex Y := by
    by_contra h
    push Not at h
    have h0 : (X ⊔ CFSG.Open.pCoreOf 2 Y).relIndex Y ≠ 0 := by
      intro h0
      have h5 := Subgroup.relIndex_mul_card (X ⊔ CFSG.Open.pCoreOf 2 Y) Y
      rw [h0, zero_mul] at h5
      exact Nat.card_pos.ne' h5.symm
    have h1 : (X ⊔ CFSG.Open.pCoreOf 2 Y).relIndex Y = 1 := by omega
    exact hne (le_antisymm (Subgroup.relIndex_eq_one.mp h1) hle)
  have hr : 1 ≤ (CFSG.Open.pCoreOf 2 X ⊓ CFSG.Open.pCoreOf 2 Y).relIndex
      (CFSG.Open.pCoreOf 2 X) := by
    refine Nat.one_le_iff_ne_zero.mpr fun h0 => ?_
    have h4 := Subgroup.relIndex_mul_card (CFSG.Open.pCoreOf 2 X ⊓ CFSG.Open.pCoreOf 2 Y)
      (CFSG.Open.pCoreOf 2 X)
    rw [h0, zero_mul] at h4
    exact Nat.card_pos.ne' h4.symm
  rw [← card_quot_mul_dvd hXY]
  calc 2 * Nat.card (↥X ⧸ CFSG.pCore 2 ↥X)
      = Nat.card (↥X ⧸ CFSG.pCore 2 ↥X) * 1 * 2 := by ring
    _ ≤ _ := Nat.mul_le_mul (Nat.mul_le_mul_left _ hr) hi

omit [Finite G] in
theorem actQ_eq_one_iff {Y : Subgroup G} (m : Subgroup.normalizer (Y : Set G)) :
    Sec17.Proof17Res6.actQ Y m = 1 ↔
      (m : G) ∈ centralizerSection Y (CFSG.Open.pCoreOf 2 Y) := by
  constructor
  · intro hm
    refine ⟨m.2, CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y m.2, fun y hy => ?_⟩
    have h1 := Proof155w3.commutator_mem_of_actQ_eq_one hm y hy
    have e : ⁅y, (m : G)⁆ = ((m : G) * y * (m : G)⁻¹ * y⁻¹)⁻¹ := by
      rw [commutatorElement_def]
      group
    rw [e]
    exact inv_mem h1
  · rintro ⟨-, -, hc⟩
    refine MulEquiv.ext fun q => ?_
    induction q using QuotientGroup.induction_on with
    | H y =>
      rw [MulAut.one_apply]
      change Sec17.Proof17Res6.actQ Y m (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y) = _
      rw [Sec17.Proof17Res6.actQ_mk]
      change (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) (Y.normalizerMonoidHom m y)) =
        QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y
      rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq,
        ← CFSG.mem_openPCoreOf_iff]
      have h1 := hc (y : G)⁻¹ (inv_mem y.2)
      have e : (((Y.normalizerMonoidHom m y)⁻¹ * y : ↥Y) : G) = (⁅(y : G)⁻¹, (m : G)⁆)⁻¹ := by
        change ((m : G) * y * (m : G)⁻¹)⁻¹ * y = _
        rw [commutatorElement_def]
        group
      rw [e]
      exact inv_mem h1

omit [Finite G] in
theorem card_barR_eq_relIndex {Y R : Subgroup G} (hRY : R ≤ Subgroup.normalizer (Y : Set G)) :
    Nat.card (barR Y R) = (centralizerSection Y (CFSG.Open.pCoreOf 2 Y)).relIndex R := by
  rw [barR, ← Subgroup.relIndex_ker]
  have hker : (Sec17.Proof17Res6.actQ Y).ker =
      (centralizerSection Y (CFSG.Open.pCoreOf 2 Y)).subgroupOf
        (Subgroup.normalizer (Y : Set G)) := by
    ext m
    rw [MonoidHom.mem_ker, Subgroup.mem_subgroupOf, actQ_eq_one_iff]
  rw [hker, Subgroup.relIndex_subgroupOf hRY]

omit [Finite G] in
theorem mem_normalizer_comap_conj {Q : Type*} [Group Q] {B : Subgroup (MulAut Q)} {e : Q}
    (he : MulAut.conj e ∈ Subgroup.normalizer (B : Set (MulAut Q))) :
    e ∈ Subgroup.normalizer ((B.comap (MulAut.conj : Q →* MulAut Q) : Subgroup Q) : Set Q) := by
  rw [Subgroup.mem_normalizer_iff] at he ⊢
  intro s
  simp only [Subgroup.mem_comap, map_mul, map_inv]
  exact he _

omit [Finite G] in
theorem conj_injective_of_center_eq_bot {Q : Type*} [Group Q] (hZ : Subgroup.center Q = ⊥) :
    Function.Injective (MulAut.conj : Q →* MulAut Q) := by
  intro x y hxy
  have hc : x⁻¹ * y ∈ Subgroup.center Q := by
    rw [Subgroup.mem_center_iff]
    intro z
    have h1 := congrArg (fun σ : MulAut Q => σ z) hxy
    simp only [MulAut.conj_apply] at h1
    calc z * (x⁻¹ * y) = x⁻¹ * (x * z * x⁻¹) * y := by group
      _ = x⁻¹ * (y * z * y⁻¹) * y := by rw [h1]
      _ = x⁻¹ * y * z := by group
  rw [hZ, Subgroup.mem_bot] at hc
  exact inv_mul_eq_one.mp hc

theorem pCoreOf_le_and_nonempty_quot_equiv {X Y : Subgroup G} (hXY : X ≤ Y) {S : Type*}
    [Group S] [IsSimpleGroup S] (hS : ¬ IsPGroup 2 S)
    (e : ((X.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))) ≃* S) :
    CFSG.Open.pCoreOf 2 X ≤ CFSG.Open.pCoreOf 2 Y ∧
      Nonempty (↥X ⧸ CFSG.pCore 2 ↥X ≃* S) := by
  classical
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set κ := QuotientGroup.mk' (CFSG.pCore 2 ↥Y) with hκ
  set φ : ↥X →* ↥Y ⧸ CFSG.pCore 2 ↥Y := κ.comp (Subgroup.inclusion hXY) with hφ
  have hrange : φ.range = (X.subgroupOf Y).map κ := by
    rw [hφ, MonoidHom.range_comp, Subgroup.inclusion_range]
  have hker1 : φ.ker ≤ CFSG.pCore 2 ↥X := by
    refine CFSG.BaerSuzuki.Helpers.le_pCore_of_normal_isPGroup φ.normal_ker ?_
    rintro ⟨x, hx⟩
    have hx' : (Subgroup.inclusion hXY x) ∈ CFSG.pCore 2 ↥Y := by
      rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, hκ, QuotientGroup.mk'_apply,
        QuotientGroup.eq_one_iff] at hx
      exact hx
    obtain ⟨n, hn⟩ := (CFSG.pCore_isPGroup : IsPGroup 2 (CFSG.pCore 2 ↥Y)) ⟨_, hx'⟩
    refine ⟨n, ?_⟩
    have h1 : (Subgroup.inclusion hXY x) ^ 2 ^ n = 1 := by
      simpa using congrArg Subtype.val hn
    have h2 : x ^ 2 ^ n = 1 := by
      apply Subgroup.inclusion_injective hXY
      rw [map_pow, h1, map_one]
    exact Subtype.ext (by simpa using h2)
  set e' : ↥φ.range ≃* S := (MulEquiv.subgroupCongr hrange).trans e with he'
  set ψ' : ↥X →* S := e'.toMonoidHom.comp φ.rangeRestrict with hψ'
  have hψ's : Function.Surjective ψ' := e'.surjective.comp φ.rangeRestrict_surjective
  have hkerψ : ψ'.ker = φ.ker := by
    ext x
    rw [hψ', MonoidHom.mem_ker, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom,
      MulEquiv.map_eq_one_iff, ← MonoidHom.mem_ker, MonoidHom.ker_rangeRestrict]
  have hker2 : CFSG.pCore 2 ↥X ≤ φ.ker := by
    have hTn : ((CFSG.pCore 2 ↥X).map ψ').Normal := (CFSG.pCore_normal).map ψ' hψ's
    have hT2 : IsPGroup 2 ((CFSG.pCore 2 ↥X).map ψ') := CFSG.pCore_isPGroup.map ψ'
    rcases hTn.eq_bot_or_eq_top with hT | hT
    · rw [← hkerψ, ← Subgroup.map_eq_bot_iff]
      exact hT
    · exfalso
      apply hS
      rw [hT] at hT2
      exact hT2.of_equiv Subgroup.topEquiv
  have hkerEq : φ.ker = CFSG.pCore 2 ↥X := le_antisymm hker1 hker2
  refine ⟨fun g hg => ?_, ⟨(QuotientGroup.quotientMulEquivOfEq (hkerψ.trans hkerEq)).symm.trans
    (QuotientGroup.quotientKerEquivOfSurjective ψ' hψ's)⟩⟩
  obtain ⟨x, hx, rfl⟩ := hg
  have hx' : x ∈ φ.ker := hker2 hx
  rw [MonoidHom.mem_ker, hφ, MonoidHom.comp_apply, hκ, QuotientGroup.mk'_apply,
    QuotientGroup.eq_one_iff] at hx'
  exact ⟨_, hx', rfl⟩

section Four

variable {Γ : Type*} [Group Γ]

theorem mem_centralizer_of_fix {R : Subgroup Γ} (hR4 : Nat.card R = 4)
    (hR2 : ∀ r ∈ R, r ^ 2 = 1) {e : Γ} {k : ℕ} (hek : e ^ 3 ^ k = 1)
    (heR : e ∈ Subgroup.normalizer (R : Set Γ)) {r : Γ} (hr : r ∈ R) (hr1 : r ≠ 1)
    (her : e * r = r * e) : e ∈ Subgroup.centralizer (R : Set Γ) := by
  classical
  have hfin : Finite R := Nat.finite_of_card_ne_zero (by rw [hR4]; norm_num)
  have : Fintype R := Fintype.ofFinite R
  rw [Subgroup.mem_centralizer_iff]
  intro t ht
  rw [eq_comm]
  by_cases ht1 : t = 1
  · rw [ht1, one_mul, mul_one]
  by_cases htr : t = r
  · rw [htr]; exact her
  have hrr : r * r = 1 := by rw [← sq]; exact hR2 r hr
  have htt : t * t = 1 := by rw [← sq]; exact hR2 t ht
  have hrt : r * t ∈ R := R.mul_mem hr ht
  have hsub : ({1, r, t, r * t} : Finset Γ) ⊆ (R : Set Γ).toFinset := by
    intro x hx
    simp only [Finset.mem_insert, Finset.mem_singleton] at hx
    rw [Set.mem_toFinset]
    rcases hx with rfl | rfl | rfl | rfl
    · exact R.one_mem
    · exact hr
    · exact ht
    · exact hrt
  have hcard4 : (R : Set Γ).toFinset.card = 4 := by
    rw [Set.toFinset_card, ← Nat.card_eq_fintype_card]
    exact hR4
  have hdist : ({1, r, t, r * t} : Finset Γ).card = 4 := by
    have h1 : (1 : Γ) ∉ ({r, t, r * t} : Finset Γ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => hr1 h.symm, fun h => ht1 h.symm, fun h => htr ?_⟩
      calc t = r * (r * t) := by rw [← mul_assoc, hrr, one_mul]
        _ = r * 1 := by rw [← h]
        _ = r := mul_one r
    have h2 : r ∉ ({t, r * t} : Finset Γ) := by
      simp only [Finset.mem_insert, Finset.mem_singleton, not_or]
      refine ⟨fun h => htr h.symm, fun h => ht1 ?_⟩
      calc t = r * (r * t) := by rw [← mul_assoc, hrr, one_mul]
        _ = r * r := by rw [← h]
        _ = 1 := hrr
    have h3 : t ∉ ({r * t} : Finset Γ) := by
      simp only [Finset.mem_singleton]
      intro h
      apply hr1
      calc r = r * t * t := by rw [mul_assoc, htt, mul_one]
        _ = t * t := by rw [← h]
        _ = 1 := htt
    rw [Finset.card_insert_of_notMem h1, Finset.card_insert_of_notMem h2,
      Finset.card_insert_of_notMem h3, Finset.card_singleton]
  have heq : ({1, r, t, r * t} : Finset Γ) = (R : Set Γ).toFinset :=
    Finset.eq_of_subset_of_card_le hsub (by rw [hcard4, hdist])
  set u := e * t * e⁻¹ with hu
  have huR : u ∈ R := (Subgroup.mem_normalizer_iff.mp heR t).mp ht
  have hu' : u ∈ ({1, r, t, r * t} : Finset Γ) := by
    rw [heq, Set.mem_toFinset]; exact huR
  have hcomm_r : ∀ n : ℕ, e ^ n * r = r * e ^ n := fun n => (Commute.pow_left her n).eq
  simp only [Finset.mem_insert, Finset.mem_singleton] at hu'
  rcases hu' with hu1 | hur | hut | hurt
  · exfalso
    apply ht1
    have : e * t * e⁻¹ = e * 1 * e⁻¹ := by rw [← hu, hu1, mul_one, mul_inv_cancel]
    exact mul_left_cancel (mul_right_cancel this)
  · exfalso
    apply htr
    have h1 : e * t * e⁻¹ = e * r * e⁻¹ := by
      rw [← hu, hur, her, mul_assoc, mul_inv_cancel, mul_one]
    exact mul_left_cancel (mul_right_cancel h1)
  · calc e * t = e * t * e⁻¹ * e := by group
      _ = t * e := by rw [← hu, hut]
  ·
    exfalso
    have he2 : e ^ 2 * t * (e ^ 2)⁻¹ = t := by
      calc e ^ 2 * t * (e ^ 2)⁻¹ = e * (e * t * e⁻¹) * e⁻¹ := by rw [sq]; group
        _ = e * (r * t) * e⁻¹ := by rw [← hu, hurt]
        _ = (e * r * e⁻¹) * (e * t * e⁻¹) := by group
        _ = r * (r * t) := by rw [her, mul_assoc r e, mul_inv_cancel, mul_one, ← hu, hurt]
        _ = t := by rw [← mul_assoc, hrr, one_mul]
    have he2n : ∀ j : ℕ, (e ^ 2) ^ j * t * ((e ^ 2) ^ j)⁻¹ = t := by
      intro j
      induction j with
      | zero => simp
      | succ j ih =>
        calc (e ^ 2) ^ (j + 1) * t * ((e ^ 2) ^ (j + 1))⁻¹ =
            (e ^ 2) ^ j * (e ^ 2 * t * (e ^ 2)⁻¹) * ((e ^ 2) ^ j)⁻¹ := by group
          _ = t := by rw [he2, ih]
    obtain ⟨j, hj⟩ : Odd (3 ^ k) := Odd.pow (by decide)
    have hfin' : e ^ 3 ^ k * t * (e ^ 3 ^ k)⁻¹ = r * t := by
      rw [hj, pow_succ, pow_mul]
      calc (e ^ 2) ^ j * e * t * ((e ^ 2) ^ j * e)⁻¹ =
          (e ^ 2) ^ j * (e * t * e⁻¹) * ((e ^ 2) ^ j)⁻¹ := by group
        _ = (e ^ 2) ^ j * (r * t) * ((e ^ 2) ^ j)⁻¹ := by rw [← hu, hurt]
        _ = ((e ^ 2) ^ j * r * ((e ^ 2) ^ j)⁻¹) * ((e ^ 2) ^ j * t * ((e ^ 2) ^ j)⁻¹) := by
          group
        _ = r * t := by
          rw [he2n j, ← pow_mul, hcomm_r, mul_assoc r, mul_inv_cancel, mul_one]
    rw [hek, one_mul, inv_one, mul_one] at hfin'
    apply hr1
    calc r = r * t * t := by rw [mul_assoc, htt, mul_one]
      _ = t * t := by rw [← hfin']
      _ = 1 := htt

omit [Group Γ] in
theorem eq_one_of_isPerfect {H A : Type*} [Group H] [Group A] [IsMulCommutative A]
    [hH : Group.IsPerfect H] (f : H →* A) (x : H) : f x = 1 := by
  have h := Abelianization.commutator_subset_ker f
  rw [hH.commutator_eq_top] at h
  exact h (Subgroup.mem_top x)

end Four

end CFSG.RankThree.PartTwo.Sec15.Wales154
