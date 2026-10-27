module

public import CFSG.Quasithin.H13.L32A72b

public section

namespace CFSG.Quasithin.H13.L32A

open CFSG.Open CFSG.Blueprint CFSG.QuasithinUnique CFSG.LieType.BorelTits
open scoped IsMulCommutative commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_mem_fix_mod {B X Y : Subgroup G} (hYX : Y ≤ X) (hne : Y ≠ X)
    (hB : IsPGroup 2 B) (hX : IsPGroup 2 X) (hBX : B ≤ Subgroup.normalizer (X : Set G))
    (hBY : B ≤ Subgroup.normalizer (Y : Set G)) (hXY : X ≤ Subgroup.normalizer (Y : Set G)) :
    ∃ m ∈ X, m ∉ Y ∧ ∀ b ∈ B, b * m * b⁻¹ * m⁻¹ ∈ Y := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hFp : IsPGroup 2 ↥(B ⊔ X) := IsPGroup.to_sup_of_normal_right' hB hX hBX
  have hYF : Y ≤ B ⊔ X := hYX.trans le_sup_right
  have hXF : X ≤ B ⊔ X := le_sup_right
  have hYn : (Y.subgroupOf (B ⊔ X)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYF).mpr (sup_le hBY hXY)
  have hXn : (X.subgroupOf (B ⊔ X)).Normal :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hXF).mpr (sup_le hBX Subgroup.le_normalizer)
  set π := QuotientGroup.mk' (Y.subgroupOf (B ⊔ X)) with hπ
  have hπ1 : ∀ y : ↥(B ⊔ X), π y = 1 ↔ (y : G) ∈ Y := fun y => by
    rw [hπ, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff, Subgroup.mem_subgroupOf]
  set X' := (X.subgroupOf (B ⊔ X)).map π with hX'
  have : X'.Normal := hXn.map π (QuotientGroup.mk'_surjective _)
  obtain ⟨x₀, hx₀X, hx₀Y⟩ : ∃ x ∈ X, x ∉ Y := by
    by_contra h
    push Not at h
    exact hne (le_antisymm hYX h)
  have hX'ne : X' ≠ ⊥ := by
    rw [Subgroup.ne_bot_iff_exists_ne_one]
    refine ⟨⟨π ⟨x₀, hXF hx₀X⟩, ⟨x₀, hXF hx₀X⟩, Subgroup.mem_subgroupOf.mpr hx₀X, rfl⟩, ?_⟩
    intro h
    exact hx₀Y ((hπ1 _).mp (congrArg Subtype.val h))
  have : Group.IsNilpotent (↥(B ⊔ X) ⧸ Y.subgroupOf (B ⊔ X)) :=
    (hFp.to_quotient _).isNilpotent
  obtain ⟨⟨q, hq⟩, hq1⟩ :=
    Subgroup.ne_bot_iff_exists_ne_one.mp (Group.IsNilpotent.inf_center_ne_bot_of_normal hX'ne)
  obtain ⟨hqX, hqZ⟩ := Subgroup.mem_inf.mp hq
  obtain ⟨y, hyX, rfl⟩ := hqX
  refine ⟨y, Subgroup.mem_subgroupOf.mp hyX, fun h => hq1 (Subtype.ext ((hπ1 y).mpr h)),
    fun b hb => ?_⟩
  have hbF : b ∈ B ⊔ X := Subgroup.mem_sup_left hb
  have hc := Subgroup.mem_center_iff.mp hqZ (π ⟨b, hbF⟩)
  have h1 : π (⟨b, hbF⟩ * y * ⟨b, hbF⟩⁻¹ * y⁻¹) = 1 := by
    rw [map_mul, map_mul, map_mul, map_inv, map_inv, hc]
    group
  simpa using (hπ1 _).mp h1

omit [Finite G] in
theorem conj_mem_centralizer_of_mem_normalizer {V : Subgroup G} {g x : G}
    (hg : g ∈ Subgroup.normalizer (V : Set G)) (hx : x ∈ Subgroup.centralizer (V : Set G)) :
    g * x * g⁻¹ ∈ Subgroup.centralizer (V : Set G) := by
  rw [Subgroup.mem_centralizer_iff] at hx ⊢
  intro v hv
  have hv' : g⁻¹ * v * g ∈ V := by
    have := (Subgroup.mem_normalizer_iff.mp (inv_mem hg) v).mp hv
    simpa using this
  have h1 := hx _ hv'
  calc v * (g * x * g⁻¹) = g * ((g⁻¹ * v * g) * x) * g⁻¹ := by group
    _ = g * (x * (g⁻¹ * v * g)) * g⁻¹ := by rw [h1]
    _ = g * x * g⁻¹ * v := by group

omit [Finite G] in
theorem le_normalizer_of_conj_mem' {H X : Subgroup G}
    (h : ∀ g ∈ H, ∀ x ∈ X, g * x * g⁻¹ ∈ X) : H ≤ Subgroup.normalizer (X : Set G) := by
  intro g hg
  rw [Subgroup.mem_normalizer_iff]
  intro x
  refine ⟨h g hg x, fun hx => ?_⟩
  have := h g⁻¹ (inv_mem hg) _ hx
  simpa [mul_assoc] using this

omit [Finite G] in
theorem sup_u0_eq_of {T V : Subgroup G} (hu0 : u0 T V = fsuV1 T V) : V ⊔ u0 T V = V := by
  rw [hu0]
  exact sup_eq_left.mpr inf_le_left

namespace Ctx72

variable {T L V : Subgroup G} {l₀ : G} (C : Ctx72 G T L V l₀)
include C

theorem v_le_centerOf : V ≤ centerOf (sL T L V) :=
  (le_sup_left.trans (le_conjClosure _ _)).trans C.le_centerOf

theorem sL_le_normalizer : sL T L V ≤ Subgroup.normalizer (V : Set G) := by
  intro s hs
  rw [Subgroup.mem_normalizer_iff]
  intro v
  have hc : ∀ w ∈ V, s * w = w * s := fun w hw =>
    Subgroup.mem_centralizer_iff.mp (Subgroup.mem_inf.mp (C.v_le_centerOf hw)).2 s hs
  constructor
  · intro hv
    rwa [hc v hv, mul_inv_cancel_right]
  · intro hv
    have h1 := hc _ hv
    have h3 : s * v * s⁻¹ = v := by
      have h2 : s * (s * v * s⁻¹) = s * v := by rw [h1]; group
      exact mul_left_cancel h2
    rwa [h3] at hv

theorem l1_le_normalizer : L₁Of L (fsuV1 T V) ≤ Subgroup.normalizer (fsuU T V : Set G) := by
  intro x hx
  exact le_normalizer_conjClosure V _ (by
    rw [normalizer_eq_centralizer_of_card_two (C.hMod G T L V C.hyp.hyp C.hyp.fsu).2.2.2.1]
    exact oTwoUpper_le _ (l1_le_kz C.hyp C.hMod hx))

theorem commutator_le_v (hu0 : u0 T V = fsuV1 T V) : ⁅sL T L V, sL T L V⁆ ≤ V := by
  have h := C.commutator_eq.2.2
  rwa [C.eq.1, sup_u0_eq_of hu0] at h

theorem comm_mem (hu0 : u0 T V = fsuV1 T V) {a b : G} (ha : a ∈ sL T L V)
    (hb : b ∈ sL T L V) : a * b * a⁻¹ * b⁻¹ ∈ V := by
  have := C.commutator_le_v hu0 (Subgroup.commutator_mem_commutator ha hb)
  rwa [commutatorElement_def] at this

theorem sq_mem (hu0 : u0 T V = fsuV1 T V) {a : G} (ha : a ∈ sL T L V) : a ^ 2 ∈ V := by
  have hUe := isElemAbelian_fsuU_of C.hyp C.hMod
  refine C.commutator_le_v hu0
    (sq_mem_commutator_closure (X := {x | ∃ h ∈ L, ∃ z ∈ fsuU T V, h * z * h⁻¹ = x}) ?_ ha)
  rintro _ ⟨l, -, u, hu, rfl⟩
  rw [conj_pow, F7.isElemAbelian_pow_eq_one hUe hu]
  group

theorem relIndex_v (hu0 : u0 T V = fsuV1 T V) : V.relIndex (fsuU T V) = 4 := by
  have h := (relIndex_sup_u0 C.hyp C.hMod C.h63 C.hF).2
  rwa [sup_u0_eq_of hu0] at h

theorem exists_mem_fsuU (hu0 : u0 T V = fsuV1 T V) : ∃ u ∈ fsuU T V, u ∉ V := by
  by_contra h
  push Not at h
  have := C.relIndex_v hu0
  rw [Subgroup.relIndex_eq_one.mpr h] at this
  norm_num at this

theorem comm_not_mem (hu0 : u0 T V = fsuV1 T V) {x : G} (hxL1 : x ∈ L₁Of L (fsuV1 T V))
    (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1) {u : G} (hu : u ∈ fsuU T V) (huV : u ∉ V) :
    x * u * x⁻¹ * u⁻¹ ∉ V := fun h => huV (by
  have := mem_sup_u0_of_comm C.hyp C.hMod C.h63 hxL1 hx3 hx1 hu (by rwa [sup_u0_eq_of hu0])
  rwa [sup_u0_eq_of hu0] at this)

theorem commutator_fsuU_le_v (hu0 : u0 T V = fsuV1 T V) :
    ⁅fsuU T V, pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T)⁆ ≤ V := by
  have h := commutator_le_sup_u0 C.hyp C.hMod C.h63 C.hF C.h1222 C.h1332 C.h1334
  rwa [sup_u0_eq_of hu0] at h

theorem centralizer_le_pCoreOf : L ⊓ Subgroup.centralizer (V : Set G) ≤
    pCoreOf 2 (L₁Of L (fsuV1 T V) ⊔ T) := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  obtain ⟨V₂, hV2⟩ := C.hyp.exists_V2 C.h13322 C.hMod C.h1222
  have : IsMulCommutative ↥V := (C.hMod G T L V C.hyp.hyp C.hyp.fsu).1.1
  have S14 := C.hyp.set14 C.h1222 C.h1332 C.h1334 hV2
  obtain ⟨-, -, hLTV, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hXp : IsPGroup 2 ↥((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G)) := S14.isPGroup_cent_sup
  have hXn : L ⊔ T ≤ Subgroup.normalizer
      (((L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) : Subgroup G) : Set G) :=
    le_normalizer_of_conj_mem' fun g hg x hx => Subgroup.mem_inf.mpr
      ⟨mul_mem (mul_mem hg (Subgroup.mem_inf.mp hx).1) (inv_mem hg),
        conj_mem_centralizer_of_mem_normalizer (hLTV hg) (Subgroup.mem_inf.mp hx).2⟩
  have hXQ : (L ⊔ T) ⊓ Subgroup.centralizer (V : Set G) ≤ pCoreOf 2 (L ⊔ T) :=
    le_pCoreOf_of_le_normalizer 2 inf_le_left hXn hXp
  have hXT := hXQ.trans (pCoreOf_sup_le C.hyp)
  have hL1T : L₁Of L (fsuV1 T V) ⊔ T ≤ L ⊔ T :=
    sup_le_sup_right (L32NSet14.Setting.L1_le.trans inf_le_left) T
  exact (inf_le_inf_right _ le_sup_left).trans
    (le_pCoreOf_of_le_normalizer 2 (hXT.trans le_sup_right) (hL1T.trans hXn) hXp)

theorem comm_mem_of_mem_centralizer (hu0 : u0 T V = fsuV1 T V) {l : G} (hl : l ∈ L)
    (hlV : l ∈ Subgroup.centralizer (V : Set G)) {s : G} (hs : s ∈ sL T L V) :
    l * s * l⁻¹ * s⁻¹ ∈ V := by
  obtain ⟨-, -, hLTV, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hR1 := C.commutator_fsuU_le_v hu0
  have hcent := C.centralizer_le_pCoreOf
  have hSV := C.sL_le_normalizer
  have hS : s ∈ Subgroup.closure {x | ∃ h ∈ L, ∃ z ∈ fsuU T V, h * z * h⁻¹ = x} := hs
  clear hs
  induction hS using Subgroup.closure_induction with
  | mem x hx =>
    obtain ⟨k, hk, u, hu, rfl⟩ := hx
    have hkV : k ∈ Subgroup.normalizer (V : Set G) := hLTV (Subgroup.mem_sup_left hk)
    have hl' : k⁻¹ * l * k ∈ L ⊓ Subgroup.centralizer (V : Set G) := by
      refine Subgroup.mem_inf.mpr ⟨mul_mem (mul_mem (inv_mem hk) hl) hk, ?_⟩
      have := conj_mem_centralizer_of_mem_normalizer (inv_mem hkV) hlV
      simpa using this
    have h1 := hR1 (Subgroup.commutator_mem_commutator hu (hcent hl'))
    rw [commutatorElement_def] at h1
    have h2 := (Subgroup.mem_normalizer_iff.mp hkV _).mp (inv_mem h1)
    convert h2 using 1
    group
  | one => simp
  | mul a b ha hb iha ihb =>
    have haV := hSV ha
    rw [show l * (a * b) * l⁻¹ * (a * b)⁻¹ =
      (l * a * l⁻¹ * a⁻¹) * (a * (l * b * l⁻¹ * b⁻¹) * a⁻¹) by group]
    exact mul_mem iha ((Subgroup.mem_normalizer_iff.mp haV _).mp ihb)
  | inv a ha iha =>
    have haV := hSV ha
    rw [show l * a⁻¹ * l⁻¹ * a⁻¹⁻¹ = a⁻¹ * (l * a * l⁻¹ * a⁻¹)⁻¹ * a⁻¹⁻¹ by group]
    exact (Subgroup.mem_normalizer_iff.mp (inv_mem haV) _).mp (inv_mem iha)

theorem mem_centralizer_of_comm_mem (hu0 : u0 T V = fsuV1 T V) {l : G} (hl : l ∈ L)
    (hlS : ∀ s ∈ sL T L V, l * s * l⁻¹ * s⁻¹ ∈ V) : l ∈ Subgroup.centralizer (V : Set G) := by
  by_contra hlV
  obtain ⟨-, -, hLTV, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hN : L ⊓ L32NSet14.trivSub (sL T L V) V = L := by
    refine normal_eq_of_not_mem_centralizer C.hyp C.h13322 C.hMod C.h1222 C.h1332 C.h1334
      inf_le_left (fun k hk n hn => Subgroup.mem_inf.mpr ⟨?_, ?_⟩)
      (Subgroup.mem_inf.mpr ⟨hl, le_normalizer_conjClosure _ _ hl,
        hLTV (Subgroup.mem_sup_left hl), hlS⟩) hlV
    · exact mul_mem (mul_mem hk (Subgroup.mem_inf.mp hn).1) (inv_mem hk)
    · exact L32NSet14.conj_mem_trivSub (le_normalizer_conjClosure _ _ hk)
        (hLTV (Subgroup.mem_sup_left hk)) (Subgroup.mem_inf.mp hn).2
  obtain ⟨x, hxL1, hx3, hx1, -⟩ := C.exists_x3
  have hxL : x ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hxL1
  obtain ⟨u, hu, huV⟩ := C.exists_mem_fsuU hu0
  rw [← hN] at hxL
  exact C.comm_not_mem hu0 hxL1 hx3 hx1 hu huV
    (((Subgroup.mem_inf.mp hxL).2).2.2 u (le_conjClosure _ _ hu))

theorem fsuU_le_of_mem (hu0 : u0 T V = fsuV1 T V) {D : Subgroup G} (hVD : V ≤ D) {m : G}
    (hmU : m ∈ fsuU T V) (hmV : m ∉ V) (hmD : m ∈ D) {x : G}
    (hxL1 : x ∈ L₁Of L (fsuV1 T V)) (hx3 : x ^ 3 = 1) (hx1 : x ≠ 1)
    (hxD : x * m * x⁻¹ ∈ D) : fsuU T V ≤ D := by
  obtain ⟨-, -, hLTV, -, -⟩ := C.hMod G T L V C.hyp.hyp C.hyp.fsu
  have hUe := isElemAbelian_fsuU_of C.hyp C.hMod
  have h4 := C.relIndex_v hu0
  have hle : V ≤ D ⊓ fsuU T V := le_inf hVD v_le_fsuU
  have hmul := Subgroup.relIndex_mul_relIndex V (D ⊓ fsuU T V) (fsuU T V) hle inf_le_right
  rw [h4] at hmul
  have hdvd : V.relIndex (D ⊓ fsuU T V) ∣ 4 := Dvd.intro _ hmul
  have hcases : V.relIndex (D ⊓ fsuU T V) = 1 ∨ V.relIndex (D ⊓ fsuU T V) = 2 ∨
      V.relIndex (D ⊓ fsuU T V) = 4 := by
    have : V.relIndex (D ⊓ fsuU T V) ∈ Nat.divisors 4 :=
      Nat.mem_divisors.mpr ⟨hdvd, by norm_num⟩
    rw [show Nat.divisors 4 = {1, 2, 4} by decide] at this
    simpa using this
  have hxU : x * m * x⁻¹ ∈ fsuU T V :=
    (Subgroup.mem_normalizer_iff.mp (C.l1_le_normalizer hxL1) m).mp hmU
  have hxL : x ∈ L := (L32NSet14.Setting.L1_le.trans inf_le_left) hxL1
  have hxmV : x * m * x⁻¹ ∉ V := fun h =>
    hmV ((Subgroup.mem_normalizer_iff.mp (hLTV (Subgroup.mem_sup_left hxL)) m).mpr h)
  rcases hcases with h1 | h2 | h4'
  · exact absurd (Subgroup.relIndex_eq_one.mp h1 (Subgroup.mem_inf.mpr ⟨hmD, hmU⟩)) hmV
  · exfalso
    have hcard : Nat.card ↥(D ⊓ fsuU T V) = 2 * Nat.card ↥V := by
      have := Subgroup.relIndex_mul_card V (D ⊓ fsuU T V)
      rw [inf_eq_left.mpr hle, h2] at this
      omega
    have hprod := L32NSet14.mul_mem_of_card_eq_two_mul hle hcard Nat.card_pos.ne'
      (Subgroup.mem_inf.mpr ⟨hxD, hxU⟩) (Subgroup.mem_inf.mpr ⟨hmD, hmU⟩) hxmV hmV
    have hm2 : m * m = 1 := by
      rw [← pow_two]
      exact F7.isElemAbelian_pow_eq_one hUe hmU
    apply C.comm_not_mem hu0 hxL1 hx3 hx1 hmU hmV
    rwa [inv_eq_of_mul_eq_one_right hm2]
  · have h1 : (D ⊓ fsuU T V).relIndex (fsuU T V) = 1 := by
      rw [h4'] at hmul
      omega
    exact (Subgroup.relIndex_eq_one.mp h1).trans inf_le_left

end Ctx72

end CFSG.Quasithin.H13.L32A
