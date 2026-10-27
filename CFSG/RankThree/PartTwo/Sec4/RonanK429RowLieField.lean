module

public import CFSG.LocalAnalysis.ComponentClassification.OutcomeLocalCTILinearSocleField
public import CFSG.RankThree.PartTwo.Sec21.Item211Lie2ProofL3Plus
public import CFSG.RankThree.PartTwo.Sec4.Item424Res3ProofUniFix

public section

namespace CFSG.RankThree.PartTwo.Sec4.RonanK429Lie

open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
open CFSG.ClassicalGroups.UnitaryFlag CFSG.RankThree.PartTwo.KFacts
open CFSG.GH74.GLS.IVK (fixedField fixedField_apply mem_fixedField_iff)
open Matrix
open scoped commutatorElement

section Group

variable {G : Type*} [Group G]

theorem commutator_mul_central {a b z w : G} (hz : ∀ g, g * z = z * g)
    (hw : ∀ g, g * w = w * g) : ⁅a * z, b * w⁆ = ⁅a, b⁆ := by
  rw [commutatorElement_def, commutatorElement_def]
  have h1 : a * z * (b * w) * (a * z)⁻¹ * (b * w)⁻¹ =
      a * (z * (b * w)) * z⁻¹ * a⁻¹ * (b * w)⁻¹ := by group
  rw [h1, ← hz (b * w)]
  have h2 : a * (b * w * z) * z⁻¹ * a⁻¹ * (b * w)⁻¹ = a * b * (w * a⁻¹) * w⁻¹ * b⁻¹ := by group
  rw [h2, ← hw a⁻¹]
  group

theorem eq_of_subnormal_of_le_simple {K P C : Subgroup G} (hKP : K ≤ P) (hPC : P ≤ C)
    (hsub : (K.subgroupOf C).IsSubnormal) (hP : IsSimpleGroup P) (hnt : K ≠ ⊥) : K = P := by
  have hsP : (K.subgroupOf P).IsSubnormal := by
    have h := hsub.comap (Subgroup.inclusion hPC)
    have heq : (K.subgroupOf C).comap (Subgroup.inclusion hPC) = K.subgroupOf P := by
      ext x
      simp [Subgroup.mem_subgroupOf]
    rwa [heq] at h
  rcases hsP.eq_bot_or_top_of_isSimpleGroup hP with h | h
  · exfalso
    apply hnt
    rw [eq_bot_iff]
    intro x hx
    have hxP : (⟨x, hKP hx⟩ : P) ∈ K.subgroupOf P := hx
    rw [h, Subgroup.mem_bot] at hxP
    exact (Subgroup.mem_bot).mpr (congrArg Subtype.val hxP)
  · exact le_antisymm hKP (Subgroup.subgroupOf_eq_top.mp h)

@[expose] noncomputable def comapEquiv {H : Type*} [Group H] (τ : G ≃* H) (P : Subgroup H) :
    P.comap τ.toMonoidHom ≃* P :=
  MulEquiv.ofBijective (τ.toMonoidHom.subgroupComap P)
    ⟨fun x y hxy => Subtype.ext (τ.injective (congrArg Subtype.val hxy)),
      fun y => ⟨⟨τ.symm y, by simp⟩, Subtype.ext (τ.apply_symm_apply (y : H))⟩⟩

theorem isSimpleGroup_comap {H : Type*} [Group H] (τ : G ≃* H) {P : Subgroup H}
    (hP : IsSimpleGroup P) : IsSimpleGroup (P.comap τ.toMonoidHom) :=
  (comapEquiv τ P).isSimpleGroup

theorem pCore_two_eq_bot_of_cube_mem {C J : Subgroup G} (hJC : J ≤ C) (hJ : IsSimpleGroup J)
    (h3 : ∃ k ∈ J, k ≠ 1 ∧ k ^ 3 = 1) (hcube : ∀ x ∈ C, x ^ 3 ∈ J) :
    CFSG.pCore 2 C = ⊥ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set N : Subgroup C := CFSG.pCore 2 C with hNdef
  haveI hNn : N.Normal := CFSG.pCore_normal
  have hN2 : IsPGroup 2 N := CFSG.pCore_isPGroup
  have key : ∀ y ∈ N, y ^ 3 = 1 → y = 1 := by
    intro y hy hy3
    obtain ⟨j, hj⟩ := hN2 ⟨y, hy⟩
    have hj' : y ^ 2 ^ j = 1 := by simpa using congrArg Subtype.val hj
    have hd : orderOf y ∣ Nat.gcd 3 (2 ^ j) :=
      Nat.dvd_gcd (orderOf_dvd_of_pow_eq_one hy3) (orderOf_dvd_of_pow_eq_one hj')
    have hg : Nat.gcd 3 (2 ^ j) = 1 :=
      Nat.Coprime.pow_right j (by norm_num : Nat.Coprime 3 2)
    rw [hg, Nat.dvd_one, orderOf_eq_one_iff] at hd
    exact hd
  set M : Subgroup J := N.comap (Subgroup.inclusion hJC) with hM
  haveI : M.Normal := hNn.comap _
  haveI := hJ
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal M with hbot | htop
  · rw [eq_bot_iff]
    intro y hy
    have hy3 : (y : G) ^ 3 ∈ J := hcube y y.2
    have hm : (⟨(y : G) ^ 3, hy3⟩ : J) ∈ M := by
      show Subgroup.inclusion hJC ⟨(y : G) ^ 3, hy3⟩ ∈ N
      have : Subgroup.inclusion hJC ⟨(y : G) ^ 3, hy3⟩ = y ^ 3 := Subtype.ext (by simp)
      rw [this]
      exact pow_mem hy 3
    rw [hbot, Subgroup.mem_bot] at hm
    have hy1 : y ^ 3 = 1 := Subtype.ext (by simpa using congrArg Subtype.val hm)
    rw [Subgroup.mem_bot]
    exact key y hy hy1
  · exfalso
    obtain ⟨k, hkJ, hk1, hk3⟩ := h3
    have hkM : (⟨k, hkJ⟩ : J) ∈ M := htop ▸ Subgroup.mem_top _
    have hkN : (⟨k, hJC hkJ⟩ : C) ∈ N := hkM
    have := key _ hkN (Subtype.ext (by simpa using hk3))
    exact hk1 (by simpa using congrArg Subtype.val this)

end Group

section Linear

variable {K : Type} [Field K]

@[expose] noncomputable def linFix (φ : K ≃+* K) :
    SpecialLinearGroup (Fin 3) (fixedField φ) →* projectiveSL 3 K :=
  (proj 3 K).comp (SpecialLinearGroup.map (fixedField φ).subtype)

theorem linFix_fixed (φ : K ≃+* K) (g₀ : SpecialLinearGroup (Fin 3) (fixedField φ)) :
    fieldAut 3 K φ (linFix φ g₀) = linFix φ g₀ := by
  rw [linFix, MonoidHom.comp_apply, fieldAut_proj]
  congr 1
  ext i j
  exact fixedField_apply φ _

theorem commutator_mem_range_linFix (φ : K ≃+* K) {x y : projectiveSL 3 K}
    (hx : fieldAut 3 K φ x = x) (hy : fieldAut 3 K φ y = y) : ⁅x, y⁆ ∈ (linFix φ).range := by
  obtain ⟨g, rfl⟩ := proj_surjective 3 K x
  obtain ⟨h, rfl⟩ := proj_surjective 3 K y
  rw [fieldAut_proj, proj_eq_proj_iff] at hx hy
  set a := SpecialLinearGroup.map φ.toRingHom g with ha
  set b := SpecialLinearGroup.map φ.toRingHom h with hb
  have hz : ∀ t, t * (a⁻¹ * g) = (a⁻¹ * g) * t := fun t =>
    (Subgroup.mem_center_iff.mp (scalars_le_center 3 K hx) t)
  have hw : ∀ t, t * (b⁻¹ * h) = (b⁻¹ * h) * t := fun t =>
    (Subgroup.mem_center_iff.mp (scalars_le_center 3 K hy) t)
  have hfix : SpecialLinearGroup.map φ.toRingHom ⁅g, h⁆ = ⁅g, h⁆ := by
    rw [map_commutatorElement, ← ha, ← hb]
    calc ⁅a, b⁆ = ⁅a * (a⁻¹ * g), b * (b⁻¹ * h)⁆ := (commutator_mul_central hz hw).symm
      _ = ⁅g, h⁆ := by rw [mul_inv_cancel_left, mul_inv_cancel_left]
  obtain ⟨A₀, hA₀⟩ := exists_sl_map_subtype_eq hfix
  exact ⟨A₀, by rw [linFix, MonoidHom.comp_apply, hA₀, map_commutatorElement]⟩

theorem pow_three_mem_range_linFix (φ : K ≃+* K) {x : projectiveSL 3 K}
    (hx : fieldAut 3 K φ x = x) : x ^ 3 ∈ (linFix φ).range := by
  obtain ⟨g, rfl⟩ := proj_surjective 3 K x
  rw [fieldAut_proj, proj_eq_proj_iff] at hx
  set a := SpecialLinearGroup.map φ.toRingHom g with ha
  have hzc : ∀ t, t * (a⁻¹ * g) = (a⁻¹ * g) * t := fun t =>
    (Subgroup.mem_center_iff.mp (scalars_le_center 3 K hx) t)
  obtain ⟨c, hc, hcz⟩ := hx
  have hz3 : (a⁻¹ * g) ^ 3 = 1 := by
    ext i j
    rw [Matrix.SpecialLinearGroup.coe_pow, hcz, ← map_pow, ← Units.val_pow_eq_pow_val, hc,
      Units.val_one, map_one, Matrix.SpecialLinearGroup.coe_one]
  have hfix : SpecialLinearGroup.map φ.toRingHom (g ^ 3) = g ^ 3 := by
    rw [map_pow, ← ha]
    calc a ^ 3 = a ^ 3 * (a⁻¹ * g) ^ 3 := by rw [hz3, mul_one]
      _ = (a * (a⁻¹ * g)) ^ 3 := ((Commute.mul_pow (hzc a) 3)).symm
      _ = g ^ 3 := by rw [mul_inv_cancel_left]
  obtain ⟨A₀, hA₀⟩ := exists_sl_map_subtype_eq hfix
  exact ⟨A₀, by rw [linFix, MonoidHom.comp_apply, hA₀, map_pow]⟩

theorem ker_linFix (φ : K ≃+* K) : (linFix φ).ker = scalars 3 (fixedField φ) := by
  ext g₀
  rw [MonoidHom.mem_ker, linFix, MonoidHom.comp_apply, proj_eq_one_iff]
  constructor
  · intro hg
    rw [scalars_eq_center, Subgroup.mem_center_iff]
    intro t
    apply sl_map_subtype_injective φ
    rw [map_mul, map_mul]
    exact Subgroup.mem_center_iff.mp (scalars_le_center 3 K hg) _
  · rintro ⟨c, hc, hgc⟩
    refine ⟨Units.map (fixedField φ).subtype.toMonoidHom c, ?_, ?_⟩
    · rw [← map_pow, hc, map_one]
    · ext i j
      rw [SpecialLinearGroup.map_apply_coe, RingHom.mapMatrix_apply, Matrix.map_apply, hgc]
      simp only [Matrix.scalar_apply, Matrix.diagonal_apply, Units.coe_map,
        MonoidHom.coe_coe]
      split_ifs <;> simp

@[expose] noncomputable def linFixEquiv (φ : K ≃+* K) :
    projectiveSL 3 (fixedField φ) ≃* (linFix φ).range :=
  (QuotientGroup.quotientMulEquivOfEq (ker_linFix φ)).symm.trans
    (QuotientGroup.quotientKerEquivRange (linFix φ))

theorem isSimpleGroup_range_linFix (φ : K ≃+* K) : IsSimpleGroup (linFix φ).range := by
  haveI := CFSG.ComponentClassification.OutcomeLocal.isSimpleGroup_projectiveSL
    (k := fixedField φ) (n := 3) le_rfl
  exact (linFixEquiv φ).symm.isSimpleGroup

theorem eq_comap_range_linFix {S : Type*} [Group S] (τ : S ≃* projectiveSL 3 K)
    {σ : MulAut S} {φ : K ≃+* K} (hστ : MulAut.congr τ σ = fieldAut 3 K φ)
    {C J : Subgroup S} (hC : ∀ x, x ∈ C ↔ σ x = x) (hJC : J ≤ C) [Group.IsPerfect J]
    (hnt : J ≠ ⊥) (hsub : (J.subgroupOf C).IsSubnormal) :
    J = (linFix φ).range.comap τ.toMonoidHom := by
  have hfixτ : ∀ x : S, σ x = x → fieldAut 3 K φ (τ x) = τ x := by
    intro x hx
    rw [← hστ]
    show τ (σ (τ.symm (τ x))) = τ x
    rw [MulEquiv.symm_apply_apply, hx]
  refine eq_of_subnormal_of_le_simple ?_ ?_ hsub
    (isSimpleGroup_comap τ (isSimpleGroup_range_linFix φ)) hnt
  · rw [← Subgroup.commutator_eq_self (H := J), Subgroup.commutator_le]
    intro a ha b hb
    show τ ⁅a, b⁆ ∈ (linFix φ).range
    rw [map_commutatorElement]
    exact commutator_mem_range_linFix φ (hfixτ a ((hC a).mp (hJC ha)))
      (hfixτ b ((hC b).mp (hJC hb)))
  · rintro x ⟨g₀, hg₀⟩
    rw [hC]
    have h1 : fieldAut 3 K φ (τ x) = τ x := by
      change fieldAut 3 K φ (τ x) = τ x
      rw [← show linFix φ g₀ = τ x from hg₀]
      exact linFix_fixed φ g₀
    rw [← hστ] at h1
    change τ (σ (τ.symm (τ x))) = τ x at h1
    rw [MulEquiv.symm_apply_apply] at h1
    exact τ.injective h1

theorem nonempty_mulEquiv_linFix {S : Type*} [Group S] (τ : S ≃* projectiveSL 3 K)
    {σ : MulAut S} {φ : K ≃+* K} (hστ : MulAut.congr τ σ = fieldAut 3 K φ)
    {C J : Subgroup S} (hC : ∀ x, x ∈ C ↔ σ x = x) (hJC : J ≤ C) [Group.IsPerfect J]
    (hnt : J ≠ ⊥) (hsub : (J.subgroupOf C).IsSubnormal) :
    Nonempty (J ≃* projectiveSL 3 (fixedField φ)) := by
  have hJ := eq_comap_range_linFix τ hστ hC hJC hnt hsub
  exact ⟨((MulEquiv.subgroupCongr hJ).trans (comapEquiv τ (linFix φ).range)).trans
    (linFixEquiv φ).symm⟩

theorem fieldCase_linear {S : Type*} [Group S] (τ : S ≃* projectiveSL 3 K)
    {σ : MulAut S} {φ : K ≃+* K} (hστ : MulAut.congr τ σ = fieldAut 3 K φ)
    {C J : Subgroup S} (hC : ∀ x, x ∈ C ↔ σ x = x) (hJC : J ≤ C) [Group.IsPerfect J]
    (hnt : J ≠ ⊥) (hsub : (J.subgroupOf C).IsSubnormal) (h3 : ∃ k ∈ J, k ≠ 1 ∧ k ^ 3 = 1) :
    Nonempty (J ≃* projectiveSL 3 (fixedField φ)) ∧ CFSG.pCore 2 C = ⊥ := by
  refine ⟨nonempty_mulEquiv_linFix τ hστ hC hJC hnt hsub, ?_⟩
  have hJ := eq_comap_range_linFix τ hστ hC hJC hnt hsub
  have hJs : IsSimpleGroup J := by
    rw [hJ]
    exact isSimpleGroup_comap τ (isSimpleGroup_range_linFix φ)
  refine pCore_two_eq_bot_of_cube_mem hJC hJs h3 fun x hx => ?_
  rw [hJ]
  show τ (x ^ 3) ∈ (linFix φ).range
  rw [map_pow]
  refine pow_three_mem_range_linFix φ ?_
  rw [← hστ]
  show τ (σ (τ.symm (τ x))) = τ x
  rw [MulEquiv.symm_apply_apply, (hC x).mp hx]

end Linear

section Unitary

variable {p f : ℕ} {K : Type} [Field K] (h : UnitaryFieldData p f K) {σ : K ≃+* K} {f₀ : ℕ}
  (h₀ : UnitaryFieldData p f₀ (fixedField σ))
  (hbar : ∀ x : fixedField σ, h.bar (x : K) = ((h₀.bar x : fixedField σ) : K))

@[expose] noncomputable def uniFix : unitarySU p f₀ (fixedField σ) 3 →* unitaryPSU h 3 :=
  (unitaryProj h 3).comp (suIncl h h₀ hbar)

theorem mem_center_of_mem_unitaryScalars {z : unitarySU p f K 3} (hz : z ∈ unitaryScalars h 3) :
    z ∈ Subgroup.center (unitarySU p f K 3) := by
  obtain ⟨c, -, -, hzc⟩ := hz
  rw [Subgroup.mem_center_iff]
  intro t
  apply Subtype.ext
  rw [Subgroup.coe_mul, Subgroup.coe_mul, hzc]
  exact (commute_scalar c _).eq

theorem uniFix_fixed (g₀ : unitarySU p f₀ (fixedField σ) 3) :
    psuField h σ (uniFix h h₀ hbar g₀) = uniFix h h₀ hbar g₀ := by
  rw [uniFix, MonoidHom.comp_apply]
  have hfix := (mem_range_suIncl_iff h h₀ hbar (suIncl h h₀ hbar g₀)).mp ⟨g₀, rfl⟩
  exact (psuField_mk σ _).trans (congrArg (unitaryProj h 3) hfix)

theorem commutator_mem_range_uniFix {x y : unitaryPSU h 3} (hx : psuField h σ x = x)
    (hy : psuField h σ y = y) : ⁅x, y⁆ ∈ (uniFix h h₀ hbar).range := by
  obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 x
  obtain ⟨g', rfl⟩ := unitaryProj_surjective h 3 y
  have hx' : (suField h σ g)⁻¹ * g ∈ unitaryScalars h 3 := by
    have := (psuField_mk σ g).symm.trans hx
    exact QuotientGroup.eq.mp this
  have hy' : (suField h σ g')⁻¹ * g' ∈ unitaryScalars h 3 := by
    have := (psuField_mk σ g').symm.trans hy
    exact QuotientGroup.eq.mp this
  set a := suField h σ g with ha
  set b := suField h σ g' with hb
  have hz : ∀ t, t * (a⁻¹ * g) = (a⁻¹ * g) * t := fun t =>
    Subgroup.mem_center_iff.mp (mem_center_of_mem_unitaryScalars h hx') t
  have hw : ∀ t, t * (b⁻¹ * g') = (b⁻¹ * g') * t := fun t =>
    Subgroup.mem_center_iff.mp (mem_center_of_mem_unitaryScalars h hy') t
  have hfix : suField h σ ⁅g, g'⁆ = ⁅g, g'⁆ := by
    rw [map_commutatorElement, ← ha, ← hb]
    calc ⁅a, b⁆ = ⁅a * (a⁻¹ * g), b * (b⁻¹ * g')⁆ := (commutator_mul_central hz hw).symm
      _ = ⁅g, g'⁆ := by rw [mul_inv_cancel_left, mul_inv_cancel_left]
  obtain ⟨g₀, hg₀⟩ := (mem_range_suIncl_iff h h₀ hbar ⁅g, g'⁆).mpr hfix
  exact ⟨g₀, by rw [uniFix, MonoidHom.comp_apply, hg₀, map_commutatorElement]⟩

theorem pow_three_mem_range_uniFix {x : unitaryPSU h 3} (hx : psuField h σ x = x) :
    x ^ 3 ∈ (uniFix h h₀ hbar).range := by
  obtain ⟨g, rfl⟩ := unitaryProj_surjective h 3 x
  have hx' : (suField h σ g)⁻¹ * g ∈ unitaryScalars h 3 := by
    have := (psuField_mk σ g).symm.trans hx
    exact QuotientGroup.eq.mp this
  set a := suField h σ g with ha
  have hzc : ∀ t, t * (a⁻¹ * g) = (a⁻¹ * g) * t := fun t =>
    Subgroup.mem_center_iff.mp (mem_center_of_mem_unitaryScalars h hx') t
  obtain ⟨c, -, hc3, hcz⟩ := hx'
  have hz3 : (a⁻¹ * g) ^ 3 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, hcz, ← map_pow, hc3, map_one, Subgroup.coe_one]
  have hfix : suField h σ (g ^ 3) = g ^ 3 := by
    rw [map_pow, ← ha]
    calc a ^ 3 = a ^ 3 * (a⁻¹ * g) ^ 3 := by rw [hz3, mul_one]
      _ = (a * (a⁻¹ * g)) ^ 3 := ((Commute.mul_pow (hzc a) 3)).symm
      _ = g ^ 3 := by rw [mul_inv_cancel_left]
  obtain ⟨g₀, hg₀⟩ := (mem_range_suIncl_iff h h₀ hbar (g ^ 3)).mpr hfix
  exact ⟨g₀, by rw [uniFix, MonoidHom.comp_apply, hg₀, map_pow]⟩

theorem ker_uniFix_le_center :
    (uniFix h h₀ hbar).ker ≤ Subgroup.center (unitarySU p f₀ (fixedField σ) 3) := by
  intro g₀ hg₀
  rw [MonoidHom.mem_ker, uniFix, MonoidHom.comp_apply] at hg₀
  have hz : suIncl h h₀ hbar g₀ ∈ unitaryScalars h 3 := by
    rw [← ker_unitaryProj h 3]
    exact hg₀
  have hc := mem_center_of_mem_unitaryScalars h hz
  rw [Subgroup.mem_center_iff] at hc ⊢
  intro t
  apply suIncl_injective h h₀ hbar
  rw [map_mul, map_mul]
  exact hc _

theorem ker_uniFix (hq₀ : 2 < p ^ f₀) :
    (uniFix h h₀ hbar).ker = Subgroup.center (unitarySU p f₀ (fixedField σ) 3) := by
  refine le_antisymm (ker_uniFix_le_center h h₀ hbar) ?_
  intro g₀ hg₀
  rw [center_unitarySU_three (h := h₀) hq₀] at hg₀
  obtain ⟨c, hcn, hc3, hgc⟩ := hg₀
  rw [MonoidHom.mem_ker, uniFix, MonoidHom.comp_apply, ← MonoidHom.mem_ker, ker_unitaryProj]
  refine ⟨Units.map (fixedField σ).subtype.toMonoidHom c, ?_, ?_, ?_⟩
  · rw [Units.coe_map]
    change (c : fixedField σ).1 * h.bar ((c : fixedField σ) : K) = 1
    rw [hbar]
    have := congrArg Subtype.val hcn
    simpa [UnitaryFieldData.norm] using this
  · rw [← map_pow, hc3, map_one]
  · apply Units.ext
    ext i j
    rw [coe_suIncl_apply, hgc]
    simp only [Matrix.GeneralLinearGroup.coe_scalar, Matrix.scalar_apply,
      Matrix.diagonal_apply, Units.coe_map, MonoidHom.coe_coe]
    split_ifs <;> simp

@[expose] noncomputable def uniFixEquiv (hq₀ : 2 < p ^ f₀) :
    unitaryPSU h₀ 3 ≃* (uniFix h h₀ hbar).range :=
  (QuotientGroup.quotientMulEquivOfEq ((ker_uniFix h h₀ hbar hq₀).trans
      (center_unitarySU_three (h := h₀) hq₀))).symm.trans
    (QuotientGroup.quotientKerEquivRange (uniFix h h₀ hbar))

theorem isSimpleGroup_range_uniFix (hq₀ : 2 < p ^ f₀) : IsSimpleGroup (uniFix h h₀ hbar).range := by
  haveI := CFSG.RankThree.PartTwo.Sec21.Item211Lie2Proof.isSimpleGroup_unitaryPSU_three
    (h := h₀) hq₀
  exact (uniFixEquiv h h₀ hbar hq₀).symm.isSimpleGroup

theorem isSolvable_range_uniFix (hq₀ : p ^ f₀ = 2) : Group.IsSolvable (uniFix h h₀ hbar).range := by
  haveI := CFSG.RankThree.PartTwo.Sec4.Item424Res3.isSolvable_unitarySU_two h₀ hq₀
  exact Group.isSolvable_of_surjective (f := (uniFix h h₀ hbar).rangeRestrict)
    (MonoidHom.rangeRestrict_surjective (uniFix h h₀ hbar))

variable {h}

theorem comap_range_uniFix_facts {S : Type*} [Group S] (τ : S ≃* unitaryPSU h 3)
    {α : MulAut S} (hστ : MulAut.congr τ α = psuField h σ)
    {C J : Subgroup S} (hC : ∀ x, x ∈ C ↔ α x = x) (hJC : J ≤ C) [Group.IsPerfect J] :
    J ≤ (uniFix h h₀ hbar).range.comap τ.toMonoidHom ∧
      (uniFix h h₀ hbar).range.comap τ.toMonoidHom ≤ C := by
  have hfixτ : ∀ x : S, α x = x → psuField h σ (τ x) = τ x := by
    intro x hx
    rw [← hστ]
    show τ (α (τ.symm (τ x))) = τ x
    rw [MulEquiv.symm_apply_apply, hx]
  refine ⟨?_, ?_⟩
  · rw [← Subgroup.commutator_eq_self (H := J), Subgroup.commutator_le]
    intro a ha b hb
    show τ ⁅a, b⁆ ∈ (uniFix h h₀ hbar).range
    rw [map_commutatorElement]
    exact commutator_mem_range_uniFix h h₀ hbar (hfixτ a ((hC a).mp (hJC ha)))
      (hfixτ b ((hC b).mp (hJC hb)))
  · rintro x ⟨g₀, hg₀⟩
    rw [hC]
    have h1 : psuField h σ (τ x) = τ x := by
      change psuField h σ (τ x) = τ x
      rw [← show uniFix h h₀ hbar g₀ = τ x from hg₀]
      exact uniFix_fixed h h₀ hbar g₀
    rw [← hστ] at h1
    change τ (α (τ.symm (τ x))) = τ x at h1
    rw [MulEquiv.symm_apply_apply] at h1
    exact τ.injective h1

include hbar in
theorem nonempty_mulEquiv_uniFix {S : Type*} [Group S] (τ : S ≃* unitaryPSU h 3)
    {α : MulAut S} (hστ : MulAut.congr τ α = psuField h σ) (hq₀ : 2 < p ^ f₀)
    {C J : Subgroup S} (hC : ∀ x, x ∈ C ↔ α x = x) (hJC : J ≤ C) [Group.IsPerfect J]
    (hnt : J ≠ ⊥) (hsub : (J.subgroupOf C).IsSubnormal) :
    Nonempty (J ≃* unitaryPSU h₀ 3) := by
  obtain ⟨hJP, hPC⟩ := comap_range_uniFix_facts (h₀ := h₀) (hbar := hbar) τ hστ hC hJC
  have hJ := eq_of_subnormal_of_le_simple hJP hPC hsub
    (isSimpleGroup_comap τ (isSimpleGroup_range_uniFix h h₀ hbar hq₀)) hnt
  exact ⟨((MulEquiv.subgroupCongr hJ).trans (comapEquiv τ (uniFix h h₀ hbar).range)).trans
    (uniFixEquiv h h₀ hbar hq₀).symm⟩

include hbar in
theorem fieldCase_unitary {S : Type*} [Group S] (τ : S ≃* unitaryPSU h 3)
    {α : MulAut S} (hστ : MulAut.congr τ α = psuField h σ) (hq₀ : 2 < p ^ f₀)
    {C J : Subgroup S} (hC : ∀ x, x ∈ C ↔ α x = x) (hJC : J ≤ C) [Group.IsPerfect J]
    (hnt : J ≠ ⊥) (hsub : (J.subgroupOf C).IsSubnormal) (h3 : ∃ k ∈ J, k ≠ 1 ∧ k ^ 3 = 1) :
    Nonempty (J ≃* unitaryPSU h₀ 3) ∧ CFSG.pCore 2 C = ⊥ := by
  refine ⟨nonempty_mulEquiv_uniFix h₀ hbar τ hστ hq₀ hC hJC hnt hsub, ?_⟩
  obtain ⟨hJP, hPC⟩ := comap_range_uniFix_facts (h₀ := h₀) (hbar := hbar) τ hστ hC hJC
  have hJ := eq_of_subnormal_of_le_simple hJP hPC hsub
    (isSimpleGroup_comap τ (isSimpleGroup_range_uniFix h h₀ hbar hq₀)) hnt
  have hJs : IsSimpleGroup J := by
    rw [hJ]
    exact isSimpleGroup_comap τ (isSimpleGroup_range_uniFix h h₀ hbar hq₀)
  refine pCore_two_eq_bot_of_cube_mem hJC hJs h3 fun x hx => ?_
  rw [hJ]
  show τ (x ^ 3) ∈ (uniFix h h₀ hbar).range
  rw [map_pow]
  refine pow_three_mem_range_uniFix h h₀ hbar ?_
  rw [← hστ]
  show τ (α (τ.symm (τ x))) = τ x
  rw [MulEquiv.symm_apply_apply, (hC x).mp hx]

theorem false_of_uniFix_two (h₀ : UnitaryFieldData p f₀ (fixedField σ))
    (hbar : ∀ x : fixedField σ, h.bar (x : K) = ((h₀.bar x : fixedField σ) : K))
    {S : Type*} [Group S] (τ : S ≃* unitaryPSU h 3)
    {α : MulAut S} (hστ : MulAut.congr τ α = psuField h σ) (hq₀ : p ^ f₀ = 2)
    {C J : Subgroup S} (hC : ∀ x, x ∈ C ↔ α x = x) (hJC : J ≤ C) [Group.IsPerfect J]
    (hnt : J ≠ ⊥) : False := by
  obtain ⟨hJP, -⟩ := comap_range_uniFix_facts (h₀ := h₀) (hbar := hbar) τ hστ hC hJC
  have hsolP : Group.IsSolvable ((uniFix h h₀ hbar).range.comap τ.toMonoidHom) := by
    haveI := isSolvable_range_uniFix h h₀ hbar hq₀
    exact Group.isSolvable_of_surjective (f := (comapEquiv τ (uniFix h h₀ hbar).range).symm.toMonoidHom)
      (comapEquiv τ (uniFix h h₀ hbar).range).symm.surjective
  have hsolJ : Group.IsSolvable J :=
    Group.isSolvable_of_isSolvable_injective (f := Subgroup.inclusion hJP)
      (Subgroup.inclusion_injective hJP)
  haveI : Nontrivial J := (Subgroup.nontrivial_iff_ne_bot J).mpr hnt
  exact Group.IsPerfect.not_isSolvable J hsolJ

end Unitary

end CFSG.RankThree.PartTwo.Sec4.RonanK429Lie
