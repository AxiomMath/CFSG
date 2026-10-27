module

public import CFSG.LocalAnalysis.SteinbergSFSingleCommPrincipalLayersDefs
public import CFSG.CharacterTheory.Semidihedral.OddFieldLift
public import CFSG.LinearAlgebra.LinearGroups.CoordinateData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldArithmetic
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBGraphFieldUnitaryData
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueBHigherLinearFieldDeterminant
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancedCatalogSUFieldOddCore
public import CFSG.LocalAnalysis.ComponentClassification.UnbalancingLocalSmallSourceLinear
public import CFSG.LocalAnalysis.ComponentInitial.LinearInvolutionFixedField
public import CFSG.LocalAnalysis.RankThreeEvenClassification.ComponentCore
public import CFSG.Walter.Defs

public section

namespace CFSG.LocalAnalysis.SymplecticFourStandard

namespace PrincipalLayers

open Subgroup TorusLayer CFSG.RankThree.PartOne.KCRootAxis
open CFSG.Assembly.LowTwoRank (StatedClassicalModel StatedProj StatedSL StatedSU StatedScalars)
open CFSG.LocalAnalysis.ComponentInitial (UnitaryFieldData)
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag (conjAut dualAut projectiveSL)
open CFSG.ClassicalGroups.UnitaryFlag (unitaryPSU unitaryPSUEquiv)
open CFSG.RankThree.PartTwo.KFacts (unitaryIsom3 psuConj psuField)
open CFSG.ComponentClassification.FixedCommutingProduct (fixedSubgroup)
open LinearUnitaryThree (barEquiv)
open scoped MatrixGroups

variable {F : Type} [Group F] [Finite F] {K : Type} [Field K] {n : ℕ}
  {S J Y V U : Subgroup F} {t : F} {hk : SL₂ K → F}

set_option quotPrecheck false in
local notation "𝐑" => CFSG.Open.standardComponentOddCore F
set_option quotPrecheck false in
local notation "θ" => QuotientGroup.mk' (CFSG.Open.standardComponentOddCore F)
set_option quotPrecheck false in
local notation "𝐒𝐛" => S.map (QuotientGroup.mk' (CFSG.Open.standardComponentOddCore F))
set_option quotPrecheck false in
local notation "𝐃" => normalClosure ((S.map (QuotientGroup.mk'
  (CFSG.Open.standardComponentOddCore F)) : Subgroup (F ⧸ CFSG.Open.standardComponentOddCore F)) :
    Set (F ⧸ CFSG.Open.standardComponentOddCore F))
set_option quotPrecheck false in
local notation "𝐚" => QuotientGroup.mk' (CFSG.Open.standardComponentOddCore F) t
set_option quotPrecheck false in
local notation "α" => (MulAut.conjNormal (H := 𝐃) 𝐚 : MulAut ↥𝐃)

namespace AxisData

theorem facts (h : AxisData F K n S J Y V U t hk) :
    Set.InjOn θ (S : Set F) ∧ (∀ Q : Subgroup F, IsPGroup 2 Q → Set.InjOn θ (Q : Set F)) ∧
      orderOf 𝐚 = 2 ∧ (∃ e : SL₂ K ≃* ↥𝐒𝐛, ∀ X, (e X : F ⧸ 𝐑) = θ (hk X)) ∧
      𝐒𝐛 ≤ centralizer ({𝐚} : Set (F ⧸ 𝐑)) ∧
      (𝐒𝐛.subgroupOf (centralizer ({𝐚} : Set (F ⧸ 𝐑)))).Normal ∧ Y.map θ = 𝐃 ∧
      (center ↥Y).map Y.subtype = (CFSG.Open.standardComponentOddCore ↥Y).map Y.subtype ∧
      (CFSG.Open.standardComponentOddCore ↥Y).map Y.subtype = Y ⊓ 𝐑 ∧
      CFSG.LocalAnalysis.SteinbergBV.OneOrTwoLayerAlternatives 𝐒𝐛 𝐃 𝐚 := by
  obtain ⟨-, -, -, -, -, h6, h7, h8, h9, h10, -, h12, -, h14, h15, -, -, -, -, -, -, -, -, -,
    h25, -, h27, -⟩ := h.layer
  exact ⟨h8, h9, h10, h12, h14, h15, h25, h6, h7, h27⟩

theorem map_Y (h : AxisData F K n S J Y V U t hk) : Y.map θ = 𝐃 :=
  h.facts.2.2.2.2.2.2.1

theorem center_eq (h : AxisData F K n S J Y V U t hk) :
    (center ↥Y).map Y.subtype = Y ⊓ 𝐑 :=
  h.facts.2.2.2.2.2.2.2.1.trans h.facts.2.2.2.2.2.2.2.2.1

theorem a_mul_a (h : AxisData F K n S J Y V U t hk) : 𝐚 * 𝐚 = 1 := by
  have := pow_orderOf_eq_one 𝐚
  rwa [h.facts.2.2.1, sq] at this

theorem a_inv (h : AxisData F K n S J Y V U t hk) : 𝐚⁻¹ = 𝐚 :=
  inv_eq_of_mul_eq_one_right h.a_mul_a

omit [Finite F] in
theorem Sb_le_D : 𝐒𝐛 ≤ 𝐃 := subset_normalClosure

theorem mem_center_iff (h : AxisData F K n S J Y V U t hk) {y : Y} :
    y ∈ center ↥Y ↔ θ y = 1 := by
  have hc := h.center_eq
  constructor
  · intro hy
    have h1 : (y : F) ∈ Y ⊓ 𝐑 := hc ▸ mem_map_of_mem _ hy
    exact (QuotientGroup.eq_one_iff _).mpr h1.2
  · intro hy
    have h1 : (y : F) ∈ (center ↥Y).map Y.subtype :=
      hc ▸ mem_inf.mpr ⟨y.2, (QuotientGroup.eq_one_iff _).mp hy⟩
    obtain ⟨z, hz, hzy⟩ := mem_map.mp h1
    rwa [show z = y from Subtype.ext hzy] at hz

theorem ker_restrict (h : AxisData F K n S J Y V U t hk) :
    (restrictTo θ h.map_Y).ker = center ↥Y := by
  ext y
  rw [mem_ker_restrictTo, h.mem_center_iff]

theorem odd_card_center (h : AxisData F K n S J Y V U t hk) : Odd (Nat.card (center ↥Y)) := by
  rw [← card_map_of_injective Y.subtype_injective, h.center_eq]
  exact (CFSG.LocalAnalysis.EvenBN.GMSK.odd_card_standardComponentOddCore F).of_dvd_nat
    (card_dvd_of_le inf_le_right)

theorem card_Y (h : AxisData F K n S J Y V U t hk) :
    Nat.card Y = Nat.card 𝐃 * Nat.card (center ↥Y) := by
  have e := QuotientGroup.quotientKerEquivOfSurjective _ (restrictTo_surjective h.map_Y)
  rw [card_eq_card_quotient_mul_card_subgroup (restrictTo θ h.map_Y).ker, Nat.card_congr e.toEquiv,
    h.ker_restrict]

theorem ordProj_card_Y (h : AxisData F K n S J Y V U t hk) :
    ordProj[2] (Nat.card Y) = ordProj[2] (Nat.card 𝐃) := by
  rw [h.card_Y, Nat.ordProj_mul 2 Nat.card_pos.ne' Nat.card_pos.ne',
    Nat.factorization_eq_zero_of_not_dvd (fun h2 => (Nat.not_even_iff_odd.mpr
      h.odd_card_center) (even_iff_two_dvd.mpr h2)), pow_zero, mul_one]

theorem injOn_V (h : AxisData F K n S J Y V U t hk) : Set.InjOn θ (V : Set F) :=
  h.facts.2.1 V h.V_pgroup

theorem card_map_subgroupOf (h : AxisData F K n S J Y V U t hk) {X : Subgroup F}
    (hX : IsPGroup 2 X) (hXY : X ≤ Y) : Nat.card ((X.map θ).subgroupOf 𝐃) = Nat.card X := by
  have hXD : X.map θ ≤ 𝐃 := h.map_Y ▸ map_mono hXY
  rw [Nat.card_congr (subgroupOfEquivOfLe hXD).toEquiv, card_map_of_injOn θ (h.facts.2.1 X hX)]

theorem exists_conj_ne (h : AxisData F K n S J Y V U t hk) :
    ∃ d ∈ 𝐃, 𝐚⁻¹ * d * 𝐚 ≠ d := by
  rcases h.facts.2.2.2.2.2.2.2.2.2 with ⟨⟨-, -, -, hd⟩, -⟩ |
    ⟨⟨D₁, D₂, -, -, hne, -, -, -, -, hsup, -, -, hmap, -⟩, -⟩
  · exact hd
  · by_contra hall
    push Not at hall
    apply hne
    rw [← hmap]
    ext x
    constructor
    · intro hx
      refine ⟨x, hx, ?_⟩
      change 𝐚⁻¹ * x * 𝐚⁻¹⁻¹ = x
      rw [inv_inv]
      exact hall x (hsup ▸ mem_sup_left hx)
    · rintro ⟨y, hy, rfl⟩
      change 𝐚⁻¹ * y * 𝐚⁻¹⁻¹ ∈ D₁
      rw [inv_inv, hall y (hsup ▸ mem_sup_left hy)]
      exact hy

omit [Finite F] in
theorem coe_alpha (d : 𝐃) : ((α d : 𝐃) : F ⧸ 𝐑) = 𝐚 * d * 𝐚⁻¹ :=
  MulAut.conjNormal_apply _ _

theorem orderOf_alpha (h : AxisData F K n S J Y V U t hk) : orderOf α = 2 := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  apply orderOf_eq_prime
  · rw [sq, ← map_mul, h.a_mul_a, map_one]
  · intro h1
    obtain ⟨d, hd, hne⟩ := h.exists_conj_ne
    apply hne
    have h2 := congrArg (fun φ : MulAut ↥𝐃 => ((φ ⟨d, hd⟩ : 𝐃) : F ⧸ 𝐑)) h1
    simp only [MulAut.one_apply] at h2
    rw [coe_alpha] at h2
    rw [h.a_inv] at h2 ⊢
    exact h2

omit [Finite F] in
theorem mem_fixedSubgroup_iff {d : 𝐃} :
    d ∈ fixedSubgroup α ↔ (d : F ⧸ 𝐑) ∈ centralizer ({𝐚} : Set (F ⧸ 𝐑)) := by
  change α d = d ↔ _
  rw [mem_centralizer_singleton_iff, Subtype.ext_iff, coe_alpha]
  constructor
  · intro h1
    calc (d : F ⧸ 𝐑) * 𝐚 = 𝐚 * d * 𝐚⁻¹ * 𝐚 := by rw [h1]
      _ = 𝐚 * d := by group
  · intro h1
    rw [← h1, mul_inv_cancel_right]

theorem Sb_le_fixed (h : AxisData F K n S J Y V U t hk) :
    𝐒𝐛.subgroupOf 𝐃 ≤ fixedSubgroup α := fun _ hd =>
  mem_fixedSubgroup_iff.mpr (h.facts.2.2.2.2.1 (mem_subgroupOf.mp hd))

theorem Sb_normal_fixed (h : AxisData F K n S J Y V U t hk) :
    ((𝐒𝐛.subgroupOf 𝐃).subgroupOf (fixedSubgroup α)).Normal := by
  refine ⟨fun x hx g => ?_⟩
  rw [mem_subgroupOf, mem_subgroupOf] at hx ⊢
  have hgC := mem_fixedSubgroup_iff.mp g.2
  have := h.facts.2.2.2.2.2.1.conj_mem ⟨x, h.facts.2.2.2.2.1 hx⟩ (mem_subgroupOf.mpr hx)
    ⟨((g : fixedSubgroup α) : 𝐃), hgC⟩
  rw [mem_subgroupOf] at this
  exact this

theorem exists_kappa (h : AxisData F K n S J Y V U t hk) :
    ∃ κ : ↥(𝐒𝐛.subgroupOf 𝐃) ≃* SL(2, K), ∀ X, ((κ.symm X : 𝐃) : F ⧸ 𝐑) = θ (hk X) := by
  obtain ⟨e, he⟩ := h.facts.2.2.2.1
  exact ⟨(subgroupOfEquivOfLe Sb_le_D).trans e.symm, fun X => by
    simp only [MulEquiv.symm_trans_apply, MulEquiv.symm_symm]
    rw [← he X]
    rfl⟩

omit [Finite F] in
theorem Sb_eq_of_fixed (hS : 𝐒𝐛.subgroupOf 𝐃 = fixedSubgroup α) :
    𝐒𝐛 = 𝐃 ⊓ centralizer ({𝐚} : Set (F ⧸ 𝐑)) := by
  apply le_antisymm
  · intro x hx
    have hxS : (⟨x, Sb_le_D hx⟩ : 𝐃) ∈ 𝐒𝐛.subgroupOf 𝐃 := mem_subgroupOf.mpr hx
    rw [hS] at hxS
    exact mem_inf.mpr ⟨Sb_le_D hx, mem_fixedSubgroup_iff.mp hxS⟩
  · intro x hx
    obtain ⟨hxD, hxC⟩ := mem_inf.mp hx
    have hxF : (⟨x, hxD⟩ : 𝐃) ∈ fixedSubgroup α := mem_fixedSubgroup_iff.mpr hxC
    rw [← hS] at hxF
    exact mem_subgroupOf.mp hxF

theorem t_not_mem (h : AxisData F K n S J Y V U t hk)
    (hout : α ∉ (MulAut.conj : ↥𝐃 →* MulAut ↥𝐃).range) : t ∉ Y := by
  intro htY
  apply hout
  refine ⟨restrictTo θ h.map_Y ⟨t, htY⟩, ?_⟩
  ext d
  rw [MulAut.conj_apply, coe_alpha]
  rfl

theorem sylowConclusion (h : AxisData F K n S J Y V U t hk)
    (hV : Nat.card V = ordProj[2] (Nat.card 𝐃))
    (hout : α ∉ (MulAut.conj : ↥𝐃 →* MulAut ↥𝐃).range) : SylowConclusion Y V t := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hsyl : ∃ R : Sylow 2 ↥Y, (R : Subgroup ↥Y).map Y.subtype = V := by
    refine ⟨Sylow.ofCard (V.subgroupOf Y) ?_, ?_⟩
    · rw [Nat.card_congr (subgroupOfEquivOfLe h.V_le).toEquiv, hV, ← h.ordProj_card_Y]
    · rw [Sylow.coe_ofCard, subgroupOf_map_subtype, inf_of_le_left h.V_le]
  have htn := h.t_not_mem hout
  have htY : t ∈ normalizer (Y : Set F) := by
    rw [normalizer_eq_top_iff.mpr h.Y_normal]
    exact mem_top t
  exact ⟨hsyl, htn, exists_sylow_sup_zpowers hsyl htY h.t_mem h.order_t htn⟩

theorem linear_three (h : AxisData F K n S J Y V U t hk) {m : ℕ} {F' : Type} [Field F']
    (hF' : Nat.card F' = 2 ^ m) (η : ↥𝐃 ≃* StatedProj (StatedSL 3 F')) :
    m = n ∧ 𝐒𝐛 = 𝐃 ⊓ centralizer ({𝐚} : Set (F ⧸ 𝐑)) ∧
      α ∉ (MulAut.conj : ↥𝐃 →* MulAut ↥𝐃).range ∧
      (∃ H : GL (Fin 3) F', ∀ d d' : ↥𝐃, (d' : F ⧸ 𝐑) = 𝐚⁻¹ * d * 𝐚 →
        conjAut 3 F' H (statedProjEquivProjectiveSL 3 F' (η d')) =
          dualAut 3 F' (conjAut 3 F' H (statedProjEquivProjectiveSL 3 F' (η d)))) ∧
      ordProj[2] (Nat.card 𝐃) = (2 ^ n) ^ 3 ∧
      ∀ U' : Subgroup ↥𝐃, CFSG.IsElementaryAbelian 2 U' → Nat.card U' = (2 ^ n) ^ 2 →
        ¬ U'.map (α).toMonoidHom ≤ U' := by
  obtain ⟨κ, -⟩ := h.exists_kappa
  obtain ⟨hmn, hSeq, hout, ⟨H, hH, -⟩, hord, hel, -⟩ :=
    LinearUnitaryThree.linear_three_fixed_normal_SL_two h.card_K h.two_le hF'
      (η.trans (statedProjEquivProjectiveSL 3 F')) α h.orderOf_alpha _ h.Sb_le_fixed
      h.Sb_normal_fixed κ
  refine ⟨hmn, Sb_eq_of_fixed hSeq, hout, ⟨H, fun d d' hd' => ?_⟩, hord, hel⟩
  have hαd : α d = d' := by
    apply Subtype.ext
    rw [coe_alpha, hd', h.a_inv]
  have := hH d
  rw [hαd] at this
  exact this

theorem unitary_three (h : AxisData F K n S J Y V U t hk) {m : ℕ} {F' : Type} [Field F']
    (hF' : UnitaryFieldData 2 m F') (η : ↥𝐃 ≃* StatedProj (StatedSU 3 (2 ^ m) F')) :
    m = n ∧ 𝐒𝐛 = 𝐃 ⊓ centralizer ({𝐚} : Set (F ⧸ 𝐑)) ∧
      α ∉ (MulAut.conj : ↥𝐃 →* MulAut ↥𝐃).range ∧
      (∃ H : unitaryIsom3 hF', ∀ d d' : ↥𝐃, (d' : F ⧸ 𝐑) = 𝐚⁻¹ * d * 𝐚 →
        psuConj hF' H ((unitaryPSUEquiv hF' (n := 3) (by norm_num)).symm (η d')) =
          psuField hF' (barEquiv hF')
            (psuConj hF' H ((unitaryPSUEquiv hF' (n := 3) (by norm_num)).symm (η d)))) ∧
      ordProj[2] (Nat.card 𝐃) = (2 ^ n) ^ 3 ∧
      ∀ U' : Subgroup ↥𝐃, CFSG.IsElementaryAbelian 2 U' → Nat.card U' ≤ 2 ^ n := by
  obtain ⟨κ, -⟩ := h.exists_kappa
  obtain ⟨hmn, hSeq, hout, ⟨H, hH, -⟩, hord, hel, -⟩ :=
    LinearUnitaryThree.unitary_three_fixed_normal_SL_two h.card_K h.two_le hF'
      (η.trans (unitaryPSUEquiv hF' (n := 3) (by norm_num)).symm) α h.orderOf_alpha _
      h.Sb_le_fixed h.Sb_normal_fixed κ
  refine ⟨hmn, Sb_eq_of_fixed hSeq, hout, ⟨H, fun d d' hd' => ?_⟩, hord, hel⟩
  have hαd : α d = d' := by
    apply Subtype.ext
    rw [coe_alpha, hd', h.a_inv]
  have := hH d
  rw [hαd] at this
  exact this

theorem map_comm (h : AxisData F K n S J Y V U t hk) {X : Subgroup F} (hXY : X ≤ Y)
    (hXc : ∀ x ∈ X, ∀ y ∈ X, x * y = y * x) :
    ∀ x ∈ (X.map θ).subgroupOf 𝐃, ∀ y ∈ (X.map θ).subgroupOf 𝐃, x * y = y * x := by
  have _hXD : X.map θ ≤ 𝐃 := h.map_Y ▸ map_mono hXY
  intro x hx y hy
  obtain ⟨a, ha, hax⟩ := mem_map.mp (mem_subgroupOf.mp hx)
  obtain ⟨b, hb, hby⟩ := mem_map.mp (mem_subgroupOf.mp hy)
  apply Subtype.ext
  rw [coe_mul, coe_mul, ← hax, ← hby, ← map_mul, ← map_mul, hXc a ha b hb]

omit [Finite F] in
theorem map_sq {X : Subgroup F} (hXs : ∀ x ∈ X, x * x = 1) :
    ∀ x ∈ (X.map θ).subgroupOf 𝐃, x * x = 1 := by
  intro x hx
  obtain ⟨a, ha, hax⟩ := mem_map.mp (mem_subgroupOf.mp hx)
  apply Subtype.ext
  rw [coe_mul, ← hax, ← map_mul, hXs a ha, map_one]
  rfl

theorem three_of_nontrivial (h : AxisData F K n S J Y V U t hk)
    (hV3 : Nat.card V = (2 ^ n) ^ 3) (m : ℕ)
    (hm : StatedClassicalModel ↥𝐃 .PSL 3 2 m ∨ StatedClassicalModel ↥𝐃 .PSU 3 2 m) :
    m = n ∧ SylowConclusion Y V t := by
  rcases hm with hm | hm
  · obtain ⟨-, F', _, _, hF', ⟨η⟩⟩ := hm
    obtain ⟨hmn, -, hout, -, hord, -⟩ := h.linear_three hF' η
    exact ⟨hmn, h.sylowConclusion (hV3.trans hord.symm) hout⟩
  · obtain ⟨⟨-, hm1, -⟩, F', _, _, hF', ⟨η⟩⟩ := hm
    have hu : UnitaryFieldData 2 m F' := ⟨Nat.prime_two, hm1, by rw [hF', ← pow_mul, mul_comm]⟩
    obtain ⟨hmn, -, hout, -, hord, -⟩ := h.unitary_three hu η
    exact ⟨hmn, h.sylowConclusion (hV3.trans hord.symm) hout⟩

theorem not_psl_two_of_nontrivial (h : AxisData F K n S J Y V U t hk) {W : Subgroup F}
    (hWV : W ≤ V) (hWc : ∀ x ∈ W, ∀ y ∈ W, x * y = y * x) (hUW : U ≤ W)
    (hWU : ∀ w ∈ W, w * w ∈ U) (hW1 : ∃ w ∈ W, w * w ≠ 1) :
    (∀ p f : ℕ, p ≠ 2 → ¬ StatedClassicalModel ↥𝐃 .PSL 2 p f) ∧
      ∀ m : ℕ, ¬ StatedClassicalModel ↥𝐃 .PSL 2 2 m := by
  have hW2 : IsPGroup 2 W := h.V_pgroup.to_le hWV
  have hWY : W ≤ Y := hWV.trans h.V_le
  have hWD : W.map θ ≤ 𝐃 := h.map_Y ▸ map_mono hWY
  have hinj := h.facts.2.1 W hW2
  obtain ⟨w, hwW, hw1⟩ := hW1
  set w' : ↥𝐃 := ⟨θ w, hWD (mem_map_of_mem _ hwW)⟩
  have hw'A : w' ∈ (W.map θ).subgroupOf 𝐃 := mem_subgroupOf.mpr (mem_map_of_mem _ hwW)
  have hw' : w' * w' ≠ 1 := by
    intro h1
    apply hw1
    have h2 : θ (w * w) = θ 1 := by
      rw [map_mul, map_one]
      exact congrArg Subtype.val h1
    exact hinj (mul_mem hwW hwW) (one_mem W) h2
  have hw'4 : w' ^ 2 ^ 2 = 1 := by
    apply Subtype.ext
    change (θ w) ^ 2 ^ 2 = 1
    rw [← map_pow, show w ^ 2 ^ 2 = (w * w) * (w * w) by
      rw [show (2 : ℕ) ^ 2 = 2 + 2 by norm_num, pow_add, sq], h.U_sq _ (hWU w hwW), map_one]
  refine ⟨fun p f hp2 hm => ?_, fun m hm => ?_⟩
  · obtain ⟨⟨hp, -, -⟩, k, _, _, hk, ⟨η⟩⟩ := hm
    have hq : Odd (Nat.card k) := hk ▸ (hp.eq_two_or_odd'.resolve_left hp2).pow
    have hA2 : IsPGroup 2 ((W.map θ).subgroupOf 𝐃) :=
      (hW2.map θ).comap_of_injective 𝐃.subtype 𝐃.subtype_injective
    have hEA : (U.map θ).subgroupOf 𝐃 ≤ (W.map θ).subgroupOf 𝐃 := fun x hx =>
      mem_subgroupOf.mpr (map_mono hUW (mem_subgroupOf.mp hx))
    have hE4 : 4 ≤ Nat.card ((U.map θ).subgroupOf 𝐃) := by
      rw [h.card_map_subgroupOf (h.V_pgroup.to_le h.U_le_V) (hUW.trans hWY), h.U_card]
      calc 4 = 2 ^ 2 := by norm_num
        _ ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) h.two_le
    exact false_of_odd_psl_two hq η hA2 (h.map_comm hWY hWc) hw'A hw' hEA (map_sq h.U_sq) hE4
  · obtain ⟨-, k, _, _, hk, ⟨η⟩⟩ := hm
    have : CharP k 2 := charP_two_of_card hk
    have h1 := sl2_mul_self_eq_one (x := (η.trans (statedProjSLTwoEquiv k)) w') (k := 2)
      (by rw [← map_pow, hw'4, map_one])
    apply hw'
    apply (η.trans (statedProjSLTwoEquiv k)).injective
    rw [map_mul, h1, map_one]

end AxisData

end PrincipalLayers

end CFSG.LocalAnalysis.SymplecticFourStandard
