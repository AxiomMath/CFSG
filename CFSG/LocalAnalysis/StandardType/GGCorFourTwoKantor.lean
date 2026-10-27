module

public import CFSG.RankThree.PartOne.LIT.KF127Trans
public import Mathlib.LinearAlgebra.FiniteDimensional.Lemmas
import Mathlib.Tactic.LinearCombination

public section

namespace CFSG.StandardType

open CFSG.RankThree.PartOne.LIT
open CFSG.RankThree.Classical (IsTransvectionWith)

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

section Blocks

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

@[expose] def ggBlockCompl {ι : Type*} (C : Submodule K V) (W : ι → Submodule K V) (i : ι) :
    Submodule K V :=
  C ⊔ ⨆ (j : ι) (_ : j ≠ i), W j

theorem le_ggBlockCompl {ι : Type*} (C : Submodule K V) (W : ι → Submodule K V) {i j : ι}
    (hij : j ≠ i) : W j ≤ ggBlockCompl C W i :=
  le_sup_of_le_right (le_iSup₂_of_le j hij le_rfl)

theorem ggBlockCompl_eq_of_subsingleton {ι : Type*} [Subsingleton ι] (C : Submodule K V)
    (W : ι → Submodule K V) (i : ι) : ggBlockCompl C W i = C := by
  have h : (⨆ (j : ι) (_ : j ≠ i), W j) = ⊥ :=
    le_bot_iff.mp (iSup₂_le fun j hj => absurd (Subsingleton.elim j i) hj)
  rw [ggBlockCompl, h, sup_bot_eq]

end Blocks

section BlockDef

variable {p : ℕ} {V : Type} [AddCommGroup V] [Module (ZMod p) V]

@[expose] def GGBlockSLSp (T : Subgroup (V ≃ₗ[ZMod p] V)) (U W : Submodule (ZMod p) V) : Prop :=
  (∀ g : V ≃ₗ[ZMod p] V, (∀ u ∈ U, g u = u) → (∀ w ∈ W, g w ∈ W) →
      LinearEquiv.det g = 1 → g ∈ T) ∨
    ∃ β : LinearMap.BilinForm (ZMod p) V, β.IsAlt ∧ (∀ u ∈ U, ∀ v, β u v = 0) ∧
      (∀ w ∈ W, w ≠ 0 → ∃ w' ∈ W, β w w' ≠ 0) ∧
      ∀ g : V ≃ₗ[ZMod p] V, (∀ u ∈ U, g u = u) → (∀ w ∈ W, g w ∈ W) →
        (∀ v w, β (g v) (g w) = β v w) → g ∈ T

end BlockDef

@[expose] def GGKantorReductionInput : Prop :=
  ∀ (p : ℕ) [Fact p.Prime], p ≠ 2 →
  ∀ (V : Type) [AddCommGroup V] [Module (ZMod p) V] [Module.Finite (ZMod p) V]
    (A : Subgroup (V ≃ₗ[ZMod p] V)),
    (∀ N : Subgroup (V ≃ₗ[ZMod p] V), N ≤ A → (∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) →
      IsPGroup p N → N = ⊥) →
    ∃ (ι : Type) (_ : Finite ι) (C : Submodule (ZMod p) V) (W : ι → Submodule (ZMod p) V),
      C ⊔ (⨆ i, W i) = ⊤ ∧ (∀ i, IsCompl (W i) (ggBlockCompl C W i)) ∧
      (∀ t ∈ trGroup A, (∀ c ∈ C, t c = c) ∧ ∀ i, ∀ w ∈ W i, t w ∈ W i) ∧
      ∀ i, 2 ≤ Module.finrank (ZMod p) (W i) ∧
        GGBlockSLSp (trGroup A) (ggBlockCompl C W i) (W i)

section Transvections

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem isTransvectionWith_transvection {f : Module.Dual K V} {c : V} (hfc : f c = 0)
    (hc : c ≠ 0) (hf : f ≠ 0) : IsTransvectionWith (LinearEquiv.transvection hfc) c f :=
  ⟨hc, hf, hfc, fun x => LinearEquiv.transvection.apply hfc x⟩

theorem mem_of_slBlock {T : Subgroup (V ≃ₗ[K] V)} {U W : Submodule K V}
    (hSL : ∀ g : V ≃ₗ[K] V, (∀ u ∈ U, g u = u) → (∀ w ∈ W, g w ∈ W) →
      LinearEquiv.det g = 1 → g ∈ T)
    {t : V ≃ₗ[K] V} {c : V} {f : Module.Dual K V} (ht : IsTransvectionWith t c f) (hc : c ∈ W)
    (hfU : ∀ u ∈ U, f u = 0) : t ∈ T := by
  refine hSL t (fun u hu => ?_) (fun w hw => ?_) (isTransvectionWith_det ht)
  · rw [ht.2.2.2, hfU u hu, zero_smul, add_zero]
  · rw [ht.2.2.2]
    exact W.add_mem hw (W.smul_mem _ hc)

@[expose] noncomputable def ggSymplTransvection {β : LinearMap.BilinForm K V} (hβ : β.IsAlt)
    (c : V) : V ≃ₗ[K] V :=
  LinearEquiv.transvection (f := LinearMap.flip β c) (v := c) (hβ.self_eq_zero c)

theorem ggSymplTransvection_apply {β : LinearMap.BilinForm K V} (hβ : β.IsAlt) (c x : V) :
    ggSymplTransvection hβ c x = x + β x c • c :=
  LinearEquiv.transvection.apply _ x

theorem isTransvectionWith_ggSymplTransvection {β : LinearMap.BilinForm K V} (hβ : β.IsAlt)
    {c : V} (hc : c ≠ 0) (hf : LinearMap.flip β c ≠ 0) :
    IsTransvectionWith (ggSymplTransvection hβ c) c (LinearMap.flip β c) :=
  ⟨hc, hf, hβ.self_eq_zero c, fun x => LinearEquiv.transvection.apply _ x⟩

theorem ggSymplTransvection_preserves {β : LinearMap.BilinForm K V} (hβ : β.IsAlt) (c : V)
    (v w : V) : β (ggSymplTransvection hβ c v) (ggSymplTransvection hβ c w) = β v w := by
  rw [ggSymplTransvection_apply, ggSymplTransvection_apply]
  have hneg : -β c w = β w c := hβ.neg_eq c w
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    hβ.self_eq_zero c, mul_zero, add_zero]
  linear_combination (-(β v c)) * hneg

theorem mem_of_spBlock {T : Subgroup (V ≃ₗ[K] V)} {U W : Submodule K V}
    {β : LinearMap.BilinForm K V} (hβ : β.IsAlt) (hβU : ∀ u ∈ U, ∀ v, β u v = 0)
    (hSp : ∀ g : V ≃ₗ[K] V, (∀ u ∈ U, g u = u) → (∀ w ∈ W, g w ∈ W) →
      (∀ v w, β (g v) (g w) = β v w) → g ∈ T)
    {c : V} (hc : c ∈ W) : ggSymplTransvection hβ c ∈ T := by
  refine hSp _ (fun u hu => ?_) (fun w hw => ?_) (ggSymplTransvection_preserves hβ c)
  · rw [ggSymplTransvection_apply, hβU u hu c, zero_smul, add_zero]
  · rw [ggSymplTransvection_apply]
    exact W.add_mem hw (W.smul_mem _ hc)

theorem flip_ne_zero_of_nondeg {β : LinearMap.BilinForm K V} (hβ : β.IsAlt)
    {W : Submodule K V} (hnd : ∀ w ∈ W, w ≠ 0 → ∃ w' ∈ W, β w w' ≠ 0) {c : V} (hc : c ∈ W)
    (hc0 : c ≠ 0) : LinearMap.flip β c ≠ 0 := by
  obtain ⟨w', -, hw'⟩ := hnd c hc hc0
  intro h0
  apply hw'
  have h1 : β w' c = 0 := by
    have := LinearMap.congr_fun h0 w'
    rwa [LinearMap.flip_apply, LinearMap.zero_apply] at this
  rw [← hβ.neg_eq w' c, h1, neg_zero]

end Transvections

section Dimension

variable {K : Type*} [Field K] {V : Type*} [AddCommGroup V] [Module K V]

theorem exists_dual_ne_zero_of_finrank_lt {S : Submodule K V}
    (h : Module.finrank K S < Module.finrank K V) :
    ∃ f : Module.Dual K V, f ≠ 0 ∧ ∀ s ∈ S, f s = 0 := by
  have hlt : S < ⊤ := by
    refine lt_top_iff_ne_top.mpr fun htop => ?_
    rw [htop, finrank_top] at h
    exact lt_irrefl _ h
  obtain ⟨f, hf, hle⟩ := Submodule.exists_le_ker_of_lt_top S hlt
  exact ⟨f, hf, fun s hs => hle hs⟩

variable [FiniteDimensional K V]

theorem finrank_sup_span_lt {U W : Submodule K V} (hWU : IsCompl W U)
    (hW : 2 ≤ Module.finrank K W) (u : V) :
    Module.finrank K ↥(U ⊔ Submodule.span K {u}) < Module.finrank K V := by
  have h1 := Submodule.finrank_add_le_finrank_add_finrank U (Submodule.span K {u})
  have h2 := finrank_span_le_card (R := K) ({u} : Set V)
  have h3 := Submodule.finrank_add_eq_of_isCompl hWU
  simp only [Set.toFinset_singleton, Finset.card_singleton] at h2
  omega

theorem finrank_sup_span_pair_lt {U W : Submodule K V} (hWU : IsCompl W U)
    (hW : 3 ≤ Module.finrank K W) (u c : V) :
    Module.finrank K ↥(U ⊔ Submodule.span K {u, c}) < Module.finrank K V := by
  classical
  have h1 := Submodule.finrank_add_le_finrank_add_finrank U (Submodule.span K {u, c})
  have h2 := finrank_span_le_card (R := K) ({u, c} : Set V)
  have h2' : ({u, c} : Set V).toFinset.card ≤ 2 := by
    rw [Set.toFinset_insert, Set.toFinset_singleton]
    exact (Finset.card_insert_le _ _).trans (by simp)
  have h3 := Submodule.finrank_add_eq_of_isCompl hWU
  omega

omit [FiniteDimensional K V] in
theorem exists_mem_notMem_span_singleton {W : Submodule K V} (hW : 2 ≤ Module.finrank K W) (x : V) :
    ∃ c ∈ W, c ∉ Submodule.span K {x} := by
  by_contra hcon
  push Not at hcon
  have hle : W ≤ Submodule.span K {x} := fun c hc => hcon c hc
  have h1 := Submodule.finrank_mono hle
  have h2 := finrank_span_le_card (R := K) ({x} : Set V)
  simp only [Set.toFinset_singleton, Finset.card_singleton] at h2
  omega

end Dimension

section Local

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [Module.Finite (ZMod p) V]

theorem exists_transvection_center_of_block {T : Subgroup (V ≃ₗ[ZMod p] V)}
    {U W : Submodule (ZMod p) V} (hWU : IsCompl W U) (hW : 2 ≤ Module.finrank (ZMod p) W)
    (hblk : GGBlockSLSp T U W) {u : V} (hu : u ∈ W) (hu0 : u ≠ 0) :
    ∃ t ∈ T, ∃ f : Module.Dual (ZMod p) V, IsTransvectionWith t u f ∧ ∀ v ∈ U, f v = 0 := by
  rcases hblk with hSL | ⟨β, hβ, hβU, hnd, hSp⟩
  · obtain ⟨f, hf, hfS⟩ := exists_dual_ne_zero_of_finrank_lt (finrank_sup_span_lt hWU hW u)
    have hfu : f u = 0 := hfS u (Submodule.mem_sup_right (Submodule.mem_span_singleton_self u))
    have hfU : ∀ v ∈ U, f v = 0 := fun v hv => hfS v (Submodule.mem_sup_left hv)
    have ht := isTransvectionWith_transvection hfu hu0 hf
    exact ⟨_, mem_of_slBlock hSL ht hu hfU, f, ht, hfU⟩
  · have hf := flip_ne_zero_of_nondeg hβ hnd hu hu0
    have ht := isTransvectionWith_ggSymplTransvection hβ hu0 hf
    refine ⟨_, mem_of_spBlock hβ hβU hSp hu, _, ht, fun v hv => ?_⟩
    rw [LinearMap.flip_apply]
    exact hβU v hv u

theorem exists_transvection_axis_of_block {T : Subgroup (V ≃ₗ[ZMod p] V)}
    {U W : Submodule (ZMod p) V} (hWU : IsCompl W U) (hW3 : 3 ≤ Module.finrank (ZMod p) W)
    (hblk : GGBlockSLSp T U W) (x : V) :
    ∃ t ∈ T, ∃ (c : V) (f : Module.Dual (ZMod p) V), IsTransvectionWith t c f ∧ f x = 0 ∧
      c ∉ Submodule.span (ZMod p) {x} := by
  rcases hblk with hSL | ⟨β, hβ, hβU, hnd, hSp⟩
  · obtain ⟨c, hcW, hcx⟩ :=
      exists_mem_notMem_span_singleton (by omega : 2 ≤ Module.finrank (ZMod p) W) x
    have hc0 : c ≠ 0 := fun h => hcx (h ▸ Submodule.zero_mem _)
    obtain ⟨f, hf, hfS⟩ := exists_dual_ne_zero_of_finrank_lt (finrank_sup_span_pair_lt hWU hW3 x c)
    have hfc : f c = 0 := hfS c (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
    have hfx : f x = 0 := hfS x (Submodule.mem_sup_right (Submodule.subset_span (by simp)))
    have hfU : ∀ v ∈ U, f v = 0 := fun v hv => hfS v (Submodule.mem_sup_left hv)
    have ht := isTransvectionWith_transvection hfc hc0 hf
    exact ⟨_, mem_of_slBlock hSL ht hcW hfU, c, f, ht, hfx, hcx⟩
  · have hZ2 : 2 ≤ Module.finrank (ZMod p) ↥(LinearMap.ker (β x) ⊓ W) := by
      have h1 := LinearMap.finrank_range_add_finrank_ker (K := ZMod p) (β x)
      have h2 : Module.finrank (ZMod p) (LinearMap.range (β x)) ≤ 1 := by
        have := Submodule.finrank_le (LinearMap.range (β x))
        rwa [Module.finrank_self] at this
      have h3 := Submodule.finrank_sup_add_finrank_inf_eq (LinearMap.ker (β x)) W
      have h4 := Submodule.finrank_le (LinearMap.ker (β x) ⊔ W)
      omega
    obtain ⟨c, hcZ, hcx⟩ := exists_mem_notMem_span_singleton hZ2 x
    have hc0 : c ≠ 0 := fun h => hcx (h ▸ Submodule.zero_mem _)
    have hf := flip_ne_zero_of_nondeg hβ hnd hcZ.2 hc0
    have ht := isTransvectionWith_ggSymplTransvection hβ hc0 hf
    refine ⟨_, mem_of_spBlock hβ hβU hSp hcZ.2, c, _, ht, ?_, hcx⟩
    rw [LinearMap.flip_apply]
    exact hcZ.1

theorem exists_transvection_fix_or_plane (hK : GGKantorReductionInput) (hp : p ≠ 2)
    (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ N : Subgroup (V ≃ₗ[ZMod p] V), N ≤ A → (∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) →
      IsPGroup p N → N = ⊥)
    (htr : ∃ t ∈ A, ∃ (c : V) (f : Module.Dual (ZMod p) V), IsTransvectionWith t c f) (x : V) :
    (∃ t ∈ A, ∃ (c : V) (f : Module.Dual (ZMod p) V), IsTransvectionWith t c f ∧ f x = 0 ∧
        c ∉ Submodule.span (ZMod p) {x}) ∨
      ∃ W : Submodule (ZMod p) V, Module.finrank (ZMod p) W = 2 ∧ x ∈ W ∧
        ∀ a ∈ A, ∀ w ∈ W, a w ∈ W := by
  obtain ⟨ι, -, C, W, htop, hcompl, hT, hblk⟩ := hK p hp V A hA
  by_cases ha : ∃ t ∈ A, ∃ (c : V) (f : Module.Dual (ZMod p) V), IsTransvectionWith t c f ∧
      f x = 0 ∧ c ∉ Submodule.span (ZMod p) {x}
  · exact Or.inl ha
  right
  have hTA : trGroup A ≤ A := trGroup_le A
  have hcen : ∀ i, ∀ u ∈ W i, u ≠ 0 → ∃ t ∈ trGroup A, ∃ f : Module.Dual (ZMod p) V,
      IsTransvectionWith t u f ∧ ∀ v ∈ ggBlockCompl C W i, f v = 0 :=
    fun i u hu hu0 => exists_transvection_center_of_block (hcompl i) (hblk i).1 (hblk i).2 hu hu0
  have h1 : ∀ i, x ∉ ggBlockCompl C W i := by
    intro i hxU
    have hne : W i ≠ ⊥ := by
      intro hbot
      have := (hblk i).1
      rw [hbot, finrank_bot] at this
      omega
    obtain ⟨u, huW, hu0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨t, htT, f, ht, hfU⟩ := hcen i u huW hu0
    refine ha ⟨t, hTA htT, u, f, ht, hfU x hxU, fun hux => hu0 ?_⟩
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hux
    have hmem : a • x ∈ W i ⊓ ggBlockCompl C W i := ⟨huW, (ggBlockCompl C W i).smul_mem a hxU⟩
    rwa [(hcompl i).inf_eq_bot, Submodule.mem_bot] at hmem
  have h2 : ∀ i, x ∈ W i := by
    intro i
    have hxtop : x ∈ W i ⊔ ggBlockCompl C W i := by
      rw [(hcompl i).sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨w, hwW, v, hvU, hwv⟩ := Submodule.mem_sup.mp hxtop
    have hw0 : w ≠ 0 := by
      rintro rfl
      rw [zero_add] at hwv
      exact h1 i (hwv ▸ hvU)
    obtain ⟨t, htT, f, ht, hfU⟩ := hcen i w hwW hw0
    by_contra hxW
    refine ha ⟨t, hTA htT, w, f, ht, ?_, fun hwx => hxW ?_⟩
    · rw [← hwv, map_add, ht.2.2.1, hfU v hvU, add_zero]
    · obtain ⟨a, ha'⟩ := Submodule.mem_span_singleton.mp hwx
      have ha0 : a ≠ 0 := by
        rintro rfl
        rw [zero_smul] at ha'
        exact hw0 ha'.symm
      have hxw : x = a⁻¹ • w := by rw [← ha', smul_smul, inv_mul_cancel₀ ha0, one_smul]
      rw [hxw]
      exact (W i).smul_mem _ hwW
  have h3 : ∀ i j : ι, i = j := by
    intro i j
    by_contra hij
    exact h1 j (le_ggBlockCompl C W hij (h2 i))
  obtain ⟨t₀, ht₀A, c₀, f₀, ht₀⟩ := htr
  have hne : Nonempty ι := by
    by_contra hemp
    rw [not_nonempty_iff] at hemp
    have hC : C = ⊤ := by rw [← htop, iSup_of_empty, sup_bot_eq]
    obtain ⟨v, hv⟩ := exists_ne_of_mem_trSet ⟨ht₀A, c₀, f₀, ht₀⟩
    exact hv ((hT t₀ (subset_trGroup ⟨ht₀A, c₀, f₀, ht₀⟩)).1 v (hC ▸ Submodule.mem_top))
  obtain ⟨i⟩ := hne
  have : Subsingleton ι := ⟨h3⟩
  have hUC : ggBlockCompl C W i = C := ggBlockCompl_eq_of_subsingleton C W i
  have h5 : Module.finrank (ZMod p) (W i) = 2 := by
    by_contra hne2
    have h3' : 3 ≤ Module.finrank (ZMod p) (W i) := by
      have := (hblk i).1
      omega
    obtain ⟨t, htT, c, f, ht, hfx, hcx⟩ :=
      exists_transvection_axis_of_block (hcompl i) h3' (hblk i).2 x
    exact ha ⟨t, hTA htT, c, f, ht, hfx, hcx⟩
  have hcenW : ∀ s ∈ trGroup A, ∀ (c : V) (g : Module.Dual (ZMod p) V),
      IsTransvectionWith s c g → c ∈ W i := by
    intro s hs c g hsg
    obtain ⟨v, hv⟩ : ∃ v, g v ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hsg.2.1 (LinearMap.ext hcon)
    have hvtop : v ∈ W i ⊔ C := by
      rw [← hUC, (hcompl i).sup_eq_top]
      exact Submodule.mem_top
    obtain ⟨w', hw', c', hc', hwc⟩ := Submodule.mem_sup.mp hvtop
    have hgc' : g c' = 0 := by
      have h := (hT s hs).1 c' hc'
      rw [hsg.2.2.2] at h
      have h' : g c' • c = 0 := by simpa using h
      exact (smul_eq_zero.mp h').resolve_right hsg.1
    have hgw' : g w' ≠ 0 := by
      rw [← hwc, map_add, hgc', add_zero] at hv
      exact hv
    have hsw := (hT s hs).2 i w' hw'
    rw [hsg.2.2.2] at hsw
    have hcw : g w' • c ∈ W i := by
      have := (W i).sub_mem hsw hw'
      rwa [add_sub_cancel_left] at this
    have := (W i).smul_mem (g w')⁻¹ hcw
    rwa [smul_smul, inv_mul_cancel₀ hgw', one_smul] at this
  refine ⟨W i, h5, h2 i, fun a haA w hw => ?_⟩
  by_cases hw0 : w = 0
  · rw [hw0, map_zero]
    exact (W i).zero_mem
  obtain ⟨t, htT, f, ht, -⟩ := hcen i w hw hw0
  exact hcenW _ (trGroup_conj haA htT) _ _ (isTransvectionWith_conj ht a)

end Local

section NormalP

variable {p : ℕ} [Fact p.Prime] {V : Type} [AddCommGroup V] [Module (ZMod p) V]
  [Module.Finite (ZMod p) V]

theorem noNormalP_trGroup (A : Subgroup (V ≃ₗ[ZMod p] V))
    (hA : ∀ N : Subgroup (V ≃ₗ[ZMod p] V), N ≤ A → (∀ a ∈ A, ∀ n ∈ N, a * n * a⁻¹ ∈ N) →
      IsPGroup p N → N = ⊥)
    (N : Subgroup (V ≃ₗ[ZMod p] V)) (hNT : N ≤ trGroup A)
    (hNn : ∀ g ∈ trGroup A, ∀ n ∈ N, g * n * g⁻¹ ∈ N) (hNp : IsPGroup p N) : N = ⊥ := by
  have : Finite (V ≃ₗ[ZMod p] V) := by
    have : Finite (V →ₗ[ZMod p] V) := Module.finite_of_finite (ZMod p)
    exact Finite.of_injective (fun e : V ≃ₗ[ZMod p] V => (e : V →ₗ[ZMod p] V))
      fun e f h => LinearEquiv.toLinearMap_injective h
  set T := trGroup A with hT
  set Na : ↥A → Subgroup (V ≃ₗ[ZMod p] V) :=
    fun a => N.map (MulAut.conj (a : V ≃ₗ[ZMod p] V)).toMonoidHom with hNa
  have hNaT : ∀ a, Na a ≤ T := by
    rintro a _ ⟨n, hn, rfl⟩
    exact trGroup_conj a.2 (hNT hn)
  have hNan : ∀ a, ((Na a).subgroupOf T).Normal := by
    intro a
    refine ⟨fun m hm g => ?_⟩
    rw [Subgroup.mem_subgroupOf] at hm ⊢
    obtain ⟨n, hn, hmn⟩ := hm
    have hmn' : (a : V ≃ₗ[ZMod p] V) * n * (a : V ≃ₗ[ZMod p] V)⁻¹ = (m : V ≃ₗ[ZMod p] V) := hmn
    have hg' : (a : V ≃ₗ[ZMod p] V)⁻¹ * g * (a : V ≃ₗ[ZMod p] V) ∈ T := by
      have h := trGroup_conj (A.inv_mem a.2) g.2
      rwa [inv_inv] at h
    refine ⟨((a : V ≃ₗ[ZMod p] V)⁻¹ * g * (a : V ≃ₗ[ZMod p] V)) * n *
      ((a : V ≃ₗ[ZMod p] V)⁻¹ * g * (a : V ≃ₗ[ZMod p] V))⁻¹, hNn _ hg' n hn, ?_⟩
    show (a : V ≃ₗ[ZMod p] V) * _ * (a : V ≃ₗ[ZMod p] V)⁻¹ =
      ((g * m * g⁻¹ : T) : V ≃ₗ[ZMod p] V)
    rw [Subgroup.coe_mul, Subgroup.coe_mul, Subgroup.coe_inv, ← hmn']
    group
  have hNap : ∀ a, IsPGroup p ((Na a).subgroupOf T) := by
    intro a
    have h1 : IsPGroup p (Na a) := hNp.map _
    exact h1.comap_of_injective T.subtype Subtype.coe_injective
  set M : Subgroup (V ≃ₗ[ZMod p] V) := ⨆ a, Na a with hM
  have hMT : M = (⨆ a, (Na a).subgroupOf T).map T.subtype := by
    rw [Subgroup.map_iSup, hM]
    exact iSup_congr fun a => (Subgroup.map_subgroupOf_eq_of_le (hNaT a)).symm
  have hMp : IsPGroup p M := by
    rw [hMT]
    have : ∀ a, ((Na a).subgroupOf T).Normal := hNan
    exact (Sylow.iSup_of_normal _ hNap).map _
  have hMA : M ≤ A := iSup_le fun a => (hNaT a).trans (trGroup_le A)
  have hMn : ∀ b ∈ A, ∀ m ∈ M, b * m * b⁻¹ ∈ M := by
    intro b hb m hm
    have hle : M.map (MulAut.conj b).toMonoidHom ≤ M := by
      rw [hM, Subgroup.map_iSup]
      refine iSup_le fun a => ?_
      have h1 : (Na a).map (MulAut.conj b).toMonoidHom = Na ⟨b * a, A.mul_mem hb a.2⟩ := by
        rw [hNa, Subgroup.map_map]
        congr 1
      rw [h1]
      exact le_iSup Na _
    exact hle ⟨m, hm, rfl⟩
  have hMbot := hA M hMA hMn hMp
  rw [eq_bot_iff]
  intro n hn
  have h1 : n ∈ M := by
    refine le_iSup Na ⟨1, A.one_mem⟩ ?_
    exact ⟨n, hn, by simp⟩
  rw [hMbot] at h1
  exact h1

end NormalP

end CFSG.StandardType
