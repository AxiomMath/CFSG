module

import CFSG.LocalAnalysis.StandardType.ZS.SubgroupSpaces
public import CFSG.LocalAnalysis.StandardType.ZS.LemmaOneTwo
public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyExcInvolutionCharpoly
public import TauCeti.Algebra.Module.Submodule.Ker
import TauCeti.LinearAlgebra.Dual.Lemmas
import CFSG.LocalAnalysis.StandardType.ZS.Basic

public section

namespace CFSG.StandardType.ZS

theorem eq_zero_of_eq_neg {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (h2 : (2 : K) ≠ 0) {v : E} (h : v = -v) : v = 0 := by
  have hsum : (2 : K) • v = 0 := by
    rw [two_smul]
    nth_rewrite 2 [h]
    exact add_neg_cancel v
  exact (smul_eq_zero.mp hsum).resolve_left h2

theorem eq_sup_inf_ker_sub_one_ker_add_one {K E : Type*} [Field K] [AddCommGroup E] [Module K E]
    (h2 : (2 : K) ≠ 0) {t : E ≃ₗ[K] E} (ht : t * t = 1) {X : Submodule K E}
    (hX : ∀ x ∈ X, (t : E →ₗ[K] E) x ∈ X) :
    X = (X ⊓ LinearMap.ker ((t : E →ₗ[K] E) - 1)) ⊔
        (X ⊓ LinearMap.ker ((t : E →ₗ[K] E) + 1)) := by
  have htt : ∀ y, (t : E →ₗ[K] E) ((t : E →ₗ[K] E) y) = y := by
    intro y
    have h : (t * t) y = (1 : E ≃ₗ[K] E) y := by rw [ht]
    simpa using h
  apply le_antisymm
  · intro w hw
    rw [Submodule.mem_sup]
    refine ⟨(2 : K)⁻¹ • (w + (t : E →ₗ[K] E) w), ⟨?_, ?_⟩,
      (2 : K)⁻¹ • (w - (t : E →ₗ[K] E) w), ⟨?_, ?_⟩, ?_⟩
    · exact X.smul_mem _ (X.add_mem hw (hX w hw))
    · refine LinearMap.mem_ker.mpr ?_
      have hfix : (t : E →ₗ[K] E) (w + (t : E →ₗ[K] E) w) =
          w + (t : E →ₗ[K] E) w := by
        rw [map_add, htt, add_comm]
      have hker : ((t : E →ₗ[K] E) - 1) (w + (t : E →ₗ[K] E) w) = 0 := by
        rw [LinearMap.sub_apply, Module.End.one_apply, hfix, sub_self]
      rw [LinearMap.map_smul, hker, smul_zero]
    · exact X.smul_mem _ (X.sub_mem hw (hX w hw))
    · refine LinearMap.mem_ker.mpr ?_
      have hneg : (t : E →ₗ[K] E) (w - (t : E →ₗ[K] E) w) =
          - (w - (t : E →ₗ[K] E) w) := by
        rw [map_sub, htt]
        abel
      have hker : ((t : E →ₗ[K] E) + 1) (w - (t : E →ₗ[K] E) w) = 0 := by
        rw [LinearMap.add_apply, Module.End.one_apply, hneg]
        abel
      rw [LinearMap.map_smul, hker, smul_zero]
    · rw [← smul_add]
      have hsum : w + (t : E →ₗ[K] E) w + (w - (t : E →ₗ[K] E) w) = (2 : K) • w := by
        rw [two_smul]
        abel
      rw [hsum, smul_smul, show (2 : K)⁻¹ * 2 = 1 from by
        rw [mul_comm, mul_inv_cancel₀ h2], one_smul]
  · exact sup_le inf_le_left inf_le_left

theorem movedSpace_eq_ker_add_one_of_mul_self {K E : Type*} [Field K] [AddCommGroup E]
    [Module K E] {t : E ≃ₗ[K] E} (h2 : (2 : K) ≠ 0) (ht : t * t = 1) :
    HardMathSupport.Kantor79.movedSpace t = LinearMap.ker ((t : E →ₗ[K] E) + 1) := by
  have htt : ∀ y, (t : E →ₗ[K] E) ((t : E →ₗ[K] E) y) = y := by
    intro y
    have h : (t * t) y = (1 : E ≃ₗ[K] E) y := by rw [ht]
    simpa using h
  ext x
  constructor
  · rintro ⟨v, rfl⟩
    refine LinearMap.mem_ker.mpr ?_
    change (t : E →ₗ[K] E) ((t : E →ₗ[K] E) v - v) + ((t : E →ₗ[K] E) v - v) = 0
    rw [map_sub, htt]
    abel
  · intro hx
    rw [LinearMap.mem_ker, LinearMap.add_apply, Module.End.one_apply,
      add_eq_zero_iff_eq_neg] at hx
    refine ⟨-((2 : K)⁻¹) • x, ?_⟩
    change (t : E →ₗ[K] E) (-((2 : K)⁻¹) • x) - (-((2 : K)⁻¹) • x) = x
    rw [map_smul, hx]
    have hsum : ((2 : K)⁻¹ + (2 : K)⁻¹) = 1 := by
      rw [← two_mul]
      exact mul_inv_cancel₀ h2
    have h1 : (-((2 : K)⁻¹)) • (-x) = (2 : K)⁻¹ • x := by simp
    have h2' : (-((2 : K)⁻¹)) • x = -((2 : K)⁻¹ • x) := by simp
    rw [h1, h2', sub_neg_eq_add, ← add_smul, hsum, one_smul]

end CFSG.StandardType.ZS

namespace CFSG.HardMathSupport.Kantor79

variable {K E : Type*} [Field K] [AddCommGroup E] [Module K E]

theorem apply_mem_movedSpace_of_commute {x y : E ≃ₗ[K] E} (hcomm : x * y = y * x) :
    ∀ v ∈ movedSpace x, y v ∈ movedSpace x := by
  rintro - ⟨u, rfl⟩
  refine ⟨y u, ?_⟩
  change (x : E →ₗ[K] E) (y u) - (y : E →ₗ[K] E) u =
    (y : E →ₗ[K] E) ((x : E →ₗ[K] E) u - u)
  rw [map_sub]
  congr 1
  have h := congrArg (fun e : E ≃ₗ[K] E => e u) hcomm
  simpa [LinearEquiv.mul_apply] using h

theorem apply_eq_neg_of_mem_movedSpace {t : E ≃ₗ[K] E} (ht : t * t = 1) {x : E}
    (hx : x ∈ movedSpace t) : t x = -x := by
  obtain ⟨v, rfl⟩ := hx
  change t (t v - v) = -(t v - v)
  rw [map_sub]
  have htt : t (t v) = v := by
    have h := congrArg (fun e : E ≃ₗ[K] E => e v) ht
    simpa [LinearEquiv.mul_apply] using h
  rw [htt]
  abel

theorem mem_movedSpace_of_apply_eq_neg {t : E ≃ₗ[K] E} {v : E} (h2 : (2 : K) ≠ 0)
    (ht : t v = -v) : v ∈ movedSpace t := by
  refine ⟨-((2 : K)⁻¹) • v, ?_⟩
  change (t : E →ₗ[K] E) (-((2 : K)⁻¹) • v) - (-((2 : K)⁻¹) • v) = v
  rw [map_smul, show (t : E →ₗ[K] E) v = -v from ht]
  have hsum : ((2 : K)⁻¹ + (2 : K)⁻¹) = 1 := by
    rw [← two_mul]
    exact mul_inv_cancel₀ h2
  have h1 : (-((2 : K)⁻¹)) • (-v) = (2 : K)⁻¹ • v := by simp
  have h2' : (-((2 : K)⁻¹)) • v = -((2 : K)⁻¹ • v) := by simp
  rw [h1, h2', sub_neg_eq_add, ← add_smul, hsum, one_smul]

end CFSG.HardMathSupport.Kantor79

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

theorem IsRefl.apply_eq_self_of_commute {t s : U ≃ₗ[ZMod p] U} (ht : IsRefl p t)
    (hs : IsRefl p s) (hcomm : t * s = s * t) (hne : HardMathSupport.Kantor79.movedSpace t ≠
      HardMathSupport.Kantor79.movedSpace s) :
    ∀ v ∈ HardMathSupport.Kantor79.movedSpace s, t v = v := by
  have hinv : ∀ w ∈ HardMathSupport.Kantor79.movedSpace s,
      t w ∈ HardMathSupport.Kantor79.movedSpace s :=
    HardMathSupport.Kantor79.apply_mem_movedSpace_of_commute hcomm.symm
  have hnotle : ¬ HardMathSupport.Kantor79.movedSpace t ≤
      HardMathSupport.Kantor79.movedSpace s := by
    intro hle
    have ht1 : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 1 := ht.2
    have hneV : HardMathSupport.Kantor79.movedSpace t ≠ ⊥ := by
      intro hbot
      rw [hbot, finrank_bot] at ht1
      exact Nat.zero_ne_one ht1
    obtain ⟨v, hv, hv0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hneV
    have hspanT : HardMathSupport.Kantor79.movedSpace t = ZMod p ∙ v :=
      eq_span_singleton_of_mem_of_finrank_eq_one ht.2 hv hv0
    have hvs : v ∈ HardMathSupport.Kantor79.movedSpace s := hle hv
    have hspanS : HardMathSupport.Kantor79.movedSpace s = ZMod p ∙ v :=
      eq_span_singleton_of_mem_of_finrank_eq_one hs.2 hvs hv0
    exact hne (hspanT.trans hspanS.symm)
  exact fun v hv => apply_eq_self_of_not_movedSpace_le ht.2 hinv hnotle hv

theorem IsRefl.comp_self_eq_id {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t) :
    (t : U →ₗ[ZMod p] U) ∘ₗ (t : U →ₗ[ZMod p] U) = 1 := by
  ext v
  have h := congrArg (fun e : U ≃ₗ[ZMod p] U => e v) ht.1
  simpa [LinearMap.comp_apply, LinearEquiv.mul_apply] using h

theorem IsRefl.isCompl_ker_sub_one_ker_add_one (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t) :
    IsCompl (LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1))
      (LinearMap.ker ((t : U →ₗ[ZMod p] U) + 1)) :=
  CFSG.StandardType.isCompl_ker_involution_of_two_ne_zero (ZMod.prime_ne_zero p 2 hp)
    (t : U →ₗ[ZMod p] U) ht.comp_self_eq_id

theorem IsRefl.movedSpace_eq_ker_add_one (hp : p ≠ 2) {t : U ≃ₗ[ZMod p] U}
    (ht : IsRefl p t) :
    HardMathSupport.Kantor79.movedSpace t =
      LinearMap.ker ((t : U →ₗ[ZMod p] U) + 1) :=
  movedSpace_eq_ker_add_one_of_mul_self (ZMod.prime_ne_zero p 2 hp) ht.1

theorem IsRefl.movedSpace_le_ker_of_commute {t s : U ≃ₗ[ZMod p] U} (ht : IsRefl p t)
    (hs : IsRefl p s) (hcomm : t * s = s * t) {W : Submodule (ZMod p) U}
    (htW : HardMathSupport.Kantor79.movedSpace t ≤ W)
    (hsW : ¬ HardMathSupport.Kantor79.movedSpace s ≤ W) :
    HardMathSupport.Kantor79.movedSpace s ≤
      LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1) := by
  have hne : HardMathSupport.Kantor79.movedSpace t ≠
      HardMathSupport.Kantor79.movedSpace s := fun heq => hsW (heq ▸ htW)
  intro v hv
  have hfix := IsRefl.apply_eq_self_of_commute ht hs hcomm hne v hv
  simpa [LinearMap.mem_ker, sub_eq_zero] using hfix

theorem IsRefl.not_movedSpace_le_ker_sub_one (hp : p ≠ 2) {t : U ≃ₗ[ZMod p] U}
    (ht : IsRefl p t) :
    ¬ HardMathSupport.Kantor79.movedSpace t ≤
      LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1) := by
  intro hle
  have hbot : HardMathSupport.Kantor79.movedSpace t = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro x hx
    have hfix : t x = x := by
      have := hle hx
      simpa [LinearMap.mem_ker, sub_eq_zero] using this
    have hneg := HardMathSupport.Kantor79.apply_eq_neg_of_mem_movedSpace ht.1 hx
    exact eq_zero_of_eq_neg (ZMod.prime_ne_zero p 2 hp) (hfix.symm.trans hneg)
  have hfin : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 0 := by
    rw [hbot, finrank_bot]
  have hone : Module.finrank (ZMod p) (HardMathSupport.Kantor79.movedSpace t) = 1 := ht.2
  omega

theorem IsRefl.finrank_ker_sub_one_add_one [Module.Finite (ZMod p) U]
    {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t) :
    Module.finrank (ZMod p) (LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1)) + 1 =
      Module.finrank (ZMod p) U := by
  have hrange : Module.finrank (ZMod p)
      (LinearMap.range ((t : U →ₗ[ZMod p] U) - 1)) = 1 := ht.2
  have hrk := LinearMap.finrank_range_add_finrank_ker ((t : U →ₗ[ZMod p] U) - 1)
  rw [hrange] at hrk
  omega

theorem IsRefl.movedSpace_eq_span (hp : p ≠ 2) {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t)
    {a : U} (ha : t a = -a) (ha0 : a ≠ 0) :
    HardMathSupport.Kantor79.movedSpace t = ZMod p ∙ a := by
  exact eq_span_singleton_of_mem_of_finrank_eq_one ht.2
    (HardMathSupport.Kantor79.mem_movedSpace_of_apply_eq_neg
      (ZMod.prime_ne_zero p 2 hp) ha) ha0

theorem coeff_mul_self_of_mul_self {t : U ≃ₗ[ZMod p] U} (ht : t * t = 1) {a : U} {c : ZMod p}
    (ha : t a = c • a) (ha0 : a ≠ 0) : c * c = 1 := by
  have htt : t (t a) = a := by
    have h : (t * t) a = (1 : U ≃ₗ[ZMod p] U) a := by rw [ht]
    simpa using h
  have hcc : (c * c) • a = a := by
    calc (c * c) • a = c • (c • a) := by rw [mul_smul]
      _ = c • t a := by rw [ha]
      _ = t (c • a) := (map_smul t c a).symm
      _ = t (t a) := by rw [ha]
      _ = a := htt
  have hsub : (c * c - 1) • a = 0 := by
    rw [sub_smul, one_smul, hcc, sub_self]
  exact sub_eq_zero.mp ((smul_eq_zero.mp hsub).resolve_right ha0)

theorem reflGen_reflSubgroupIn (F : Subgroup (U ≃ₗ[ZMod p] U)) (W : Submodule (ZMod p) U) :
    ReflGen p (reflSubgroupIn p F W) :=
  reflGen_closure_of_forall_isRefl fun _ hg => hg.2.1

theorem ReflGen.closure_insert_reflSubgroupIn {H : Subgroup (U ≃ₗ[ZMod p] U)}
    {b : U ≃ₗ[ZMod p] U} (hb : IsRefl p b) (W : Submodule (ZMod p) U) :
    ReflGen p (Subgroup.closure (insert b (reflSubgroupIn p H W : Set (U ≃ₗ[ZMod p] U)))) :=
  (reflGen_reflSubgroupIn H W).closure_insert hb

theorem apply_mem_ker_sub_one_of_commute {K E : Type*} [Field K] [AddCommGroup E]
    [Module K E] {r1 r2 : E ≃ₗ[K] E} (hcomm : r1 * r2 = r2 * r1) {X : Submodule K E}
    (hX : ∀ x ∈ X, (r2 : E →ₗ[K] E) x ∈ X) :
    ∀ w ∈ X ⊓ LinearMap.ker ((r1 : E →ₗ[K] E) - 1),
      (r2 : E →ₗ[K] E) w ∈ X ⊓ LinearMap.ker ((r1 : E →ₗ[K] E) - 1) := by
  intro w hw
  refine ⟨hX w hw.1, ?_⟩
  have hpt : ∀ v, (r2 : E →ₗ[K] E) ((r1 : E →ₗ[K] E) v) =
      (r1 : E →ₗ[K] E) ((r2 : E →ₗ[K] E) v) := fun v => by
    simpa [LinearEquiv.mul_apply] using congrArg (fun g : E ≃ₗ[K] E => g v) hcomm.symm
  have hcomp : (r2 : E →ₗ[K] E) ∘ₗ ((r1 : E →ₗ[K] E) - 1) =
      ((r1 : E →ₗ[K] E) - 1) ∘ₗ (r2 : E →ₗ[K] E) := by
    ext v
    simp only [LinearMap.comp_apply, LinearMap.sub_apply, Module.End.one_apply]
    rw [map_sub, hpt v]
  exact LinearMap.map_mem_ker_of_comp_eq (d := (r1 : E →ₗ[K] E) - 1)
    (e := (r1 : E →ₗ[K] E) - 1) (r2 : E →ₗ[K] E) hcomp hw.2

theorem mem_reflSubgroupIn_of_movedSpace_le {F : Subgroup (U ≃ₗ[ZMod p] U)}
    {t : U ≃ₗ[ZMod p] U} (htF : t ∈ F) (ht : IsRefl p t) {W : Submodule (ZMod p) U}
    (hle : HardMathSupport.Kantor79.movedSpace t ≤ W) : t ∈ reflSubgroupIn p F W :=
  Subgroup.subset_closure ⟨htF, ht, fun v => hle ⟨v, rfl⟩⟩

open Submodule in
theorem forall_mem_closure_mapsTo_of_forall {K E : Type*} [Field K] [AddCommGroup E]
    [Module K E] [FiniteDimensional K E] {S : Set (E ≃ₗ[K] E)} {W : Submodule K E}
    (hS : ∀ s ∈ S, ∀ w ∈ W, s w ∈ W) :
    ∀ g ∈ Subgroup.closure S, ∀ w ∈ W, g w ∈ W := by
  intro g hg
  induction hg using Subgroup.closure_induction with
  | mem t ht => exact hS t ht
  | one => intro w hw; simpa using hw
  | mul a b _ _ iha ihb => intro w hw; exact iha (b w) (ihb w hw)
  | inv a _ iha =>
      intro w hw
      have hle : W.map (a : E →ₗ[K] E) ≤ W := Submodule.map_le_iff_le_comap.mpr iha
      have heq : W.map (a : E →ₗ[K] E) = W :=
        Submodule.eq_of_le_of_finrank_eq hle (LinearEquiv.finrank_map_eq a W)
      have hw' : w ∈ W.map (a : E →ₗ[K] E) := by rw [heq]; exact hw
      obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hw'
      simpa using hx

theorem IsRefl.finrank_inf_ker_sub_one_add_one (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {t : U ≃ₗ[ZMod p] U} (ht : IsRefl p t) {A : Submodule (ZMod p) U} {a : U}
    (haA : a ∈ A) (ha : a ∉ LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1)) :
    Module.finrank (ZMod p) ↥(A ⊓ LinearMap.ker ((t : U →ₗ[ZMod p] U) - 1)) + 1 =
      Module.finrank (ZMod p) ↥A := by
  obtain ⟨a₀, φ, hφ, rfl⟩ := (isRefl_iff hp t).mp ht
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have ha0 : a₀ ≠ 0 := by
    rintro rfl
    exact h2 (by rw [map_zero] at hφ; exact hφ.symm)
  have hker : LinearMap.ker ((Module.reflection hφ : U →ₗ[ZMod p] U) - 1) =
      LinearMap.ker φ := by
    ext v
    rw [LinearMap.mem_ker, LinearMap.mem_ker]
    have hval : ((Module.reflection hφ : U →ₗ[ZMod p] U) - 1) v = -(φ v • a₀) := by
      change Module.reflection hφ v - v = -(φ v • a₀)
      rw [Module.reflection_apply]
      abel
    rw [hval, neg_eq_zero, smul_eq_zero]
    exact ⟨fun h => h.elim id (fun h0 => absurd h0 ha0), Or.inl⟩
  rw [hker, inf_comm]
  refine Module.Dual.finrank_ker_inf_add_one (f := φ) (U := A) ?_
  intro hle
  exact ha (hker ▸ hle haA)

end CFSG.StandardType.ZS
