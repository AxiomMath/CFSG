module

public import CFSG.LocalAnalysis.StandardType.ZS.TableCommon
import CFSG.LocalAnalysis.StandardType.GGCoxeterLabelBasic
import CFSG.LocalAnalysis.StandardType.ZS.Basic

public section

namespace CFSG.StandardType.ZS

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private theorem one_add_pow_prime_of_square_zero {M : Module.End (ZMod p) U} (hM : M * M = 0) :
    (1 + M) ^ p = 1 := by
  have hpow : ∀ n : ℕ, (1 + M) ^ n = 1 + n • M := by
    intro n
    induction n with
    | zero => simp
    | succ n ih =>
      rw [pow_succ, ih, add_mul, one_mul, mul_add, mul_one, smul_mul_assoc, hM, smul_zero,
        add_zero, succ_nsmul]
      abel
  rw [hpow p, ← Nat.cast_smul_eq_nsmul (ZMod p) p M, ZMod.natCast_self, zero_smul, add_zero]

theorem orderOf_reflection_mul_dvd_of_four (hp : p ≠ 2) {a b : U}
    {φ ψ : Module.Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2) (h4 : φ b * ψ a = 4) :
    orderOf (Module.reflection hφ * Module.reflection hψ) ∣ p := by
  rw [orderOf_dvd_iff_pow_eq_one]
  exact CFSG.StandardType.reflection_mul_reflection_pow_char hφ hψ
    ((Fact.out : p.Prime).odd_of_ne_two hp) h4

theorem orderOf_reflection_mul_dvd_of_eq_zero {a b : U}
    {φ ψ : Module.Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2) (h0 : φ b = 0) :
    orderOf (Module.reflection hφ * Module.reflection hψ) ∣ 2 * p := by
  let g : U ≃ₗ[ZMod p] U := Module.reflection hφ * Module.reflection hψ
  change orderOf g ∣ 2 * p
  let M : Module.End (ZMod p) U := g
  have hN : ∀ z, (M ^ 2 - (1 : Module.End (ZMod p) U)) z = (ψ a * φ z) • b := by
    intro z
    change ((Module.reflection hφ * Module.reflection hψ : U ≃ₗ[ZMod p] U) ^ 2) z - z =
      (ψ a * φ z) • b
    rw [CFSG.StandardType.reflection_mul_reflection_sq_apply_of_eq_zero hφ hψ h0 z]
    abel
  have hM2 : (M ^ 2 - (1 : Module.End (ZMod p) U)) *
      (M ^ 2 - (1 : Module.End (ZMod p) U)) = 0 := by
    ext z
    rw [Module.End.mul_apply, hN z, hN ((ψ a * φ z) • b), LinearMap.zero_apply]
    simp [map_smul, smul_eq_mul, h0]
  have hEnd : ((M ^ 2) ^ p) = 1 := by
    have h := one_add_pow_prime_of_square_zero (M := M ^ 2 - (1 : Module.End (ZMod p) U)) hM2
    simpa [add_comm, sub_add_cancel] using h
  rw [orderOf_dvd_iff_pow_eq_one, pow_mul]
  apply LinearEquiv.toLinearMap_injective
  change (LinearEquiv.automorphismGroup.toLinearMapMonoidHom ((g ^ 2) ^ p)) =
    LinearEquiv.automorphismGroup.toLinearMapMonoidHom (1 : U ≃ₗ[ZMod p] U)
  rw [map_pow, map_pow, map_one]
  exact hEnd

private theorem isCompl_span_pair_ker_inf_ker (hp : p ≠ 2) {a b : U}
    {φ ψ : Module.Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2)
    (h4 : φ b * ψ a ≠ 4) :
    IsCompl (Submodule.span (ZMod p) {a, b}) (LinearMap.ker φ ⊓ LinearMap.ker ψ) := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hE : 4 - φ b * ψ a ≠ 0 := sub_ne_zero.mpr h4.symm
  refine ⟨?_, ?_⟩
  · rw [Submodule.disjoint_def]
    intro x hxW hxW'
    obtain ⟨c, d, hxcd⟩ := Submodule.mem_span_pair.mp hxW
    obtain ⟨hf, hg⟩ := Submodule.mem_inf.mp hxW'
    rw [LinearMap.mem_ker] at hf hg
    rw [← hxcd, map_add, map_smul, map_smul, hφ, smul_eq_mul, smul_eq_mul] at hf
    rw [← hxcd, map_add, map_smul, map_smul, hψ, smul_eq_mul, smul_eq_mul] at hg
    have hdE : d * (4 - φ b * ψ a) = 0 := by
      have h1 : (c * ψ a + d * 2) * 2 = 0 := by rw [hg]; ring
      have h1' : (c * 2 + d * φ b) * ψ a = 0 := by rw [hf]; ring
      calc d * (4 - φ b * ψ a)
          = (c * ψ a + d * 2) * 2 - (c * 2 + d * φ b) * ψ a := by ring
        _ = 0 := by rw [h1, h1']; ring
    have hd : d = 0 := (mul_eq_zero.mp hdE).resolve_right hE
    have hc : c = 0 := by
      rw [hd, zero_mul, add_zero] at hf
      exact (mul_eq_zero.mp hf).resolve_right h2
    rw [← hxcd, hc, hd, zero_smul, zero_smul, add_zero]
  · rw [codisjoint_iff, eq_top_iff]
    intro x _
    rw [Submodule.mem_sup]
    set c : ZMod p := (2 * φ x - φ b * ψ x) / (4 - φ b * ψ a) with hcdef
    set d : ZMod p := (2 * ψ x - ψ a * φ x) / (4 - φ b * ψ a) with hddef
    refine ⟨c • a + d • b, Submodule.mem_span_pair.mpr ⟨c, d, rfl⟩,
      x - (c • a + d • b), Submodule.mem_inf.mpr ⟨?_, ?_⟩, by abel⟩
    · have hφy : φ (c • a + d • b) = φ x := by
        rw [map_add, map_smul, map_smul, hφ, smul_eq_mul, smul_eq_mul, hcdef, hddef]
        field_simp [hE]
        ring_nf
      rw [LinearMap.mem_ker, map_sub, hφy]
      exact sub_self (φ x)
    · have hψy : ψ (c • a + d • b) = ψ x := by
        rw [map_add, map_smul, map_smul, hψ, smul_eq_mul, smul_eq_mul, hcdef, hddef]
        field_simp [hE]
        ring_nf
      rw [LinearMap.mem_ker, map_sub, hψy]
      exact sub_self (ψ x)


private theorem root_mem_of_reflection_mem {u x : U} {χ : Module.Dual (ZMod p) U}
    {B : Subgroup (U ≃ₗ[ZMod p] U)} (hχ : χ u = 2) (hr : Module.reflection hχ ∈ B)
    {X : Submodule (ZMod p) U} (hX : ∀ h ∈ B, ∀ y ∈ X, h y ∈ X) (hxX : x ∈ X)
    (hχx : χ x ≠ 0) : u ∈ X := by
  have hru : Module.reflection hχ x ∈ X := hX _ hr x hxX
  have hmem : x - Module.reflection hχ x ∈ X := X.sub_mem hxX hru
  have heq : x - Module.reflection hχ x = χ x • u := by rw [Module.reflection_apply]; abel
  rw [heq] at hmem
  have h := X.smul_mem ((χ x)⁻¹) hmem
  rwa [inv_smul_smul₀ hχx] at h

private theorem mem_left_of_mem_right {a b x : U} {φ : Module.Dual (ZMod p) U}
    {X : Submodule (ZMod p) U} (hα : φ b ≠ 0) (hxX : x ∈ X) (hbX : b ∈ X) {c d : ZMod p}
    (hxcd : c • a + d • b = x) (hx0 : x ≠ 0) (hφx : φ x = 0) : a ∈ X := by
  have hca : c • a ∈ X := by
    have hxdb : x - d • b = c • a := by rw [← hxcd]; abel
    exact hxdb ▸ X.sub_mem hxX (X.smul_mem d hbX)
  by_cases hc0 : c = 0
  · exfalso
    have hd0 : d ≠ 0 := by
      intro hd
      exact hx0 (by rw [← hxcd, hc0, hd, zero_smul, zero_smul, add_zero])
    have hdφ : d * φ b = 0 := by
      have h := hφx
      rw [← hxcd, hc0] at h
      simpa [map_add, map_smul, smul_eq_mul] using h
    exact hα ((mul_eq_zero.mp hdφ).resolve_left hd0)
  · have h := X.smul_mem (c⁻¹) hca
    rwa [inv_smul_smul₀ hc0] at h

private theorem mem_right_of_mem_left {a b x : U} {ψ : Module.Dual (ZMod p) U}
    {X : Submodule (ZMod p) U} (hβ : ψ a ≠ 0) (hxX : x ∈ X) (haX : a ∈ X) {c d : ZMod p}
    (hxcd : c • a + d • b = x) (hx0 : x ≠ 0) (hψx : ψ x = 0) : b ∈ X := by
  have hdb : d • b ∈ X := by
    have hxca : x - c • a = d • b := by rw [← hxcd]; abel
    exact hxca ▸ X.sub_mem hxX (X.smul_mem c haX)
  by_cases hd0 : d = 0
  · exfalso
    have hc0 : c ≠ 0 := by
      intro hc
      exact hx0 (by rw [← hxcd, hc, hd0, zero_smul, zero_smul, add_zero])
    have hcψ : c * ψ a = 0 := by
      have h := hψx
      rw [← hxcd, hd0] at h
      simpa [map_add, map_smul, smul_eq_mul] using h
    exact hβ ((mul_eq_zero.mp hcψ).resolve_left hc0)
  · have h := X.smul_mem (d⁻¹) hdb
    rwa [inv_smul_smul₀ hd0] at h

private theorem pair_mem_of_invariant (hp : p ≠ 2) {a b : U}
    {φ ψ : Module.Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2) (hα : φ b ≠ 0)
    (hβ : ψ a ≠ 0) (h4 : φ b * ψ a ≠ 4) {X : Submodule (ZMod p) U}
    (hXW : X ≤ Submodule.span (ZMod p) {a, b}) {x : U} (hxX : x ∈ X) (hx0 : x ≠ 0)
    (ha_of : φ x ≠ 0 → a ∈ X) (hb_of : ψ x ≠ 0 → b ∈ X) : a ∈ X ∧ b ∈ X := by
  obtain ⟨c, d, hxcd⟩ := Submodule.mem_span_pair.mp (hXW hxX)
  by_cases hφx : φ x = 0
  · by_cases hψx : ψ x = 0
    · exfalso
      have hxW' : x ∈ LinearMap.ker φ ⊓ LinearMap.ker ψ :=
        Submodule.mem_inf.mpr ⟨LinearMap.mem_ker.mpr hφx, LinearMap.mem_ker.mpr hψx⟩
      have hdisj := (isCompl_span_pair_ker_inf_ker hp hφ hψ h4).1
      exact hx0 (by simpa using hdisj.le_bot ⟨hXW hxX, hxW'⟩)
    · exact ⟨mem_left_of_mem_right hα hxX (hb_of hψx) hxcd hx0 hφx, hb_of hψx⟩
  · have haX : a ∈ X := ha_of hφx
    by_cases hψx : ψ x = 0
    · exact ⟨haX, mem_right_of_mem_left hβ hxX haX hxcd hx0 hψx⟩
    · exact ⟨haX, hb_of hψx⟩

private theorem span_pair_le_of_invariant (hp : p ≠ 2) {a b : U}
    {φ ψ : Module.Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2) (hα : φ b ≠ 0)
    (hβ : ψ a ≠ 0) (h4 : φ b * ψ a ≠ 4) {X : Submodule (ZMod p) U}
    (hXW : X ≤ Submodule.span (ZMod p) {a, b})
    (hXinv : ∀ h ∈ Subgroup.closure {Module.reflection hφ, Module.reflection hψ},
      ∀ y ∈ X, h y ∈ X)
    {x : U} (hxX : x ∈ X) (hx0 : x ≠ 0) :
    Submodule.span (ZMod p) {a, b} ≤ X := by
  have ha_of (hφx : φ x ≠ 0) : a ∈ X :=
    root_mem_of_reflection_mem hφ (Subgroup.subset_closure (by simp)) hXinv hxX hφx
  have hb_of (hψx : ψ x ≠ 0) : b ∈ X :=
    root_mem_of_reflection_mem hψ (Subgroup.subset_closure (by simp)) hXinv hxX hψx
  have key := pair_mem_of_invariant hp hφ hψ hα hβ h4 hXW hxX hx0 ha_of hb_of
  refine Submodule.span_le.mpr ?_
  rintro y hy
  rcases (by simpa using hy : y = a ∨ y = b) with rfl | rfl
  · exact key.1
  · exact key.2


private theorem linearIndependent_pair_of_pairing {a b : U} {φ ψ : Module.Dual (ZMod p) U}
    (hφ : φ a = 2) (hψ : ψ b = 2) (h4 : φ b * ψ a ≠ 4) (ha : a ≠ 0) :
    LinearIndependent (ZMod p) ![a, b] := by
  rw [LinearIndependent.pair_iff' ha]
  intro c hc
  have hφb : φ b = c * 2 := by rw [← hc, map_smul, hφ, smul_eq_mul]
  have hψa : c * ψ a = 2 := by
    have h := congrArg ψ hc
    simpa [map_smul, hψ, smul_eq_mul] using h
  have h4' : φ b * ψ a = 4 := by
    rw [hφb]
    calc (c * 2) * ψ a = 2 * (c * ψ a) := by ring
      _ = 4 := by rw [hψa]; ring
  exact h4 h4'

private theorem finrank_span_pair_of_linearIndependent {a b : U}
    (hli : LinearIndependent (ZMod p) ![a, b]) :
    Module.finrank (ZMod p) (Submodule.span (ZMod p) {a, b}) = 2 := by
  rw [show ({a, b} : Set U) = Set.range ![a, b] by
    rw [Matrix.range_cons, Matrix.range_cons, Matrix.range_empty, Set.union_empty,
      Set.singleton_union]]
  simpa using finrank_span_eq_card hli

private theorem map_reflection_le_span_pair (u v : U) {χ : Module.Dual (ZMod p) U}
    (hχ : χ u = 2) :
    Submodule.map (Module.reflection hχ : U →ₗ[ZMod p] U) (Submodule.span (ZMod p) {u, v}) ≤
      Submodule.span (ZMod p) {u, v} := by
  rw [Submodule.map_span, Submodule.span_le]
  rintro y ⟨w, hw, rfl⟩
  rcases (by simpa using hw : w = u ∨ w = v) with hwu | hwv
  · rw [hwu]
    change Module.reflection hχ u ∈ Submodule.span (ZMod p) {u, v}
    rw [Module.reflection_apply_self]
    exact Submodule.neg_mem _ (Submodule.subset_span (by simp))
  · rw [hwv]
    change Module.reflection hχ v ∈ Submodule.span (ZMod p) {u, v}
    rw [Module.reflection_apply]
    exact Submodule.sub_mem _ (Submodule.subset_span (by simp))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))

private theorem map_reflection_eq_span_pair (u v : U) {χ : Module.Dual (ZMod p) U}
    (hχ : χ u = 2)
    (hle : Submodule.map (Module.reflection hχ : U →ₗ[ZMod p] U) (Submodule.span (ZMod p) {u, v}) ≤
      Submodule.span (ZMod p) {u, v}) :
    Submodule.map (Module.reflection hχ : U →ₗ[ZMod p] U) (Submodule.span (ZMod p) {u, v}) =
      Submodule.span (ZMod p) {u, v} := by
  refine le_antisymm hle ?_
  intro y hy
  exact Submodule.mem_map.mpr ⟨Module.reflection hχ y,
    hle (Submodule.mem_map.mpr ⟨y, hy, rfl⟩), Module.involutive_reflection hχ y⟩

private theorem root_ne_zero_of_eq_two (hp : p ≠ 2) {a : U} {φ : Module.Dual (ZMod p) U}
    (hφ : φ a = 2) : a ≠ 0 := by
  intro h
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  rw [h, map_zero] at hφ
  exact h2 hφ.symm

private theorem map_pair_eq_span_pair {a b : U} {φ ψ : Module.Dual (ZMod p) U}
    (hφ : φ a = 2) (hψ : ψ b = 2) :
    Submodule.map (Module.reflection hφ : U →ₗ[ZMod p] U) (Submodule.span (ZMod p) {a, b}) =
        Submodule.span (ZMod p) {a, b} ∧
      Submodule.map (Module.reflection hψ : U →ₗ[ZMod p] U) (Submodule.span (ZMod p) {a, b}) =
        Submodule.span (ZMod p) {a, b} := by
  refine ⟨map_reflection_eq_span_pair a b hφ (map_reflection_le_span_pair a b hφ), ?_⟩
  have h := map_reflection_eq_span_pair b a hψ (map_reflection_le_span_pair b a hψ)
  rwa [show ({b, a} : Set U) = {a, b} from Set.pair_comm b a] at h

private theorem closure_pair_fixes_ker_inf {a b : U} {φ ψ : Module.Dual (ZMod p) U}
    (hφ : φ a = 2) (hψ : ψ b = 2) :
    ∀ h ∈ Subgroup.closure {Module.reflection hφ, Module.reflection hψ},
      ∀ w ∈ (LinearMap.ker φ ⊓ LinearMap.ker ψ : Submodule (ZMod p) U), h w = w := by
  have hsub : Subgroup.closure {Module.reflection hφ, Module.reflection hψ} ≤
      fixingSubgroup (U ≃ₗ[ZMod p] U)
        ((LinearMap.ker φ ⊓ LinearMap.ker ψ : Submodule (ZMod p) U) : Set U) := by
    rw [Subgroup.closure_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · change Module.reflection hφ ∈ fixingSubgroup (U ≃ₗ[ZMod p] U)
        ((LinearMap.ker φ ⊓ LinearMap.ker ψ : Submodule (ZMod p) U) : Set U)
      rw [mem_fixingSubgroup_iff]
      intro w hw
      have hwφ : φ w = 0 := LinearMap.mem_ker.mp hw.1
      change Module.reflection hφ w = w
      rw [Module.reflection_apply, hwφ, zero_smul, sub_zero]
    · change Module.reflection hψ ∈ fixingSubgroup (U ≃ₗ[ZMod p] U)
        ((LinearMap.ker φ ⊓ LinearMap.ker ψ : Submodule (ZMod p) U) : Set U)
      rw [mem_fixingSubgroup_iff]
      intro w hw
      have hwψ : ψ w = 0 := LinearMap.mem_ker.mp hw.2
      change Module.reflection hψ w = w
      rw [Module.reflection_apply, hwψ, zero_smul, sub_zero]
  intro h hh w hw
  have h := (mem_fixingSubgroup_iff (M := U ≃ₗ[ZMod p] U)
    (s := ((LinearMap.ker φ ⊓ LinearMap.ker ψ : Submodule (ZMod p) U) : Set U))).mp
    (hsub hh) w hw
  simpa using h

private theorem closure_pair_preserves_span_pair {a b : U} {φ ψ : Module.Dual (ZMod p) U}
    (hφ : φ a = 2) (hψ : ψ b = 2)
    (hmr : Submodule.map (Module.reflection hφ : U →ₗ[ZMod p] U) (Submodule.span (ZMod p) {a, b}) =
      Submodule.span (ZMod p) {a, b})
    (hms : Submodule.map (Module.reflection hψ : U →ₗ[ZMod p] U) (Submodule.span (ZMod p) {a, b}) =
      Submodule.span (ZMod p) {a, b}) :
    ∀ h ∈ Subgroup.closure {Module.reflection hφ, Module.reflection hψ},
      ∀ w ∈ Submodule.span (ZMod p) {a, b}, h w ∈ Submodule.span (ZMod p) {a, b} := by
  let W : Submodule (ZMod p) U := Submodule.span (ZMod p) {a, b}
  have hmap_inv {x : U ≃ₗ[ZMod p] U}
      (hx : Submodule.map (x : U →ₗ[ZMod p] U) W = W) :
      Submodule.map ((x⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) W = W := by
    have hinj := Submodule.map_injective_of_injective (f := (x : U →ₗ[ZMod p] U)) x.injective
    apply hinj
    have hcomp : (x : U →ₗ[ZMod p] U) ∘ₗ ((x⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) =
        LinearMap.id := by
      change (x : U →ₗ[ZMod p] U) * ((x⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) = 1
      rw [← LinearEquiv.coe_toLinearMap_mul, mul_inv_cancel, LinearEquiv.coe_toLinearMap_one]
      rfl
    rw [← Submodule.map_comp, hcomp, Submodule.map_id, hx]
  let H : Subgroup (U ≃ₗ[ZMod p] U) :=
    { carrier := {h | Submodule.map (h : U →ₗ[ZMod p] U) W = W}
      one_mem' := by simp
      mul_mem' := by
        intro x y hx hy
        show Submodule.map ((x * y : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) W = W
        change Submodule.map ((x : U →ₗ[ZMod p] U).comp (y : U →ₗ[ZMod p] U)) W = W
        rw [Submodule.map_comp, hy, hx]
      inv_mem' := by
        intro x hx
        exact hmap_inv hx }
  have hsub : Subgroup.closure {Module.reflection hφ, Module.reflection hψ} ≤ H := by
    rw [Subgroup.closure_le]
    rintro g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hg
    rcases hg with rfl | rfl
    · exact hmr
    · exact hms
  intro h hh w hw
  have hmap : Submodule.map (h : U →ₗ[ZMod p] U) W = W := hsub hh
  have hmem : h w ∈ Submodule.map (h : U →ₗ[ZMod p] U) W :=
    Submodule.mem_map.mpr ⟨w, hw, rfl⟩
  rwa [hmap] at hmem

private theorem irredOnSection_span_pair_of_invariant (hp : p ≠ 2) {a b : U}
    {φ ψ : Module.Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2) (hα : φ b ≠ 0)
    (hβ : ψ a ≠ 0) (h4 : φ b * ψ a ≠ 4) :
    IrredOnSection (Subgroup.closure {Module.reflection hφ, Module.reflection hψ}) ⊥
      (Submodule.span (ZMod p) {a, b}) := by
  intro X _ hXW hXinv
  rcases eq_or_ne X ⊥ with hXbot | hXne
  · exact Or.inl hXbot
  · right
    obtain ⟨x, hxX, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hXne
    exact le_antisymm hXW (span_pair_le_of_invariant hp hφ hψ hα hβ h4 hXW hXinv hxX hx0)

private theorem reflection_apply_self_ne (hp : p ≠ 2) {a : U} {φ : Module.Dual (ZMod p) U}
    (hφ : φ a = 2) (ha : a ≠ 0) : Module.reflection hφ a ≠ a := by
  intro hcon
  have hra : Module.reflection hφ a = -a := Module.reflection_apply_self hφ
  rw [hra] at hcon
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have h2a : (2 : ZMod p) • a = 0 := by
    rw [two_smul]
    exact neg_eq_iff_add_eq_zero.mp hcon
  exact ha ((smul_eq_zero.mp h2a).resolve_left h2)

theorem splitSupport_closure_reflection_pair (hp : p ≠ 2) {a b : U}
    {φ ψ : Module.Dual (ZMod p) U} (hφ : φ a = 2) (hψ : ψ b = 2) (hα : φ b ≠ 0) (hβ : ψ a ≠ 0)
    (h4 : φ b * ψ a ≠ 4) :
    SplitSupport (Subgroup.closure {Module.reflection hφ, Module.reflection hψ}) 2 := by
  have ha := root_ne_zero_of_eq_two hp hφ
  have hli := linearIndependent_pair_of_pairing hφ hψ h4 ha
  obtain ⟨hmr, hms⟩ := map_pair_eq_span_pair hφ hψ
  have hfix := closure_pair_fixes_ker_inf hφ hψ
  have hinv := closure_pair_preserves_span_pair hφ hψ hmr hms
  have hirr := irredOnSection_span_pair_of_invariant hp hφ hψ hα hβ h4
  have key := splitSupport_of_isCompl
    (B := Subgroup.closure {Module.reflection hφ, Module.reflection hψ})
    (W := Submodule.span (ZMod p) {a, b}) (W' := LinearMap.ker φ ⊓ LinearMap.ker ψ)
    (isCompl_span_pair_ker_inf_ker hp hφ hψ h4) hfix hinv hirr
    ⟨Module.reflection hφ, Subgroup.subset_closure (by simp), a,
      Submodule.subset_span (by simp), reflection_apply_self_ne hp hφ ha⟩
  have hWfin : Module.finrank (ZMod p) (Submodule.span (ZMod p) {a, b}) = 2 :=
    finrank_span_pair_of_linearIndependent hli
  simpa [hWfin] using key


theorem splitSupport_closure_pair (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {x y : U ≃ₗ[ZMod p] U} (hx : IsRefl p x) (hy : IsRefl p y)
    (hcop : Nat.Coprime (orderOf (x * y)) p) (h2 : 2 < orderOf (x * y)) :
    SplitSupport (Subgroup.closure {x, y}) 2 := by
  obtain ⟨a, φ, hφ, rfl⟩ := (isRefl_iff hp x).mp hx
  obtain ⟨b, ψ, hψ, rfl⟩ := (isRefl_iff hp y).mp hy
  by_cases hα : φ b = 0
  · exfalso
    have hdvd : orderOf (Module.reflection hφ * Module.reflection hψ) ∣ 2 * p :=
      orderOf_reflection_mul_dvd_of_eq_zero hφ hψ hα
    have h1 : orderOf (Module.reflection hφ * Module.reflection hψ) ∣ 2 :=
      hcop.dvd_of_dvd_mul_right (by simpa using hdvd)
    have hle := Nat.le_of_dvd (by omega) h1
    omega
  · by_cases hβ : ψ a = 0
    · exfalso
      have hdvd : orderOf (Module.reflection hψ * Module.reflection hφ) ∣ 2 * p :=
        orderOf_reflection_mul_dvd_of_eq_zero (a := b) (b := a) (φ := ψ) (ψ := φ) hψ hφ hβ
      have hcomm : orderOf (Module.reflection hφ * Module.reflection hψ) =
          orderOf (Module.reflection hψ * Module.reflection hφ) := by
        rw [← orderOf_inv (Module.reflection hφ * Module.reflection hψ), mul_inv_rev,
          Module.reflection_inv, Module.reflection_inv]
      have hdvd' : orderOf (Module.reflection hφ * Module.reflection hψ) ∣ 2 * p := by
        rw [hcomm]
        exact hdvd
      have h1 : orderOf (Module.reflection hφ * Module.reflection hψ) ∣ 2 :=
        hcop.dvd_of_dvd_mul_right (by simpa using hdvd')
      have hle := Nat.le_of_dvd (by omega) h1
      omega
    · by_cases h4 : φ b * ψ a = 4
      · exfalso
        have hdvd : orderOf (Module.reflection hφ * Module.reflection hψ) ∣ p :=
          orderOf_reflection_mul_dvd_of_four hp hφ hψ h4
        have h1 : orderOf (Module.reflection hφ * Module.reflection hψ) ∣ 1 :=
          hcop.dvd_of_dvd_mul_right (m := 1) (by simpa using hdvd)
        have hle := Nat.le_of_dvd (by omega) h1
        omega
      · exact splitSupport_closure_reflection_pair hp hφ hψ hα hβ h4

theorem throughRefl_two_of_oneClass (hp : p ≠ 2) [Module.Finite (ZMod p) U]
    {J : Subgroup (U ≃ₗ[ZMod p] U)} (hone : OneClass p J) {x y : U ≃ₗ[ZMod p] U} (hx : x ∈ J)
    (hy : y ∈ J) (hrx : IsRefl p x) (hry : IsRefl p y)
    (hcop : Nat.Coprime (orderOf (x * y)) p) (h2 : 2 < orderOf (x * y)) :
    ThroughRefl p 2 J := by
  refine throughRefl_of_oneClass hone (B := Subgroup.closure {x, y}) ?_ ?_ hrx ?_ ?_
  · rw [Subgroup.closure_le]
    rintro t ht
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
    rcases ht with rfl | rfl
    · exact hx
    · exact hy
  · exact Subgroup.subset_closure (by simp)
  · rw [ReflGen]
    refine le_antisymm ?_ ?_
    · exact Subgroup.closure_mono (by
        rintro t ht
        simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at ht
        rcases ht with rfl | rfl
        · exact ⟨Subgroup.subset_closure (by simp), hrx⟩
        · exact ⟨Subgroup.subset_closure (by simp), hry⟩)
    · rw [Subgroup.closure_le]
      intro t ht
      exact ht.1
  · exact splitSupport_closure_pair hp hrx hry hcop h2

end CFSG.StandardType.ZS
