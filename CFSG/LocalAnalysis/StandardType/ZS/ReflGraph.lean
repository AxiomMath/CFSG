module

public import CFSG.LocalAnalysis.StandardType.GGSecFiveZSInputs
import CFSG.LocalAnalysis.StandardType.GGWitSlpmConjAux
import CFSG.LocalAnalysis.StandardType.ZS.CommutingRefl
import CFSG.LocalAnalysis.StandardType.GGWitSlpm

public section

namespace CFSG.StandardType.ZS

open Module

variable {p : ℕ} [Fact p.Prime] {U : Type} [AddCommGroup U] [Module (ZMod p) U]

private def reflGraphRel (A : Subgroup (U ≃ₗ[ZMod p] U)) :
    (U ≃ₗ[ZMod p] U) → (U ≃ₗ[ZMod p] U) → Prop :=
  fun x y => x ∈ A ∧ IsRefl p x ∧ y ∈ A ∧ IsRefl p y ∧ ¬ Commute x y

private def reflComponent (A : Subgroup (U ≃ₗ[ZMod p] U)) (r : U ≃ₗ[ZMod p] U) :
    Set (U ≃ₗ[ZMod p] U) :=
  {t | t ∈ A ∧ IsRefl p t ∧ Relation.ReflTransGen (reflGraphRel A) r t}

private structure ReflRoots (A : Subgroup (U ≃ₗ[ZMod p] U)) where
  root : {x : U ≃ₗ[ZMod p] U // x ∈ A ∧ IsRefl p x} → U
  form : {x : U ≃ₗ[ZMod p] U // x ∈ A ∧ IsRefl p x} → Dual (ZMod p) U
  form_root : ∀ t, form t (root t) = 2
  eq_reflection : ∀ t, t.1 = reflection (form_root t)

private def compRoot {A : Subgroup (U ≃ₗ[ZMod p] U)} {r : U ≃ₗ[ZMod p] U}
    (ρ : ReflRoots A) (u : {x : U ≃ₗ[ZMod p] U // x ∈ reflComponent A r}) : U :=
  ρ.root ⟨u.1, u.2.1, u.2.2.1⟩

private def compForm {A : Subgroup (U ≃ₗ[ZMod p] U)} {r : U ≃ₗ[ZMod p] U}
    (ρ : ReflRoots A) (u : {x : U ≃ₗ[ZMod p] U // x ∈ reflComponent A r}) : Dual (ZMod p) U :=
  ρ.form ⟨u.1, u.2.1, u.2.2.1⟩

private lemma compForm_root {A : Subgroup (U ≃ₗ[ZMod p] U)} {r : U ≃ₗ[ZMod p] U}
    (ρ : ReflRoots A) (u : {x : U ≃ₗ[ZMod p] U // x ∈ reflComponent A r}) :
    compForm ρ u (compRoot ρ u) = 2 :=
  ρ.form_root ⟨u.1, u.2.1, u.2.2.1⟩

private lemma comp_eq_reflection {A : Subgroup (U ≃ₗ[ZMod p] U)} {r : U ≃ₗ[ZMod p] U}
    (ρ : ReflRoots A) (u : {x : U ≃ₗ[ZMod p] U // x ∈ reflComponent A r}) :
    u.1 = reflection (compForm_root ρ u) :=
  ρ.eq_reflection ⟨u.1, u.2.1, u.2.2.1⟩

private def compSpan {A : Subgroup (U ≃ₗ[ZMod p] U)} (r : U ≃ₗ[ZMod p] U)
    (ρ : ReflRoots A) : Submodule (ZMod p) U :=
  Submodule.span (ZMod p) (Set.range (compRoot (r := r) ρ))

private lemma compRoot_ne_zero (hp : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {r : U ≃ₗ[ZMod p] U} (ρ : ReflRoots A)
    (u : {x : U ≃ₗ[ZMod p] U // x ∈ reflComponent A r}) : compRoot ρ u ≠ 0 := by
  intro h
  have hz := compForm_root ρ u
  rw [show compRoot ρ u = 0 from h, map_zero] at hz
  exact (ZMod.prime_ne_zero p 2 hp) hz.symm

private lemma commute_of_not_mem_component {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (r : U ≃ₗ[ZMod p] U) {t : U ≃ₗ[ZMod p] U} (htA : t ∈ A) (ht : IsRefl p t)
    (htC : t ∉ reflComponent A r) :
    ∀ u : {x : U ≃ₗ[ZMod p] U // x ∈ reflComponent A r}, Commute t u.1 := by
  intro u
  by_contra hnc
  apply htC
  exact ⟨htA, ht, u.2.2.2.tail ⟨u.2.1, u.2.2.1, htA, ht, fun h => hnc h.symm⟩⟩

private lemma fix_root_of_not_mem_component (hp : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (r : U ≃ₗ[ZMod p] U) (ρ : ReflRoots A) {t : U ≃ₗ[ZMod p] U} (htA : t ∈ A)
    (ht : IsRefl p t) (htC : t ∉ reflComponent A r) :
    ∀ u : {x : U ≃ₗ[ZMod p] U // x ∈ reflComponent A r},
      t (compRoot ρ u) = compRoot ρ u := by
  intro u
  have hcomm : Commute (reflection (ρ.form_root ⟨t, htA, ht⟩))
      (reflection (compForm_root ρ u)) := by
    rw [← ρ.eq_reflection ⟨t, htA, ht⟩, ← comp_eq_reflection ρ u]
    exact commute_of_not_mem_component r htA ht htC u
  have hne : reflection (ρ.form_root ⟨t, htA, ht⟩) ≠ reflection (compForm_root ρ u) := by
    intro h
    apply htC
    refine ⟨htA, ht, ?_⟩
    rw [show t = reflection (ρ.form_root ⟨t, htA, ht⟩) from ρ.eq_reflection ⟨t, htA, ht⟩, h,
      ← comp_eq_reflection ρ u]
    exact u.2.2.2
  have hz := apply_eq_zero_of_commute hp (ρ.form_root ⟨t, htA, ht⟩) (compForm_root ρ u) hcomm hne
  rw [show t = reflection (ρ.form_root ⟨t, htA, ht⟩) from ρ.eq_reflection ⟨t, htA, ht⟩,
    reflection_apply (compRoot ρ u) (ρ.form_root ⟨t, htA, ht⟩), hz, zero_smul, sub_zero]

private lemma component_maps_span {A : Subgroup (U ≃ₗ[ZMod p] U)} (r : U ≃ₗ[ZMod p] U)
    (ρ : ReflRoots A) (u : {x : U ≃ₗ[ZMod p] U // x ∈ reflComponent A r}) :
    compSpan r ρ ≤ Submodule.comap (u.1 : U →ₗ[ZMod p] U) (compSpan r ρ) := by
  dsimp only [compSpan]
  rw [Submodule.span_le]
  rintro x ⟨v, rfl⟩
  rw [SetLike.mem_coe, Submodule.mem_comap, comp_eq_reflection ρ u]
  change (reflection (compForm_root ρ u)) (compRoot ρ v) ∈
    Submodule.span (ZMod p) (Set.range (compRoot (r := r) ρ))
  rw [reflection_apply (compRoot ρ v) (compForm_root ρ u)]
  exact Submodule.sub_mem _ (Submodule.subset_span ⟨v, rfl⟩)
    (Submodule.smul_mem _ _ (Submodule.subset_span ⟨u, rfl⟩))

private lemma component_fixes_span (hp : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (r : U ≃ₗ[ZMod p] U) (ρ : ReflRoots A) {t : U ≃ₗ[ZMod p] U} (htA : t ∈ A)
    (ht : IsRefl p t) (htC : t ∉ reflComponent A r) :
    compSpan r ρ ≤ LinearMap.ker ((t : U →ₗ[ZMod p] U) - LinearMap.id) := by
  dsimp only [compSpan]
  rw [Submodule.span_le]
  rintro x ⟨u, rfl⟩
  rw [SetLike.mem_coe, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply]
  change (t : U →ₗ[ZMod p] U) (compRoot ρ u) - compRoot ρ u = 0
  rw [show (t : U →ₗ[ZMod p] U) (compRoot ρ u) = compRoot ρ u from
    fix_root_of_not_mem_component hp r ρ htA ht htC u, sub_self]

private lemma refl_mem_stabilizer [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (r : U ≃ₗ[ZMod p] U) (ρ : ReflRoots A)
    {t : U ≃ₗ[ZMod p] U} (htA : t ∈ A) (ht : IsRefl p t) :
    (compSpan r ρ).map (t : U →ₗ[ZMod p] U) = compSpan r ρ := by
  by_cases htC : t ∈ reflComponent A r
  · have hle : (compSpan r ρ).map (t : U →ₗ[ZMod p] U) ≤ compSpan r ρ := by
      rw [Submodule.map_le_iff_le_comap]
      intro w hw
      exact component_maps_span r ρ ⟨t, htC⟩ hw
    have hfin : Module.finrank (ZMod p) ((compSpan r ρ).map (t : U →ₗ[ZMod p] U)) =
        Module.finrank (ZMod p) (compSpan r ρ) :=
      (Submodule.equivMapOfInjective (t : U →ₗ[ZMod p] U) (t : U ≃ₗ[ZMod p] U).injective
        (compSpan r ρ)).finrank_eq.symm
    exact Submodule.eq_of_le_of_finrank_eq hle hfin
  · have hfix : ∀ w ∈ compSpan r ρ, (t : U →ₗ[ZMod p] U) w = w := fun w hw => by
      have := component_fixes_span hp r ρ htA ht htC hw
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
      exact this
    apply le_antisymm
    · rw [Submodule.map_le_iff_le_comap]
      intro w hw
      rw [Submodule.mem_comap, hfix w hw]
      exact hw
    · intro w hw
      rw [Submodule.mem_map]
      exact ⟨w, hw, hfix w hw⟩

private def spanStabilizer {A : Subgroup (U ≃ₗ[ZMod p] U)} (r : U ≃ₗ[ZMod p] U)
    (ρ : ReflRoots A) : Subgroup (U ≃ₗ[ZMod p] U) :=
  { carrier := {g | (compSpan r ρ).map (g : U →ₗ[ZMod p] U) = compSpan r ρ}
    mul_mem' := by
      intro g h hg hh
      show Submodule.map ((g * h : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) (compSpan r ρ) = compSpan r ρ
      rw [LinearEquiv.coe_toLinearMap_mul, Module.End.mul_eq_comp, Submodule.map_comp, hh, hg]
    one_mem' := by
      show Submodule.map ((1 : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) (compSpan r ρ) = compSpan r ρ
      simp
    inv_mem' := by
      intro g hg
      have hcomp : (((g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)).comp
          (g : U →ₗ[ZMod p] U) = LinearMap.id := by
        ext v; simp
      calc Submodule.map ((g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) (compSpan r ρ)
          = (Submodule.map (g : U →ₗ[ZMod p] U) (compSpan r ρ)).map
              ((g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) := by rw [hg]
        _ = Submodule.map ((((g⁻¹ : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U)).comp
              (g : U →ₗ[ZMod p] U)) (compSpan r ρ) := by rw [← Submodule.map_comp]
        _ = Submodule.map LinearMap.id (compSpan r ρ) := by rw [hcomp]
        _ = compSpan r ρ := Submodule.map_id _ }

private lemma span_roots_invariant [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p A) (r : U ≃ₗ[ZMod p] U)
    (ρ : ReflRoots A) : ∀ t ∈ A, ∀ w ∈ compSpan r ρ, t w ∈ compSpan r ρ := by
  have hclosure : Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ A ∧ IsRefl p t} ≤
      spanStabilizer r ρ :=
    (Subgroup.closure_le (spanStabilizer r ρ)).mpr
      (fun t ht => refl_mem_stabilizer hp r ρ ht.1 ht.2)
  have hA_le : A ≤ spanStabilizer r ρ := hgen.trans_le hclosure
  intro t htA w hw
  have htB : (compSpan r ρ).map (t : U →ₗ[ZMod p] U) = compSpan r ρ := hA_le htA
  have hmem : (t : U →ₗ[ZMod p] U) w ∈ (compSpan r ρ).map (t : U →ₗ[ZMod p] U) :=
    Submodule.mem_map_of_mem hw
  rwa [htB] at hmem

private lemma span_roots_eq_top [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p A)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤)
    (r : U ≃ₗ[ZMod p] U) (hr : r ∈ A) (hrr : IsRefl p r) (ρ : ReflRoots A) :
    compSpan r ρ = ⊤ := by
  have hInv := span_roots_invariant hp hgen r ρ
  have hne : compSpan r ρ ≠ ⊥ := by
    intro hbot
    have hmem : compRoot ρ ⟨r, hr, hrr, Relation.ReflTransGen.refl⟩ ∈ compSpan r ρ :=
      Submodule.subset_span ⟨_, rfl⟩
    rw [hbot] at hmem
    exact compRoot_ne_zero hp ρ ⟨r, hr, hrr, Relation.ReflTransGen.refl⟩ (by simpa using hmem)
  exact (hirr (compSpan r ρ) hInv).resolve_left hne

private lemma not_isRefl_of_forall_eq_self {t : U ≃ₗ[ZMod p] U}
    (hfix : ∀ w : U, (t : U →ₗ[ZMod p] U) w = w) : ¬ IsRefl p t := by
  intro ht
  have hrange : LinearMap.range ((t : U →ₗ[ZMod p] U) - LinearMap.id) = ⊥ := by
    rw [Submodule.eq_bot_iff]
    intro v hv
    obtain ⟨x, rfl⟩ := hv
    rw [LinearMap.sub_apply, LinearMap.id_apply, hfix x, sub_self]
  have h1 : Module.finrank (ZMod p) (LinearMap.range ((t : U →ₗ[ZMod p] U) - LinearMap.id)) = 1 :=
    ht.2
  rw [hrange, finrank_bot] at h1
  omega

theorem reflTransGen_not_commute [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p A)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤)
    {r s : U ≃ₗ[ZMod p] U} (hr : r ∈ A) (hrr : IsRefl p r) (hs : s ∈ A) (hss : IsRefl p s) :
    Relation.ReflTransGen
      (fun x y : U ≃ₗ[ZMod p] U => x ∈ A ∧ IsRefl p x ∧ y ∈ A ∧ IsRefl p y ∧ ¬ Commute x y)
      r s := by
  have h2 : (2 : ZMod p) ≠ 0 := ZMod.prime_ne_zero p 2 hp
  have hroot : ∀ t : {x : U ≃ₗ[ZMod p] U // x ∈ A ∧ IsRefl p x},
      ∃ (a : U) (φ : Dual (ZMod p) U) (hφ : φ a = 2), t.1 = reflection hφ := by
    rintro ⟨t, htA, ht⟩
    obtain ⟨a, φ, hφ, h⟩ := wSlpmC_isRefl_form h2 t ht
    exact ⟨a, φ, hφ, LinearEquiv.ext h⟩
  choose a φ hφ heq using hroot
  let ρ : ReflRoots A := { root := a, form := φ, form_root := hφ, eq_reflection := heq }
  have hWtop : compSpan r ρ = ⊤ := span_roots_eq_top hp hgen hirr r hr hrr ρ
  have hsC : s ∈ reflComponent A r := by
    by_contra hsC
    have hfix : ∀ w : U, (s : U →ₗ[ZMod p] U) w = w := by
      intro w
      have hw : w ∈ compSpan r ρ := by rw [hWtop]; trivial
      have := component_fixes_span hp r ρ hs hss hsC hw
      rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
      exact this
    exact not_isRefl_of_forall_eq_self hfix hss
  exact hsC.2.2

private lemma orderOf_mul_eq_three [Module.Finite (ZMod p) U] {x y : U ≃ₗ[ZMod p] U}
    (hx2 : x * x = 1) (hy2 : y * y = 1) (hnc : ¬ Commute x y)
    (hle : orderOf (x * y) ≤ 3) : orderOf (x * y) = 3 := by
  have : Finite U := Module.finite_of_finite (ZMod p)
  have : Fintype U := Fintype.ofFinite U
  have : Finite (U ≃ₗ[ZMod p] U) :=
    Finite.of_injective (fun e : U ≃ₗ[ZMod p] U => (e : U → U))
      (fun e₁ e₂ h => LinearEquiv.ext (congrFun h))
  have hpos : 0 < orderOf (x * y) := orderOf_pos _
  have hne1 : orderOf (x * y) ≠ 1 := by
    intro h1
    have hyx : y = x := by
      have h := congrArg (fun z => x * z) (orderOf_eq_one_iff.mp h1)
      rw [mul_one] at h
      rw [← mul_assoc, hx2, one_mul] at h
      exact h
    exact hnc (by rw [hyx])
  have hne2 : orderOf (x * y) ≠ 2 := by
    intro h2
    have hsq : (x * y) * (x * y) = 1 := by
      have := pow_orderOf_eq_one (x * y)
      rwa [h2] at this
    have hinvx : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
    have hinvy : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
    have h1 : (x * y)⁻¹ = x * y := inv_eq_of_mul_eq_one_left hsq
    rw [mul_inv_rev, hinvx, hinvy] at h1
    exact hnc h1.symm
  omega

private lemma conj_mul_inv_of_orderOf_eq_three {x y : U ≃ₗ[ZMod p] U}
    (hx2 : x * x = 1) (hy2 : y * y = 1) (h3 : orderOf (x * y) = 3) :
    (x * y) * x * (x * y)⁻¹ = y := by
  have hinvx : x⁻¹ = x := inv_eq_of_mul_eq_one_right hx2
  have hinvy : y⁻¹ = y := inv_eq_of_mul_eq_one_right hy2
  have hpow3 : (x * y) ^ 3 = 1 := by
    have := pow_orderOf_eq_one (x * y)
    rwa [h3] at this
  have hsq : (x * y) * (x * y) = y * x := by
    have h1 : ((x * y) * (x * y)) * (x * y) = 1 := by
      simpa [pow_succ, pow_two, mul_assoc] using hpow3
    have h2 : (x * y) * (x * y) = (x * y)⁻¹ := (mul_eq_one_iff_eq_inv.mp h1)
    rw [mul_inv_rev, hinvx, hinvy] at h2
    exact h2
  have hxyx : x * y * x = y * x * y := by
    have := congrArg (fun z => z * y) hsq
    simpa [mul_assoc, hy2] using this
  rw [mul_inv_rev, hinvx, hinvy, hxyx]
  calc (y * x * y) * (y * x) = y * x * (y * y) * x := by group
    _ = y * x * 1 * x := by rw [hy2]
    _ = y * (x * x) := by group
    _ = y * 1 := by rw [hx2]
    _ = y := mul_one y

theorem exists_conj_of_orderOf_mul_le_three [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p A)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤)
    (hd : ∀ x ∈ A, ∀ y ∈ A, IsRefl p x → IsRefl p y → orderOf (x * y) ≤ 3)
    {r s : U ≃ₗ[ZMod p] U} (hr : r ∈ A) (hrr : IsRefl p r) (hs : s ∈ A) (hss : IsRefl p s) :
    ∃ g ∈ A, g * r * g⁻¹ = s := by
  let S : (U ≃ₗ[ZMod p] U) → (U ≃ₗ[ZMod p] U) → Prop := fun x y => ∃ g ∈ A, g * x * g⁻¹ = y
  have hedge : ∀ x y, x ∈ A ∧ IsRefl p x ∧ y ∈ A ∧ IsRefl p y ∧ ¬ Commute x y → S x y := by
    rintro x y ⟨hxA, hx, hyA, hy, hnc⟩
    exact ⟨x * y, mul_mem hxA hyA,
      conj_mul_inv_of_orderOf_eq_three hx.1 hy.1
        (orderOf_mul_eq_three hx.1 hy.1 hnc (hd x hxA y hyA hx hy))⟩
  have hS_refl : ∀ x, S x x := fun x => ⟨1, one_mem _, by simp⟩
  have hS_trans : ∀ x y z, S x y → S y z → S x z := by
    rintro x y z ⟨g, hgA, hg⟩ ⟨h, hhA, hh⟩
    refine ⟨h * g, mul_mem hhA hgA, ?_⟩
    rw [mul_inv_rev]
    calc (h * g) * x * (g⁻¹ * h⁻¹) = h * (g * x * g⁻¹) * h⁻¹ := by group
      _ = h * y * h⁻¹ := by rw [hg]
      _ = z := hh
  exact (reflTransGen_not_commute hp hgen hirr hr hrr hs hss).head_induction_on
    (motive := fun a _ => S a s) (hS_refl s)
    (fun {a c} hac _ ih => hS_trans a c s (hedge a c hac) ih)

end CFSG.StandardType.ZS
