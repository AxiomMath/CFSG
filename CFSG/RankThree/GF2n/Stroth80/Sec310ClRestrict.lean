module

public import CFSG.RankThree.GF2n.Stroth80.Sec310ClPoint

public section

namespace CFSG.RankThree.GF2n.Stroth80.Classify

section Frame

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
  {F : LinearMap.BilinForm K V}

theorem frame_coord {e f x x' : V} (halt : F.IsAlt) (hef : F e f = 1) (hxx' : F x x' = 1)
    (hxe : F x e = 0) (hxf : F x f = 0) (hx'e : F x' e = 0) (hx'f : F x' f = 0) :
    ∀ u ∈ Submodule.span K ({e, f, x, x'} : Set V),
      u = F u f • e + F u e • f + F u x' • x + F u x • x' := by
  have hfe : F f e = 1 := by rw [form_comm halt]; exact hef
  have hxe' : F e x = 0 := by rw [form_comm halt]; exact hxe
  have hxf' : F f x = 0 := by rw [form_comm halt]; exact hxf
  have hx'e' : F e x' = 0 := by rw [form_comm halt]; exact hx'e
  have hx'f' : F f x' = 0 := by rw [form_comm halt]; exact hx'f
  have hx'x : F x' x = 1 := by rw [form_comm halt]; exact hxx'
  intro u hu
  induction hu using Submodule.span_induction with
  | mem y hy =>
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hy
    rcases hy with h | h | h | h <;> rw [h]
    · simp [hef, form_self halt, hx'e', hxe']
    · simp [hfe, form_self halt, hx'f', hxf']
    · simp [hxf, hxe, hxx', form_self halt]
    · simp [hx'f, hx'e, hx'x, form_self halt]
  | zero => simp
  | add a b _ _ ha hb =>
    simp only [map_add, LinearMap.add_apply, add_smul]
    linear_combination (norm := module) ha + hb
  | smul c a _ ha =>
    simp only [map_smul, LinearMap.smul_apply, smul_eq_mul]
    linear_combination (norm := module) c • ha

@[expose] def framePr (F : LinearMap.BilinForm K V) (e f x x' v : V) : V :=
  F v f • e + F v e • f + F v x' • x + F v x • x'

theorem framePr_form {e f x x' : V} (halt : F.IsAlt) (hef : F e f = 1) (hxx' : F x x' = 1)
    (hxe : F x e = 0) (hxf : F x f = 0) (hx'e : F x' e = 0) (hx'f : F x' f = 0) (v : V) :
    F (framePr F e f x x' v) e = F v e ∧ F (framePr F e f x x' v) f = F v f ∧
      F (framePr F e f x x' v) x = F v x ∧ F (framePr F e f x x' v) x' = F v x' := by
  have hfe : F f e = 1 := by rw [form_comm halt]; exact hef
  have hxe' : F e x = 0 := by rw [form_comm halt]; exact hxe
  have hxf' : F f x = 0 := by rw [form_comm halt]; exact hxf
  have hx'e' : F e x' = 0 := by rw [form_comm halt]; exact hx'e
  have hx'f' : F f x' = 0 := by rw [form_comm halt]; exact hx'f
  have hx'x : F x' x = 1 := by rw [form_comm halt]; exact hxx'
  unfold framePr
  refine ⟨?_, ?_, ?_, ?_⟩ <;>
    simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, hef, hfe,
      hxe, hxf, hx'e, hx'f, hxe', hxf', hx'e', hx'f', hxx', hx'x, form_self halt]

theorem frame_perp_span {U : Submodule K V} {e f x x' : V}
    (hUc : ∀ u ∈ U, u = F u f • e + F u e • f + F u x' • x + F u x • x') {w : V}
    (hwe : F w e = 0) (hwf : F w f = 0) (hwx : F w x = 0) (hwx' : F w x' = 0) :
    ∀ u ∈ U, F w u = 0 := by
  intro u hu
  calc F w u = F w (F u f • e + F u e • f + F u x' • x + F u x • x') :=
        congrArg (F w) (hUc u hu)
    _ = 0 := by simp [map_add, map_smul, hwe, hwf, hwx, hwx']

theorem stab_of_span {U : Submodule K V} {e f x x' : V} {g : V ≃ₗ[K] V}
    (hge : g e ∈ U) (hgf : g f ∈ U) (hgx : g x ∈ U) (hgx' : g x' ∈ U)
    (hspan : ∀ u ∈ U, ∃ a b c d : K, u = a • e + b • f + c • x + d • x') :
    ∀ u ∈ U, g u ∈ U := by
  intro u hu
  obtain ⟨a, b, c, d, rfl⟩ := hspan u hu
  simp only [map_add, map_smul]
  exact Submodule.add_mem U (Submodule.add_mem U (Submodule.add_mem U
    (Submodule.smul_mem U a hge) (Submodule.smul_mem U b hgf)) (Submodule.smul_mem U c hgx))
    (Submodule.smul_mem U d hgx')

theorem dual_coord {U : Submodule K V} {e f x x' : V} (hUe : e ∈ U) (hUf : f ∈ U) (hUx : x ∈ U)
    (hUx' : x' ∈ U) (hUc : ∀ u ∈ U, u = F u f • e + F u e • f + F u x' • x + F u x • x')
    (φ : Module.Dual K U) (v : U) :
    φ v = F (v : V) f * φ ⟨e, hUe⟩ + F (v : V) e * φ ⟨f, hUf⟩ + F (v : V) x' * φ ⟨x, hUx⟩ +
      F (v : V) x * φ ⟨x', hUx'⟩ := by
  have h : v = F (v : V) f • (⟨e, hUe⟩ : U) + F (v : V) e • (⟨f, hUf⟩ : U) +
      F (v : V) x' • (⟨x, hUx⟩ : U) + F (v : V) x • (⟨x', hUx'⟩ : U) :=
    Subtype.ext (by
      simp only [Submodule.coe_add, Submodule.coe_smul]
      exact hUc (v : V) v.2)
  calc φ v = φ (F (v : V) f • (⟨e, hUe⟩ : U) + F (v : V) e • (⟨f, hUf⟩ : U) +
      F (v : V) x' • (⟨x, hUx⟩ : U) + F (v : V) x • (⟨x', hUx'⟩ : U)) := congrArg φ h
    _ = F (v : V) f * φ ⟨e, hUe⟩ + F (v : V) e * φ ⟨f, hUf⟩ + F (v : V) x' * φ ⟨x, hUx⟩ +
        F (v : V) x * φ ⟨x', hUx'⟩ := by
      simp only [map_add, map_smul, smul_eq_mul]

end Frame

section Restrict

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
  {F : LinearMap.BilinForm K V}

@[expose] def restrictSub (U : Submodule K V) (B : Subgroup (V ≃ₗ[K] V)) :
    Subgroup (U ≃ₗ[K] U) where
  carrier := {r | ∃ g ∈ B, ∀ u : U, ((r u : U) : V) = g u}
  mul_mem' := by
    rintro r₁ r₂ ⟨g₁, hg₁, h₁⟩ ⟨g₂, hg₂, h₂⟩
    refine ⟨g₁ * g₂, B.mul_mem hg₁ hg₂, fun u => ?_⟩
    simp only [LinearEquiv.mul_apply]
    rw [h₁, h₂]
  one_mem' := ⟨1, B.one_mem, fun u => rfl⟩
  inv_mem' := by
    rintro r ⟨g, hg, h⟩
    refine ⟨g⁻¹, B.inv_mem hg, fun u => ?_⟩
    have hru : r (r⁻¹ u) = u := by simp
    have h' := h (r⁻¹ u)
    rw [hru] at h'
    rw [h']
    simp

theorem restrictSub_mono {U : Submodule K V} {B B' : Subgroup (V ≃ₗ[K] V)} (h : B ≤ B') :
    restrictSub U B ≤ restrictSub U B' := by
  rintro r ⟨g, hg, hr⟩
  exact ⟨g, h hg, hr⟩

theorem exists_restrict {U : Submodule K V} {g : V ≃ₗ[K] V} (hgU : ∀ u ∈ U, g u ∈ U)
    (hg2 : ∀ v, g (g v) = v) : ∃ r : U ≃ₗ[K] U, ∀ u : U, ((r u : U) : V) = g u :=
  ⟨LinearEquiv.ofInvolutive ((g : V →ₗ[K] V).restrict hgU) (fun u => Subtype.ext (hg2 (u : V))),
    fun u => rfl⟩

@[expose] def perpFixSub (F : LinearMap.BilinForm K V) (U : Submodule K V) :
    Subgroup (V ≃ₗ[K] V) where
  carrier := {g | ∀ w : V, (∀ u ∈ U, F w u = 0) → g w = w}
  mul_mem' := fun {a b} ha hb w hw => by
    simp only [LinearEquiv.mul_apply]
    rw [hb w hw, ha w hw]
  one_mem' := fun w _ => rfl
  inv_mem' := fun {g} hg w hw => by
    have h1 : g w = w := hg w hw
    calc g⁻¹ w = g⁻¹ (g w) := by rw [h1]
      _ = w := by simp

theorem fix_of_pointRad {U : Submodule K V} {p q : V} (halt : F.IsAlt) (hpq : F p q = 1)
    {g : V ≃ₗ[K] V} (hg : g ∈ pointRadSubgroup F p) (hω : g q - q ∈ U) (hUp : p ∈ U)
    (w : V) (hw : ∀ u ∈ U, F w u = 0) : g w = w := by
  rw [pointRad_apply_perp halt hpq hg w (hw p hUp), form_comm halt, hw _ hω, zero_smul,
    add_zero]

theorem restrict_mem_pointRad {U : Submodule K V} {p : V} (hp : p ∈ U) {g : V ≃ₗ[K] V}
    (hg : g ∈ pointRadSubgroup F p) {r : U ≃ₗ[K] U} (hr : ∀ u : U, ((r u : U) : V) = g u) :
    r ∈ pointRadSubgroup (F.compl₁₂ U.subtype U.subtype) ⟨p, hp⟩ := by
  obtain ⟨h1, h2, h3⟩ := hg
  refine ⟨fun u u' => ?_, ?_, fun v hv => ?_⟩
  · show F ((r u : U) : V) ((r u' : U) : V) = F (u : V) (u' : V)
    rw [hr u, hr u']
    exact h1 _ _
  · apply Subtype.ext
    show ((r ⟨p, hp⟩ : U) : V) = p
    rw [hr]
    exact h2
  · obtain ⟨c, hc⟩ := h3 (v : V) hv
    refine ⟨c, Subtype.ext ?_⟩
    rw [hr]
    simp only [Submodule.coe_add, Submodule.coe_smul]
    exact hc

end Restrict

section Dim4

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]
  {F : LinearMap.BilinForm K V}

theorem frame_nondeg {U : Submodule K V} {e f x x' : V} (halt : F.IsAlt) (hUe : e ∈ U)
    (hUf : f ∈ U) (hUx : x ∈ U) (hUx' : x' ∈ U)
    (hUc : ∀ u ∈ U, u = F u f • e + F u e • f + F u x' • x + F u x • x') :
    (F.compl₁₂ U.subtype U.subtype).Nondegenerate := by
  have hfU : ∀ a b : U, F.compl₁₂ U.subtype U.subtype a b = F.compl₁₂ U.subtype U.subtype b a :=
    fun a b => form_comm halt (a : V) (b : V)
  have hsep : ∀ u : U, (∀ u' : U, F.compl₁₂ U.subtype U.subtype u u' = 0) → u = 0 := by
    intro u hu
    have h1 : F (u : V) f = 0 := hu ⟨f, hUf⟩
    have h2 : F (u : V) e = 0 := hu ⟨e, hUe⟩
    have h3 : F (u : V) x' = 0 := hu ⟨x', hUx'⟩
    have h4 : F (u : V) x = 0 := hu ⟨x, hUx⟩
    apply Subtype.ext
    show (u : V) = 0
    calc (u : V) = F (u : V) f • e + F (u : V) e • f + F (u : V) x' • x + F (u : V) x • x' :=
          hUc (u : V) u.2
      _ = 0 := by simp [h1, h2, h3, h4]
  exact ⟨hsep, fun u hu => hsep u (fun u' => (hfU u u').trans (hu u'))⟩

theorem frame_alt (halt : F.IsAlt) (U : Submodule K V) : (F.compl₁₂ U.subtype U.subtype).IsAlt :=
  fun u => halt (u : V)

theorem frame_linInd {e f x x' : V} (halt : F.IsAlt) (hef : F e f = 1) (hxx' : F x x' = 1)
    (hxe : F x e = 0) (hxf : F x f = 0) (hx'e : F x' e = 0) (hx'f : F x' f = 0) :
    LinearIndependent K ![e, f, x, x'] := by
  have hfe : F f e = 1 := by rw [form_comm halt]; exact hef
  have hxe' : F e x = 0 := by rw [form_comm halt]; exact hxe
  have hxf' : F f x = 0 := by rw [form_comm halt]; exact hxf
  have hx'e' : F e x' = 0 := by rw [form_comm halt]; exact hx'e
  have hx'f' : F f x' = 0 := by rw [form_comm halt]; exact hx'f
  have hx'x : F x' x = 1 := by rw [form_comm halt]; exact hxx'
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have key : g 0 • e + g 1 • f + g 2 • x + g 3 • x' = 0 := by
    simpa [Fin.sum_univ_four] using hg
  have c0 : g 0 = 0 := by
    have := congrArg (fun v => F v f) key
    simpa [map_add, map_smul, hef, form_self halt, hxf, hx'f] using this
  have c1 : g 1 = 0 := by
    have := congrArg (fun v => F v e) key
    simpa [map_add, map_smul, hfe, form_self halt, hxe, hx'e] using this
  have c2 : g 2 = 0 := by
    have := congrArg (fun v => F v x') key
    simpa [map_add, map_smul, hx'e', hx'f', hxx', form_self halt] using this
  have c3 : g 3 = 0 := by
    have := congrArg (fun v => F v x) key
    simpa [map_add, map_smul, hxe', hxf', hx'x, form_self halt] using this
  intro i
  fin_cases i <;> simp [c0, c1, c2, c3]

theorem frame_finrank {e f x x' : V} (halt : F.IsAlt) (hef : F e f = 1) (hxx' : F x x' = 1)
    (hxe : F x e = 0) (hxf : F x f = 0) (hx'e : F x' e = 0) (hx'f : F x' f = 0) :
    Module.finrank K (Submodule.span K ({e, f, x, x'} : Set V)) = 4 := by
  have h := finrank_span_eq_card (frame_linInd halt hef hxx' hxe hxf hx'e hx'f)
  have hrange : Set.range ![e, f, x, x'] = ({e, f, x, x'} : Set V) := by
    ext y
    simp [Matrix.range_cons, Matrix.range_empty]
    tauto
  rw [hrange] at h
  simpa using h

end Dim4

section Transv

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]

@[expose] def transvMap (B : LinearMap.BilinForm K V) (p : V) (c : K) : V →ₗ[K] V :=
  LinearMap.id + (c • B.flip p).smulRight p

theorem transvMap_apply (B : LinearMap.BilinForm K V) (p : V) (c : K) (u : V) :
    transvMap B p c u = u + (c * B u p) • p := by
  simp [transvMap]

theorem transvMap_invol {B : LinearMap.BilinForm K V} (halt : B.IsAlt) {p : V} (c : K) :
    Function.Involutive (transvMap B p c) := by
  intro u
  have hpp : B p p = 0 := halt p
  have h1 : B (transvMap B p c u) p = B u p := by
    rw [transvMap_apply]
    simp [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, hpp]
  rw [transvMap_apply, h1, transvMap_apply, add_assoc, vec_add_self K, add_zero]

theorem transvMap_isom {B : LinearMap.BilinForm K V} (halt : B.IsAlt) {p : V} (c : K)
    (x y : V) : B (transvMap B p c x) (transvMap B p c y) = B x y := by
  rw [transvMap_apply, transvMap_apply]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    form_self halt]
  rw [form_comm halt p y]
  linear_combination (c * B x p * B y p) * two_eq_zero_K (K := K)

end Transv

section Quad

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]

open _root_.Classical in
@[expose] noncomputable def qExt {U : Submodule K V} (Q : QuadraticForm K U) (v : V) : K :=
  if h : v ∈ U then Q ⟨v, h⟩ else 0

theorem qExt_mem {U : Submodule K V} (Q : QuadraticForm K U) {v : V} (h : v ∈ U) :
    qExt Q v = Q ⟨v, h⟩ :=
  dif_pos h

theorem qExt_smul {U : Submodule K V} (Q : QuadraticForm K U) {c : K} {u : V} (hu : u ∈ U) :
    qExt Q (c • u) = c ^ 2 * qExt Q u := by
  rw [qExt_mem Q (Submodule.smul_mem U c hu), qExt_mem Q hu]
  have h : (⟨c • u, Submodule.smul_mem U c hu⟩ : U) = c • (⟨u, hu⟩ : U) := Subtype.ext rfl
  rw [h, QuadraticMap.map_smul, smul_eq_mul]
  ring

theorem qExt_add {U : Submodule K V} (Q : QuadraticForm K U) {F : LinearMap.BilinForm K V}
    (hpol : ∀ a b : U, Q.polarBilin a b = F (a : V) (b : V)) {u u' : V} (hu : u ∈ U)
    (hu' : u' ∈ U) : qExt Q (u + u') = qExt Q u + qExt Q u' + F u u' := by
  rw [qExt_mem Q (Submodule.add_mem U hu hu'), qExt_mem Q hu, qExt_mem Q hu']
  have h : (⟨u + u', Submodule.add_mem U hu hu'⟩ : U) = ⟨u, hu⟩ + ⟨u', hu'⟩ :=
    Subtype.ext rfl
  have hp : QuadraticMap.polar Q ⟨u, hu⟩ ⟨u', hu'⟩ = F u u' := by
    rw [← QuadraticMap.polarBilin_apply_apply]
    exact hpol _ _
  rw [h, QuadraticMap.map_add Q ⟨u, hu⟩ ⟨u', hu'⟩, hp]

end Quad

section Elation

variable {K V : Type} [Field K] [CharP K 2] [AddCommGroup V] [Module K V]

theorem elation_restrict_A {F : LinearMap.BilinForm K V} (halt : F.IsAlt) {e f x x' : V}
    (hef : F e f = 1) {U : Submodule K V} (hUe : e ∈ U) (hUf : f ∈ U) (hUx : x ∈ U)
    (hUx' : x' ∈ U)
    (hUc : ∀ u ∈ U, u = F u f • e + F u e • f + F u x' • x + F u x • x')
    (A : Subgroup (V ≃ₗ[K] V)) (hA : A ≤ pointRadSubgroup F e)
    (hAfull : ∀ w ∈ Submodule.span K ({x, x'} : Set V), ∃ g ∈ A, ∃ c : K, g f - f = w + c • e)
    (hgU : ∀ g ∈ A, ∀ u ∈ U, g u ∈ U) (hg2 : ∀ g ∈ A, ∀ v, g (g v) = v) :
    ElationFull (F.compl₁₂ U.subtype U.subtype) (restrictSub U A) ⟨e, hUe⟩ := by
  intro φ hφ
  have hw : φ ⟨x', hUx'⟩ • x + φ ⟨x, hUx⟩ • x' ∈ Submodule.span K ({x, x'} : Set V) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  obtain ⟨g, hg, c, hgc⟩ := hAfull _ hw
  obtain ⟨r, hr⟩ := exists_restrict (hgU g hg) (hg2 g hg)
  refine ⟨r, ⟨g, hg, hr⟩, fun v hv => ?_⟩
  have hv' : F (v : V) e = 0 := hv
  have hgv := pointRad_apply_perp halt hef (hA hg) (v : V) hv'
  have hform : F (g f - f) (v : V) = φ v := by
    rw [hgc, dual_coord hUe hUf hUx hUx' hUc φ v, hφ]
    have h1 : F x (v : V) = F (v : V) x := form_comm halt x _
    have h2 : F x' (v : V) = F (v : V) x' := form_comm halt x' _
    have h3 : F e (v : V) = F (v : V) e := form_comm halt e _
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1,
      h2, h3, hv', zero_mul, mul_zero, add_zero, zero_add]
    ring
  apply Subtype.ext
  rw [hr v, Submodule.coe_add, Submodule.coe_smul, hgv, hform]

theorem elation_restrict_A' {F : LinearMap.BilinForm K V} (halt : F.IsAlt) {e f x x' : V}
    (hfe : F f e = 1) {U : Submodule K V} (hUe : e ∈ U) (hUf : f ∈ U) (hUx : x ∈ U)
    (hUx' : x' ∈ U)
    (hUc : ∀ u ∈ U, u = F u f • e + F u e • f + F u x' • x + F u x • x')
    (A' : Subgroup (V ≃ₗ[K] V)) (hA' : A' ≤ pointRadSubgroup F f)
    (hA'full : ∀ w ∈ Submodule.span K ({x, x'} : Set V), ∃ g ∈ A', ∃ c : K, g e - e = w + c • f)
    (hgU : ∀ g ∈ A', ∀ u ∈ U, g u ∈ U) (hg2 : ∀ g ∈ A', ∀ v, g (g v) = v) :
    ElationFull (F.compl₁₂ U.subtype U.subtype) (restrictSub U A') ⟨f, hUf⟩ := by
  intro φ hφ
  have hw : φ ⟨x', hUx'⟩ • x + φ ⟨x, hUx⟩ • x' ∈ Submodule.span K ({x, x'} : Set V) :=
    Submodule.add_mem _ (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
      (Submodule.smul_mem _ _ (Submodule.subset_span (by simp)))
  obtain ⟨g, hg, c, hgc⟩ := hA'full _ hw
  obtain ⟨r, hr⟩ := exists_restrict (hgU g hg) (hg2 g hg)
  refine ⟨r, ⟨g, hg, hr⟩, fun v hv => ?_⟩
  have hv' : F (v : V) f = 0 := hv
  have hgv := pointRad_apply_perp halt hfe (hA' hg) (v : V) hv'
  have hform : F (g e - e) (v : V) = φ v := by
    rw [hgc, dual_coord hUe hUf hUx hUx' hUc φ v, hφ]
    have h1 : F x (v : V) = F (v : V) x := form_comm halt x _
    have h2 : F x' (v : V) = F (v : V) x' := form_comm halt x' _
    have h4 : F f (v : V) = F (v : V) f := form_comm halt f _
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul, h1,
      h2, h4, hv', zero_mul, mul_zero, add_zero, zero_add]
    ring
  apply Subtype.ext
  rw [hr v, Submodule.coe_add, Submodule.coe_smul, hgv, hform]

end Elation

theorem lemmaPSub_of_lemmaP (hP : LemmaPStatement) {K V : Type} [Field K] [Finite K] [CharP K 2]
    [AddCommGroup V] [Module K V] [FiniteDimensional K V] {F : LinearMap.BilinForm K V}
    (hq : 4 ≤ Nat.card K) (hnd : F.Nondegenerate) (halt : F.IsAlt) {e f x x' : V}
    (hef : F e f = 1) (hxx' : F x x' = 1) (hxe : F x e = 0) (hxf : F x f = 0)
    (hx'e : F x' e = 0) (hx'f : F x' f = 0)
    (A A' : Subgroup (V ≃ₗ[K] V)) (hA : A ≤ pointRadSubgroup F e)
    (hA' : A' ≤ pointRadSubgroup F f)
    (hAω : ∀ g ∈ A, g f - f ∈ Submodule.span K {e, x, x'})
    (hA'ω : ∀ g ∈ A', g e - e ∈ Submodule.span K {f, x, x'})
    (hAfull : ∀ w ∈ Submodule.span K {x, x'}, ∃ g ∈ A, ∃ c : K, g f - f = w + c • e)
    (hA'full : ∀ w ∈ Submodule.span K {x, x'}, ∃ g ∈ A', ∃ c : K, g e - e = w + c • f) :
    (∀ c : K, ∃ g ∈ A ⊔ A', ∀ v, g v = v + (c * F v e) • e) ∨
      ∃ q : V → K,
        (∀ (c : K) (u : V), u ∈ Submodule.span K {e, f, x, x'} → q (c • u) = c ^ 2 * q u) ∧
        (∀ u u' : V, u ∈ Submodule.span K {e, f, x, x'} → u' ∈ Submodule.span K {e, f, x, x'} →
          q (u + u') = q u + q u' + F u u') ∧
        q e = 0 ∧ q f = 0 ∧ (∀ g ∈ A, q (g f) = q f) ∧ (∀ g ∈ A', q (g e) = q e) := by
  obtain ⟨U, hUdef⟩ : ∃ U : Submodule K V, U = Submodule.span K ({e, f, x, x'} : Set V) :=
    ⟨_, rfl⟩
  rw [← hUdef]
  have hUe : e ∈ U := by rw [hUdef]; exact Submodule.subset_span (by simp)
  have hUf : f ∈ U := by rw [hUdef]; exact Submodule.subset_span (by simp)
  have hUx : x ∈ U := by rw [hUdef]; exact Submodule.subset_span (by simp)
  have hUx' : x' ∈ U := by rw [hUdef]; exact Submodule.subset_span (by simp)
  have hUc : ∀ u ∈ U, u = F u f • e + F u e • f + F u x' • x + F u x • x' := by
    rw [hUdef]; exact frame_coord halt hef hxx' hxe hxf hx'e hx'f
  have hfe : F f e = 1 := by rw [form_comm halt]; exact hef
  have hfinU : Module.finrank K U = 4 := by
    rw [hUdef]; exact frame_finrank halt hef hxx' hxe hxf hx'e hx'f
  have hUspan : ∀ u ∈ U, ∃ a b c d : K, u = a • e + b • f + c • x + d • x' :=
    fun u hu => ⟨F u f, F u e, F u x', F u x, hUc u hu⟩
  have hsub1 : Submodule.span K ({e, x, x'} : Set V) ≤ U := by
    rw [hUdef]; exact Submodule.span_mono (Set.insert_subset_insert (Set.subset_insert _ _))
  have hsub2 : Submodule.span K ({f, x, x'} : Set V) ≤ U := by
    rw [hUdef]; exact Submodule.span_mono (Set.subset_insert _ _)
  have hωA : ∀ g ∈ A, g f - f ∈ U := fun g hg => hsub1 (hAω g hg)
  have hωA' : ∀ g ∈ A', g e - e ∈ U := fun g hg => hsub2 (hA'ω g hg)
  have hgU : ∀ g ∈ A, ∀ u ∈ U, g u ∈ U := by
    intro g hg
    have hgP : g ∈ pointRadSubgroup F e := hA hg
    have hge : g e ∈ U := by rw [(mem_pointRad_iff.mp hgP).2.1]; exact hUe
    have hgf : g f ∈ U := by
      have h := Submodule.add_mem U hUf (hωA g hg)
      simpa using h
    have hgx : g x ∈ U := by
      rw [pointRad_apply_perp halt hef hgP x hxe]
      exact Submodule.add_mem U hUx (Submodule.smul_mem U _ hUe)
    have hgx' : g x' ∈ U := by
      rw [pointRad_apply_perp halt hef hgP x' hx'e]
      exact Submodule.add_mem U hUx' (Submodule.smul_mem U _ hUe)
    exact stab_of_span hge hgf hgx hgx' hUspan
  have hgU' : ∀ g ∈ A', ∀ u ∈ U, g u ∈ U := by
    intro g hg
    have hgP : g ∈ pointRadSubgroup F f := hA' hg
    have hgf : g f ∈ U := by rw [(mem_pointRad_iff.mp hgP).2.1]; exact hUf
    have hge : g e ∈ U := by
      have h := Submodule.add_mem U hUe (hωA' g hg)
      simpa using h
    have hgx : g x ∈ U := by
      rw [pointRad_apply_perp halt hfe hgP x hxf]
      exact Submodule.add_mem U hUx (Submodule.smul_mem U _ hUf)
    have hgx' : g x' ∈ U := by
      rw [pointRad_apply_perp halt hfe hgP x' hx'f]
      exact Submodule.add_mem U hUx' (Submodule.smul_mem U _ hUf)
    exact stab_of_span hge hgf hgx hgx' hUspan
  have hg2 : ∀ g ∈ A, ∀ v, g (g v) = v := fun g hg v => by
    rw [← LinearEquiv.mul_apply, pointRad_mul_self halt hef (hA hg)]
    rfl
  have hg2' : ∀ g ∈ A', ∀ v, g (g v) = v := fun g hg v => by
    rw [← LinearEquiv.mul_apply, pointRad_mul_self halt hfe (hA' hg)]
    rfl
  have hfixA : ∀ g ∈ A, ∀ w : V, (∀ u ∈ U, F w u = 0) → g w = w := fun g hg w hw =>
    fix_of_pointRad halt hef (hA hg) (hωA g hg) hUe w hw
  have hfixA' : ∀ g ∈ A', ∀ w : V, (∀ u ∈ U, F w u = 0) → g w = w := fun g hg w hw =>
    fix_of_pointRad halt hfe (hA' hg) (hωA' g hg) hUf w hw
  have hfixSub : A ⊔ A' ≤ perpFixSub F U :=
    sup_le (fun g hg => fun w hw => hfixA g hg w hw) (fun g hg => fun w hw => hfixA' g hg w hw)
  have hAU_le : restrictSub U A ≤ restrictSub U (A ⊔ A') := restrictSub_mono le_sup_left
  have hA'U_le : restrictSub U A' ≤ restrictSub U (A ⊔ A') := restrictSub_mono le_sup_right
  have hAUsub : (restrictSub U A : Set (U ≃ₗ[K] U)) ⊆
      pointRad (F.compl₁₂ U.subtype U.subtype) ⟨e, hUe⟩ := by
    intro r hr
    obtain ⟨g, hg, hrg⟩ := hr
    exact restrict_mem_pointRad hUe (hA hg) hrg
  have hA'Usub : (restrictSub U A' : Set (U ≃ₗ[K] U)) ⊆
      pointRad (F.compl₁₂ U.subtype U.subtype) ⟨f, hUf⟩ := by
    intro r hr
    obtain ⟨g, hg, hrg⟩ := hr
    exact restrict_mem_pointRad hUf (hA' hg) hrg
  have hEAU := elation_restrict_A halt hef hUe hUf hUx hUx' hUc A hA hAfull hgU hg2
  have hEA'U := elation_restrict_A' halt hfe hUe hUf hUx hUx' hUc A' hA' hA'full hgU' hg2'
  have hP' := hP K U (F.compl₁₂ U.subtype U.subtype) hq (frame_nondeg halt hUe hUf hUx hUx' hUc)
    (frame_alt halt U) hfinU ⟨e, hUe⟩ ⟨f, hUf⟩ hef (restrictSub U A) (restrictSub U A')
    hAUsub hA'Usub hEAU hEA'U
  rcases hP' with hsup | ⟨Qf, hQpol, hQe, hQf, hQA, hQA'⟩
  · left
    intro c
    let τ : U ≃ₗ[K] U := LinearEquiv.ofInvolutive
      (transvMap (F.compl₁₂ U.subtype U.subtype) ⟨e, hUe⟩ c) (transvMap_invol (frame_alt halt U) c)
    have hτmem : τ ∈ sympSubgroup (F.compl₁₂ U.subtype U.subtype) := fun a b =>
      transvMap_isom (frame_alt halt U) (p := ⟨e, hUe⟩) c a b
    have hτ : ∀ u : U, ((τ u : U) : V) = (u : V) + (c * F (u : V) e) • e := fun u =>
      congrArg Subtype.val (transvMap_apply (F.compl₁₂ U.subtype U.subtype) ⟨e, hUe⟩ c u)
    have hτJ : τ ∈ restrictSub U (A ⊔ A') := by
      rw [← hsup] at hτmem
      exact (sup_le hAU_le hA'U_le) hτmem
    obtain ⟨g, hgJ, hgτ⟩ := hτJ
    refine ⟨g, hgJ, fun v => ?_⟩
    obtain ⟨p, hp⟩ : ∃ p : V, p = framePr F e f x x' v := ⟨_, rfl⟩
    have hpU : p ∈ U := by
      rw [hp]
      unfold framePr
      exact Submodule.add_mem U (Submodule.add_mem U (Submodule.add_mem U
        (Submodule.smul_mem U _ hUe) (Submodule.smul_mem U _ hUf)) (Submodule.smul_mem U _ hUx))
        (Submodule.smul_mem U _ hUx')
    have hpF := framePr_form halt hef hxx' hxe hxf hx'e hx'f v
    rw [← hp] at hpF
    obtain ⟨hpe, hpf, hpx, hpx'⟩ := hpF
    have hw : ∀ u ∈ U, F (v - p) u = 0 := by
      apply frame_perp_span hUc
      · rw [map_sub, LinearMap.sub_apply, hpe, sub_self]
      · rw [map_sub, LinearMap.sub_apply, hpf, sub_self]
      · rw [map_sub, LinearMap.sub_apply, hpx, sub_self]
      · rw [map_sub, LinearMap.sub_apply, hpx', sub_self]
    have hgp : g p = p + (c * F p e) • e := by
      have h := hgτ ⟨p, hpU⟩
      rw [hτ ⟨p, hpU⟩] at h
      exact h.symm
    have hgw : g (v - p) = v - p := hfixSub hgJ (v - p) hw
    have hv : g v = g p + g (v - p) := by
      rw [← map_add]
      congr 1
      abel
    rw [hv, hgp, hgw, hpe]
    abel
  · right
    have hpolV : ∀ a b : U, Qf.polarBilin a b = F (a : V) (b : V) := fun a b =>
      congrArg (fun k : LinearMap.BilinForm K U => k a b) hQpol
    refine ⟨qExt Qf, fun c u hu => qExt_smul Qf hu,
      fun u u' hu hu' => qExt_add Qf hpolV hu hu', ?_, ?_, ?_, ?_⟩
    · rw [qExt_mem Qf hUe]
      exact hQe
    · rw [qExt_mem Qf hUf]
      exact hQf
    · intro g hg
      have hgfU : g f ∈ U := by
        have h := Submodule.add_mem U hUf (hωA g hg)
        simpa using h
      obtain ⟨r, hr⟩ := exists_restrict (hgU g hg) (hg2 g hg)
      have hrA : r ∈ restrictSub U A := ⟨g, hg, hr⟩
      have h1 : Qf (r ⟨f, hUf⟩) = Qf ⟨f, hUf⟩ := hQA hrA ⟨f, hUf⟩
      have h2 : (⟨g f, hgfU⟩ : U) = r ⟨f, hUf⟩ := Subtype.ext (hr ⟨f, hUf⟩).symm
      rw [qExt_mem Qf hgfU, qExt_mem Qf hUf, h2, h1]
    · intro g hg
      have hgeU : g e ∈ U := by
        have h := Submodule.add_mem U hUe (hωA' g hg)
        simpa using h
      obtain ⟨r, hr⟩ := exists_restrict (hgU' g hg) (hg2' g hg)
      have hrA' : r ∈ restrictSub U A' := ⟨g, hg, hr⟩
      have h1 : Qf (r ⟨e, hUe⟩) = Qf ⟨e, hUe⟩ := hQA' hrA' ⟨e, hUe⟩
      have h2 : (⟨g e, hgeU⟩ : U) = r ⟨e, hUe⟩ := Subtype.ext (hr ⟨e, hUe⟩).symm
      rw [qExt_mem Qf hgeU, qExt_mem Qf hUe, h2, h1]

end CFSG.RankThree.GF2n.Stroth80.Classify
