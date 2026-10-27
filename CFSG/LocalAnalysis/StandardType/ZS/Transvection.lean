module

public import CFSG.LocalAnalysis.StandardType.ZS.Basic
public import CFSG.LocalAnalysis.StandardType.GGQTwoReflLin
import CFSG.LocalAnalysis.StandardType.GGWitSlpmConjAux
import CFSG.LocalAnalysis.StandardType.McLaughlinOdd
import CFSG.LocalAnalysis.StandardType.GGWitSlpm

public section

namespace CFSG.StandardType.ZS

open CFSG.StandardType.QTwoLin (IsTransvectionLin)

variable {p : ℕ} {U : Type} [AddCommGroup U] [Module (ZMod p) U]

@[expose] def transvectionClosure (A : Subgroup (U ≃ₗ[ZMod p] U)) :
    Subgroup (U ≃ₗ[ZMod p] U) :=
  Subgroup.closure {t | t ∈ A ∧ IsTransvectionLin t}

private theorem conj_transvec_mem {A : Subgroup (U ≃ₗ[ZMod p] U)} {a t : U ≃ₗ[ZMod p] U}
    (ha : a ∈ A) (htA : t ∈ A) (htT : IsTransvectionLin t) :
    a * t * a⁻¹ ∈ A ∧ IsTransvectionLin (a * t * a⁻¹) := by
  obtain ⟨u, ψ, hu, hψ, hψu, ht⟩ := htT
  refine ⟨A.mul_mem (A.mul_mem ha htA) (A.inv_mem ha),
    ⟨a u, ψ.comp (a.symm : U →ₗ[ZMod p] U), ?_, ?_, ?_, ?_⟩⟩
  · intro h0
    exact hu (a.injective (by simpa using h0))
  · intro h0
    apply hψ
    ext y
    have := congrArg (fun f : Module.Dual (ZMod p) U => f (a y)) h0
    simpa using this
  · simpa using hψu
  · intro v
    change a (t (a.symm v)) = v + (ψ.comp (a.symm : U →ₗ[ZMod p] U)) v • a u
    rw [ht (a.symm v), map_add, map_smul, LinearEquiv.apply_symm_apply, LinearMap.comp_apply]
    rfl

theorem transvectionClosure_le (A : Subgroup (U ≃ₗ[ZMod p] U)) : transvectionClosure A ≤ A := by
  rw [transvectionClosure, Subgroup.closure_le]
  rintro t ⟨htA, _⟩
  exact htA

theorem conj_mem_transvectionClosure {A : Subgroup (U ≃ₗ[ZMod p] U)} {a h : U ≃ₗ[ZMod p] U}
    (ha : a ∈ A) (hh : h ∈ transvectionClosure A) : a * h * a⁻¹ ∈ transvectionClosure A := by
  rw [transvectionClosure] at hh ⊢
  have hle : Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ A ∧ IsTransvectionLin t} ≤
      Subgroup.comap (MulAut.conj a)
        (Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ A ∧ IsTransvectionLin t}) := by
    rw [Subgroup.closure_le]
    rintro t ⟨htA, htT⟩
    exact Subgroup.subset_closure (conj_transvec_mem ha htA htT)
  have := hle hh
  simpa [MulAut.conj_apply] using this


private theorem sp_expand_scalar {R : Type*} [CommRing R] (a b c d e f g : R)
    (hd : d = -g) (hf : f = 0) :
    a + c * d + e * (b + c * f) = a + e * b - c * g := by
  rw [hd, hf]; ring

private theorem sp_key_scalar {R : Type*} [CommRing R] {a x y : R} (h : a + x - y = a) :
    x = y := by
  linear_combination h

private theorem sp_cancel_scalar {R : Type*} [CommRing R] (x y z : R)
    (h : x * y = (-y) * z) : x * y = (-z) * y := by
  rw [h]; ring

private theorem sp_final_scalar {R : Type*} [CommRing R] {y z : R} (h : y - z = -y) :
    2 * y = z := by
  linear_combination h

private theorem sp_rel_scalar {R : Type*} [Field R] {x0 x1 c0 c1 φy : R} (h2 : (2 : R) ≠ 0)
    (h0 : 2 * x0 = φy * c0) (h1 : 2 * x1 = φy * c1) : c1 * x0 = c0 * x1 := by
  have hh : 2 * (c1 * x0) = 2 * (c0 * x1) := by
    linear_combination c1 * h0 - c0 * h1
  exact mul_left_cancel₀ h2 hh

private theorem sp_two_inv_mul {R : Type*} [Field R] (x : R) (h2 : (2 : R) ≠ 0) :
    2⁻¹ * x * 2 = x := by
  rw [mul_assoc, mul_comm x 2, ← mul_assoc, inv_mul_cancel₀ h2, one_mul]

private theorem sp_inv_smul {R M : Type*} [Field R] [AddCommGroup M] [Module R M] (c : R)
    (hc : c ≠ 0) (m : M) : c⁻¹ • (c • m) = m := by
  rw [smul_smul, inv_mul_cancel₀ hc, one_smul]

private theorem map_isTransvecInvariant {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {V : Submodule (ZMod p) U}
    (hV : ∀ h ∈ transvectionClosure A, ∀ w ∈ V, h w ∈ V)
    {a : U ≃ₗ[ZMod p] U} (ha : a ∈ A) :
    ∀ h ∈ transvectionClosure A, ∀ x ∈ V.map (a : U →ₗ[ZMod p] U),
      h x ∈ V.map (a : U →ₗ[ZMod p] U) := by
  intro h hh x hx
  rw [Submodule.mem_map] at hx ⊢
  obtain ⟨w, hw, rfl⟩ := hx
  refine ⟨(a⁻¹ * h * a) w, hV _ (conj_mem_transvectionClosure (A.inv_mem ha) hh) w hw, ?_⟩
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply]
  exact LinearEquiv.apply_symm_apply a _

private theorem finrank_le_one_of_inf_map_eq_bot [Fact p.Prime] [Module.Finite (ZMod p) U]
    {r : U ≃ₗ[ZMod p] U} (hr : IsRefl p r)
    {V : Submodule (ZMod p) U} (hbot : V ⊓ V.map (r : U →ₗ[ZMod p] U) = ⊥) :
    Module.finrank (ZMod p) V ≤ 1 := by
  let g : V →ₗ[ZMod p] U := ((r : U →ₗ[ZMod p] U) - LinearMap.id).comp V.subtype
  have hginj : Function.Injective g := by
    intro x y hxy
    have h0 : (((r : U →ₗ[ZMod p] U) - LinearMap.id : U →ₗ[ZMod p] U)) ((x - y : V) : U) = 0 := by
      have : g (x - y) = 0 := by rw [map_sub, hxy, sub_self]
      simpa [g] using this
    have h1 : (r : U →ₗ[ZMod p] U) ((x - y : V) : U) = ((x - y : V) : U) := by
      rw [LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at h0
      exact h0
    have hmemV : (((x - y : V) : U)) ∈ V := (x - y : V).2
    have hmemMap : (((x - y : V) : U)) ∈ V.map (r : U →ₗ[ZMod p] U) := by
      rw [Submodule.mem_map]
      exact ⟨((x - y : V) : U), hmemV, h1⟩
    have hmem : (((x - y : V) : U)) ∈ (⊥ : Submodule (ZMod p) U) := by
      rw [← hbot]
      exact Submodule.mem_inf.mpr ⟨hmemV, hmemMap⟩
    have hz : (x - y : V) = 0 := Subtype.ext ((Submodule.mem_bot (ZMod p)).mp hmem)
    exact sub_eq_zero.mp hz
  have hfin : Module.finrank (ZMod p) (LinearMap.range g) = Module.finrank (ZMod p) V :=
    LinearMap.finrank_range_of_inj hginj
  have hle : LinearMap.range g ≤ LinearMap.range ((r : U →ₗ[ZMod p] U) - LinearMap.id) := by
    rintro _ ⟨v, rfl⟩
    exact LinearMap.mem_range_self _ (v : U)
  calc Module.finrank (ZMod p) V = Module.finrank (ZMod p) (LinearMap.range g) := hfin.symm
    _ ≤ Module.finrank (ZMod p) (LinearMap.range ((r : U →ₗ[ZMod p] U) - LinearMap.id)) :=
        Submodule.finrank_mono hle
    _ = 1 := hr.2

private def transvecFix (T : Subgroup (U ≃ₗ[ZMod p] U)) : Submodule (ZMod p) U :=
  ⨅ h : T, LinearMap.ker (((h : U ≃ₗ[ZMod p] U) : U →ₗ[ZMod p] U) - LinearMap.id)

private theorem mem_transvecFix {T : Subgroup (U ≃ₗ[ZMod p] U)} {v : U} :
    v ∈ transvecFix T ↔ ∀ h : T, (h : U ≃ₗ[ZMod p] U) v = v := by
  rw [transvecFix, Submodule.mem_iInf]
  constructor
  · intro h hh
    have := h hh
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero] at this
    exact this
  · intro h hh
    rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]
    exact h hh

private theorem transvecFix_isInvariant {A : Subgroup (U ≃ₗ[ZMod p] U)}
    {a : U ≃ₗ[ZMod p] U} (ha : a ∈ A) :
    ∀ v ∈ transvecFix (transvectionClosure A), a v ∈ transvecFix (transvectionClosure A) := by
  intro v hv
  rw [mem_transvecFix] at hv ⊢
  intro h
  have hconj : (a⁻¹ * (h : U ≃ₗ[ZMod p] U) * a) ∈ transvectionClosure A :=
    conj_mem_transvectionClosure (A.inv_mem ha) h.2
  have hv' := hv ⟨a⁻¹ * (h : U ≃ₗ[ZMod p] U) * a, hconj⟩
  rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply] at hv'
  calc (h : U ≃ₗ[ZMod p] U) (a v) = a (a⁻¹ ((h : U ≃ₗ[ZMod p] U) (a v))) :=
        (LinearEquiv.apply_symm_apply a _).symm
    _ = a v := by rw [hv']

private theorem mem_transvecFix_of_fixes {A : Subgroup (U ≃ₗ[ZMod p] U)} {w : U}
    (hw : ∀ t ∈ A, IsTransvectionLin t → t w = w) :
    w ∈ transvecFix (transvectionClosure A) := by
  rw [mem_transvecFix]
  intro h
  have hh : (h : U ≃ₗ[ZMod p] U) ∈ transvectionClosure A := h.2
  change (h : U ≃ₗ[ZMod p] U) ∈
    Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ A ∧ IsTransvectionLin t} at hh
  let H : Subgroup (U ≃ₗ[ZMod p] U) :=
    { carrier := {g | g w = w}
      one_mem' := by change (1 : U ≃ₗ[ZMod p] U) w = w; rfl
      mul_mem' := by
        intro g k hg hk
        change (g * k) w = w
        rw [LinearEquiv.mul_apply, hk, hg]
      inv_mem' := by
        intro g hg
        show g⁻¹ w = w
        calc g⁻¹ w = g⁻¹ (g w) := by rw [hg]
          _ = w := LinearEquiv.symm_apply_apply g w }
  have hle : Subgroup.closure {t : U ≃ₗ[ZMod p] U | t ∈ A ∧ IsTransvectionLin t} ≤ H := by
    rw [Subgroup.closure_le]
    rintro t ⟨htA, htT⟩
    exact hw t htA htT
  exact hle hh

private theorem transvec_fixes_of_span [Fact p.Prime]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {W₀ : Submodule (ZMod p) U} {w : U}
    (hW₀ : ∀ h ∈ transvectionClosure A, ∀ z ∈ W₀, h z ∈ W₀)
    (hspan : W₀ = Submodule.span (ZMod p) {w}) (hwW₀ : w ∈ W₀)
    {t : U ≃ₗ[ZMod p] U} (htA : t ∈ A) (htT : IsTransvectionLin t) : t w = w := by
  have htc : t ∈ transvectionClosure A := Subgroup.subset_closure ⟨htA, htT⟩
  obtain ⟨u, ψ, hu, hψ, hψu, htψ⟩ := htT
  have htw : t w ∈ W₀ := hW₀ t htc w hwW₀
  by_contra hne
  have hψw : ψ w ≠ 0 := fun h0 => hne (by rw [htψ w, h0, zero_smul, add_zero])
  have htw' : t w ∈ Submodule.span (ZMod p) {w} := by rw [← hspan]; exact htw
  have hsub : t w - w = ψ w • u := by rw [htψ w]; abel
  have hsubspan : t w - w ∈ Submodule.span (ZMod p) {w} :=
    Submodule.sub_mem _ htw' (Submodule.subset_span (Set.mem_singleton w))
  have hu_mem : u ∈ Submodule.span (ZMod p) {w} := by
    have heq : u = (ψ w)⁻¹ • (t w - w) := by rw [hsub, sp_inv_smul (ψ w) hψw u]
    rw [heq]
    exact Submodule.smul_mem _ _ hsubspan
  rw [Submodule.mem_span_singleton] at hu_mem
  obtain ⟨d, hd⟩ := hu_mem
  have hψud : ψ u = d * ψ w := by rw [← hd, map_smul]; rfl
  rw [hψu] at hψud
  have hd0 : d = 0 := (mul_eq_zero.mp hψud.symm).resolve_right hψw
  exact hu (by rw [← hd, hd0, zero_smul])

private theorem false_of_fixes_at [Fact p.Prime] [Module.Finite (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ a ∈ A, ∀ z ∈ W, a z ∈ W) → W = ⊥ ∨ W = ⊤)
    (ht : ∃ t ∈ A, IsTransvectionLin t) {w : U} (hw0 : w ≠ 0)
    (hfix : ∀ t ∈ A, IsTransvectionLin t → t w = w) : False := by
  have hwFix : w ∈ transvecFix (transvectionClosure A) := mem_transvecFix_of_fixes hfix
  have hFix : transvecFix (transvectionClosure A) = ⊤ := by
    rcases hirr _ (fun a ha x hx => transvecFix_isInvariant ha x hx) with h | h
    · exfalso
      have : w ∈ (⊥ : Submodule (ZMod p) U) := by rw [← h]; exact hwFix
      exact hw0 ((Submodule.mem_bot (ZMod p)).mp this)
    · exact h
  obtain ⟨t0, ht0A, ht0T⟩ := ht
  have ht0c : t0 ∈ transvectionClosure A := Subgroup.subset_closure ⟨ht0A, ht0T⟩
  obtain ⟨u0, ψ0, hu0, hψ0, hψ0u0, ht0⟩ := ht0T
  have hall : ∀ (v : U) (h : transvectionClosure A), (h : U ≃ₗ[ZMod p] U) v = v :=
    fun v h => mem_transvecFix.mp (by rw [hFix]; exact Submodule.mem_top) h
  obtain ⟨v, hv⟩ : ∃ v : U, ψ0 v ≠ 0 := by
    by_contra h
    push Not at h
    exact hψ0 (LinearMap.ext fun x => by simpa using h x)
  have hvt : t0 v = v := hall v ⟨t0, ht0c⟩
  rw [ht0 v] at hvt
  have hzero : ψ0 v • u0 = 0 := by
    exact add_left_cancel (show v + ψ0 v • u0 = v + 0 by simpa using hvt)
  rcases smul_eq_zero.mp hzero with h | h
  · exact hv h
  · exact hu0 h

private theorem false_of_inf_map_eq_bot [Fact p.Prime] [Module.Finite (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ a ∈ A, ∀ z ∈ W, a z ∈ W) → W = ⊥ ∨ W = ⊤)
    (ht : ∃ t ∈ A, IsTransvectionLin t) {W₀ : Submodule (ZMod p) U}
    (hW₀ : ∀ h ∈ transvectionClosure A, ∀ z ∈ W₀, h z ∈ W₀) (hW₀ne : W₀ ≠ ⊥)
    {r : U ≃ₗ[ZMod p] U} (hrRefl : IsRefl p r)
    (hbot : W₀ ⊓ W₀.map (r : U →ₗ[ZMod p] U) = ⊥) : False := by
  have hle1 : Module.finrank (ZMod p) W₀ ≤ 1 := finrank_le_one_of_inf_map_eq_bot hrRefl hbot
  have hone : 1 ≤ Module.finrank (ZMod p) W₀ := Submodule.one_le_finrank_iff.mpr hW₀ne
  have hfin1 : Module.finrank (ZMod p) W₀ = 1 := le_antisymm hle1 hone
  obtain ⟨w, hwW₀, hw0⟩ := (Submodule.ne_bot_iff W₀).mp hW₀ne
  have hspan : W₀ = Submodule.span (ZMod p) {w} :=
    (Submodule.eq_of_le_of_finrank_eq ((Submodule.span_singleton_le_iff_mem w W₀).mpr hwW₀)
      (by rw [finrank_span_singleton hw0, hfin1])).symm
  exact false_of_fixes_at hirr ht hw0 fun t htA htT =>
    transvec_fixes_of_span hW₀ hspan hwW₀ htA htT

private theorem map_eq_self_of_reflection [Fact p.Prime] [Module.Finite (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} {W₀ : Submodule (ZMod p) U}
    (hW₀ : ∀ h ∈ transvectionClosure A, ∀ z ∈ W₀, h z ∈ W₀)
    {r : U ≃ₗ[ZMod p] U} (hrA : r ∈ A)
    (hmin : ∀ V : Submodule (ZMod p) U,
      (∀ h ∈ transvectionClosure A, ∀ z ∈ V, h z ∈ V) → V ≠ ⊥ →
        Module.finrank (ZMod p) W₀ ≤ Module.finrank (ZMod p) V)
    (hne : W₀ ⊓ W₀.map (r : U →ₗ[ZMod p] U) ≠ ⊥) :
    W₀.map (r : U →ₗ[ZMod p] U) = W₀ := by
  have hmapInv : ∀ h ∈ transvectionClosure A,
      ∀ x ∈ W₀ ⊓ W₀.map (r : U →ₗ[ZMod p] U),
        h x ∈ W₀ ⊓ W₀.map (r : U →ₗ[ZMod p] U) := by
    intro h hh x hx
    rw [Submodule.mem_inf] at hx ⊢
    exact ⟨hW₀ h hh x hx.1, map_isTransvecInvariant hW₀ hrA h hh x hx.2⟩
  have hfin_ge := hmin _ hmapInv hne
  have hle : W₀ ⊓ W₀.map (r : U →ₗ[ZMod p] U) ≤ W₀ := inf_le_left
  have hfin_eq : Module.finrank (ZMod p) ↥(W₀ ⊓ W₀.map (r : U →ₗ[ZMod p] U)) =
      Module.finrank (ZMod p) W₀ :=
    le_antisymm (Submodule.finrank_mono hle) hfin_ge
  have heq : W₀ ⊓ W₀.map (r : U →ₗ[ZMod p] U) = W₀ :=
    Submodule.eq_of_le_of_finrank_eq hle hfin_eq
  have hle' : W₀ ≤ W₀.map (r : U →ₗ[ZMod p] U) := by
    have := inf_le_right (a := W₀) (b := W₀.map (r : U →ₗ[ZMod p] U))
    rwa [heq] at this
  exact (Submodule.eq_of_le_of_finrank_eq hle'
    (LinearEquiv.finrank_map_eq r W₀).symm).symm

private theorem map_into_of_reflections [Fact p.Prime] [Module.Finite (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p A) {W₀ : Submodule (ZMod p) U}
    (hmap_refl : ∀ r ∈ A, IsRefl p r → W₀.map (r : U →ₗ[ZMod p] U) = W₀) :
    ∀ a ∈ A, ∀ w ∈ W₀, a w ∈ W₀ := by
  let H : Subgroup (U ≃ₗ[ZMod p] U) :=
    { carrier := {g | ∀ w ∈ W₀, g w ∈ W₀}
      one_mem' := by intro w hw; simpa using hw
      mul_mem' := by intro g k hg hk w hw; exact hg (k w) (hk w hw)
      inv_mem' := by
        intro g hg
        have hle : W₀.map (g : U →ₗ[ZMod p] U) ≤ W₀ := by
          rw [Submodule.map_le_iff_le_comap]
          intro w hw
          exact hg w hw
        have hfin : Module.finrank (ZMod p) (W₀.map (g : U →ₗ[ZMod p] U)) =
            Module.finrank (ZMod p) W₀ := LinearEquiv.finrank_map_eq g W₀
        have heq : W₀.map (g : U →ₗ[ZMod p] U) = W₀ :=
          Submodule.eq_of_le_of_finrank_eq hle hfin
        intro w hw
        have hmem : w ∈ W₀.map (g : U →ₗ[ZMod p] U) := by rw [heq]; exact hw
        rw [Submodule.mem_map] at hmem
        obtain ⟨w', hw', hw'eq⟩ := hmem
        have : g⁻¹ w = w' := by
          rw [← hw'eq]
          exact LinearEquiv.symm_apply_apply g w'
        rw [this]
        exact hw' }
  have hAH : A ≤ H := by
    rw [hgen, Subgroup.closure_le]
    rintro r ⟨hrA, hrRefl⟩
    intro w hw
    rw [← hmap_refl r hrA hrRefl]
    exact Submodule.mem_map_of_mem (f := (r : U →ₗ[ZMod p] U)) hw
  exact fun a ha w hw => hAH ha w hw

private theorem eq_top_of_minimal [Fact p.Prime] [Module.Finite (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p A)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤)
    (ht : ∃ t ∈ A, IsTransvectionLin t) {W₀ : Submodule (ZMod p) U}
    (hW₀ : ∀ h ∈ transvectionClosure A, ∀ w ∈ W₀, h w ∈ W₀) (hW₀ne : W₀ ≠ ⊥)
    (hmin : ∀ V : Submodule (ZMod p) U,
      (∀ h ∈ transvectionClosure A, ∀ w ∈ V, h w ∈ V) → V ≠ ⊥ →
        Module.finrank (ZMod p) W₀ ≤ Module.finrank (ZMod p) V) :
    W₀ = ⊤ := by
  have hmap_refl : ∀ r ∈ A, IsRefl p r → W₀.map (r : U →ₗ[ZMod p] U) = W₀ := by
    intro r hrA hrRefl
    by_cases hbot : W₀ ⊓ W₀.map (r : U →ₗ[ZMod p] U) = ⊥
    · exact (false_of_inf_map_eq_bot hirr ht hW₀ hW₀ne hrRefl hbot).elim
    · exact map_eq_self_of_reflection hW₀ hrA hmin hbot
  have hmap_A := map_into_of_reflections hgen hmap_refl
  rcases hirr W₀ hmap_A with h | h
  · exact absurd h hW₀ne
  · exact h

theorem transvectionClosure_irreducible [Fact p.Prime] [Module.Finite (ZMod p) U]
    {A : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p A)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤)
    (ht : ∃ t ∈ A, IsTransvectionLin t) (W : Submodule (ZMod p) U)
    (hW : ∀ h ∈ transvectionClosure A, ∀ w ∈ W, h w ∈ W) : W = ⊥ ∨ W = ⊤ := by
  classical
  by_cases hWbot : W = ⊥
  · exact Or.inl hWbot
  right
  obtain ⟨t, htA, htT⟩ := ht
  have htwit : t ∈ A ∧ IsTransvectionLin t := ⟨htA, htT⟩
  obtain ⟨u, ψ, hu, hψ, hψu, _⟩ := htT
  have hnt : Nontrivial U := ⟨⟨u, 0, hu⟩⟩
  have hne_top : (⊤ : Submodule (ZMod p) U) ≠ ⊥ := by
    intro h
    have : u ∈ (⊥ : Submodule (ZMod p) U) := by rw [← h]; exact Submodule.mem_top
    exact hu ((Submodule.mem_bot (ZMod p)).mp this)
  have hS : ∃ n : ℕ, ∃ V : Submodule (ZMod p) U,
      (∀ h ∈ transvectionClosure A, ∀ w ∈ V, h w ∈ V) ∧ V ≠ ⊥ ∧
        Module.finrank (ZMod p) V = n :=
    ⟨_, ⊤, fun _ _ _ _ => Submodule.mem_top, hne_top, rfl⟩
  obtain ⟨W₀, hW₀, hW₀ne, hW₀fin⟩ := Nat.find_spec hS
  have hmin : ∀ V : Submodule (ZMod p) U,
      (∀ h ∈ transvectionClosure A, ∀ w ∈ V, h w ∈ V) → V ≠ ⊥ →
        Module.finrank (ZMod p) W₀ ≤ Module.finrank (ZMod p) V := by
    intro V hV hVne
    rw [hW₀fin]
    exact Nat.find_min' hS ⟨V, hV, hVne, rfl⟩
  have htop : W₀ = ⊤ := eq_top_of_minimal hgen hirr ⟨t, htwit⟩ hW₀ hW₀ne hmin
  have hfinW : Module.finrank (ZMod p) W = Module.finrank (ZMod p) U := by
    have h1 := hmin W hW hWbot
    rw [htop, finrank_top] at h1
    exact le_antisymm (Submodule.finrank_le W) h1
  exact Submodule.eq_of_le_of_finrank_eq le_top (by rw [finrank_top]; exact hfinW)
private theorem sp_conj_pairing_key [Fact p.Prime] [Module.Finite (ZMod p) U]
    {B : LinearMap.BilinForm (ZMod p) U} (hB : B.IsAlt)
    {a : U} {φ : Module.Dual (ZMod p) U} (hφ : φ a = 2) {u : U} (hu : φ u = 0)
    (hnorm : ∀ g : U ≃ₗ[ZMod p] U, (∀ x y, B (g x) (g y) = B x y) →
      ∀ x y, B ((Module.reflection hφ * g * (Module.reflection hφ)⁻¹) x)
        ((Module.reflection hφ * g * (Module.reflection hφ)⁻¹) y) = B x y) :
    ∀ v w, ((B.flip u).comp (Module.reflection hφ : U →ₗ[ZMod p] U)) w * B v u =
      ((B.flip u).comp (Module.reflection hφ : U →ₗ[ZMod p] U)) v * B w u := by
  let ψ : Module.Dual (ZMod p) U := (B.flip u).comp (Module.reflection hφ : U →ₗ[ZMod p] U)
  let T : LinearMap.GeneralLinearGroup (ZMod p) U :=
    CFSG.ClassicalGroups.Alternating.symplecticTransvection B hB u 1
  let t : U ≃ₗ[ZMod p] U := T.toLinearEquiv
  have ht_apply : ∀ x, t x = x + B x u • u := by
    intro x
    change (T : U →ₗ[ZMod p] U) x = x + B x u • u
    rw [CFSG.ClassicalGroups.Alternating.symplecticTransvection_apply, one_mul]
  have ht_iso : ∀ x y, B (t x) (t y) = B x y := by
    intro x y
    change B ((T : U →ₗ[ZMod p] U) x) ((T : U →ₗ[ZMod p] U) y) = B x y
    exact CFSG.LocalAnalysis.ComponentInitial.mem_bilinIsometryGroup.mp
      (CFSG.ClassicalGroups.Alternating.symplecticTransvection_mem_bilinIsometryGroup hB u 1) x y
  have hru : Module.reflection hφ u = u := by
    rw [Module.reflection_apply, hu, zero_smul, sub_zero]
  have hact : ∀ v, (Module.reflection hφ * t * (Module.reflection hφ)⁻¹) v = v + ψ v • u := by
    intro v
    calc (Module.reflection hφ * t * (Module.reflection hφ)⁻¹) v
        = Module.reflection hφ (t (Module.reflection hφ v)) := by
          rw [LinearEquiv.mul_apply, LinearEquiv.mul_apply, Module.reflection_inv]
      _ = Module.reflection hφ (Module.reflection hφ v + B (Module.reflection hφ v) u • u) := by
          rw [ht_apply]
      _ = v + B (Module.reflection hφ v) u • u := by
          rw [map_add, map_smul, Module.involutive_reflection hφ v, hru]
      _ = v + ψ v • u := rfl
  have hexp : ∀ v w, B (v + ψ v • u) (w + ψ w • u)
      = B v w + ψ w * B v u - ψ v * B w u := by
    intro v w
    have huuw : B u w = -(B w u) := by
      have h : -((B u) w) = (B w) u := hB.neg_eq u w
      exact neg_eq_iff_eq_neg.mp h
    have huu : B u u = 0 := hB.self_eq_zero u
    simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul]
    exact sp_expand_scalar (B v w) (B v u) (ψ v) (B u w) (ψ w) (B u u) (B w u) huuw huu
  have hkey : ∀ v w, ψ w * B v u = ψ v * B w u := by
    intro v w
    have h := hnorm t ht_iso v w
    rw [hact v, hact w, hexp v w] at h
    exact sp_key_scalar h
  exact hkey

private theorem two_mul_B_eq_of_refl_normalizes_sp [Fact p.Prime] [Module.Finite (ZMod p) U]
    {B : LinearMap.BilinForm (ZMod p) U} (hB : B.IsAlt)
    {a : U} {φ : Module.Dual (ZMod p) U} (hφ : φ a = 2)
    (hnorm : ∀ g : U ≃ₗ[ZMod p] U,
      (∀ x y, B (g x) (g y) = B x y) →
      ∀ x y, B ((Module.reflection hφ * g * (Module.reflection hφ)⁻¹) x)
        ((Module.reflection hφ * g * (Module.reflection hφ)⁻¹) y) = B x y)
    {u : U} (hu : φ u = 0) (hbau : B a u ≠ 0) (y : U) :
    2 * B y u = φ y * B a u := by
  let ψ : Module.Dual (ZMod p) U := (B.flip u).comp (Module.reflection hφ : U →ₗ[ZMod p] U)
  have hkey : ∀ v w, ψ w * B v u = ψ v * B w u := sp_conj_pairing_key hB hφ hu hnorm
  have hψa : ψ a = -(B a u) := by
    have hra : (Module.reflection hφ : U →ₗ[ZMod p] U) a = -a := Module.reflection_apply_self hφ
    change B.flip u ((Module.reflection hφ : U →ₗ[ZMod p] U) a) = -(B a u)
    rw [hra, map_neg]
    simp [LinearMap.BilinForm.flip_apply]
  have hψ_eq : ∀ w, ψ w = -(B w u) := by
    intro w
    have h := hkey a w
    rw [hψa] at h
    refine mul_right_cancel₀ hbau ?_
    exact sp_cancel_scalar (ψ w) (B a u) (B w u) h
  have hψform : ∀ w, ψ w = B w u - φ w * B a u := by
    intro w
    change B.flip u (Module.reflection hφ w) = B w u - φ w * B a u
    rw [Module.reflection_apply, map_sub, map_smul]
    simp only [LinearMap.BilinForm.flip_apply, smul_eq_mul]
    rfl
  have := hψ_eq y
  rw [hψform y] at this
  exact sp_final_scalar this

private theorem sp_refl_ker_w [Fact p.Prime] [Module.Finite (ZMod p) U]
    (hp : p ≠ 2) (h3 : 3 ≤ Module.finrank (ZMod p) U) {B : LinearMap.BilinForm (ZMod p) U}
    {a : U} {φ : Module.Dual (ZMod p) U} (hφ : φ a = 2) {u : U} (hu : φ u = 0)
    (hbau : B a u ≠ 0) :
    ∃ w ∈ LinearMap.ker φ, w ∉ Submodule.span (ZMod p) {u} ∧ B a w ≠ 0 := by
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero hp
  have hφne : φ ≠ 0 := fun h => h2 (by rw [h] at hφ; exact hφ.symm)
  have hkercard : Module.finrank (ZMod p) (LinearMap.ker φ) + 1 =
      Module.finrank (ZMod p) U :=
    Module.Dual.finrank_ker_add_one_of_ne_zero (f := φ) hφne
  have hker2 : 2 ≤ Module.finrank (ZMod p) (LinearMap.ker φ) := by omega
  have hune : u ≠ 0 := fun h0 => hbau (by rw [h0, map_zero])
  have hnotle : ¬ LinearMap.ker φ ≤ Submodule.span (ZMod p) {u} := by
    intro hle
    have h1 := Submodule.finrank_mono hle
    rw [finrank_span_singleton hune] at h1
    omega
  obtain ⟨v, hvker, hvnot⟩ : ∃ v ∈ LinearMap.ker φ, v ∉ Submodule.span (ZMod p) {u} := by
    by_contra h
    push Not at h
    exact hnotle fun x hx => h x hx
  by_cases hbv : B a v = 0
  · refine ⟨u + v, (LinearMap.ker φ).add_mem hu hvker, ?_, ?_⟩
    · intro hmem
      apply hvnot
      have : v = (u + v) - u := by abel
      rw [this]
      exact Submodule.sub_mem _ hmem (Submodule.subset_span (Set.mem_singleton u))
    · rw [map_add, hbv, add_zero]; exact hbau
  · exact ⟨v, hvker, hvnot, hbv⟩

private theorem sp_refl_ker_contra [Fact p.Prime] {B : LinearMap.BilinForm (ZMod p) U}
    (hBnd : B.Nondegenerate) {a u w : U} (hbau : B a u ≠ 0)
    (hwnot : w ∉ Submodule.span (ZMod p) {u})
    (hrel : ∀ y : U, B a w * B y u = B a u * B y w) : False := by
  have hsep : B a w • u - B a u • w = 0 := by
    apply hBnd.2
    intro y
    rw [map_sub, map_smul, map_smul]
    simp only [smul_eq_mul]
    rw [hrel y]
    exact sub_self _
  have hw_span : w ∈ Submodule.span (ZMod p) {u} := by
    have heq : B a u • w = B a w • u := (sub_eq_zero.mp hsep).symm
    have hw_eq : w = ((B a u)⁻¹ * B a w) • u := by
      calc w = (B a u)⁻¹ • (B a u • w) := (sp_inv_smul (B a u) hbau w).symm
        _ = (B a u)⁻¹ • (B a w • u) := by rw [heq]
        _ = ((B a u)⁻¹ * B a w) • u := by rw [smul_smul]
    rw [hw_eq]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_singleton u))
  exact hwnot hw_span

theorem false_of_isRefl_normalizes_sp [Fact p.Prime] [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {B : LinearMap.BilinForm (ZMod p) U} (hB : B.IsAlt)
    (hBnd : B.Nondegenerate) {r : U ≃ₗ[ZMod p] U} (hr : IsRefl p r)
    (hnorm : ∀ g : U ≃ₗ[ZMod p] U, (∀ x y, B (g x) (g y) = B x y) →
      ∀ x y, B ((r * g * r⁻¹) x) ((r * g * r⁻¹) y) = B x y) : False := by
  obtain ⟨a, φ, hφa, rfl⟩ := (isRefl_iff hp r).mp hr
  have h2 : (2 : ZMod p) ≠ 0 := wSlpmC_two_ne_zero hp
  have ha : a ≠ 0 := fun h => h2 (by rw [h, map_zero] at hφa; exact hφa.symm)
  have hker_orth : ∀ u : U, φ u = 0 → B a u = 0 := by
    intro u hu
    by_contra hbau
    obtain ⟨w, hwker, hwnot, hbaw⟩ := sp_refl_ker_w hp h3 hφa hu hbau
    exact sp_refl_ker_contra hBnd hbau hwnot fun y => sp_rel_scalar h2
      (two_mul_B_eq_of_refl_normalizes_sp hB hφa hnorm hu hbau y)
      (two_mul_B_eq_of_refl_normalizes_sp hB hφa hnorm hwker hbaw y)
  have hBa_zero : ∀ v : U, B a v = 0 := by
    intro v
    have hφw : φ (v - (2⁻¹ * φ v) • a) = 0 := by
      rw [map_sub, map_smul, hφa, smul_eq_mul]
      rw [sp_two_inv_mul (φ v) h2]
      exact sub_self _
    have h1 := hker_orth _ hφw
    have hsplit : B a v = B a (v - (2⁻¹ * φ v) • a) + B a ((2⁻¹ * φ v) • a) := by
      rw [← map_add]
      congr 1
      abel
    rw [hsplit, h1, map_smul, hB.self_eq_zero, smul_zero, add_zero]
  exact ha (hBnd.1 a hBa_zero)

private theorem exists_refl_of_reflGen [Fact p.Prime] {A : Subgroup (U ≃ₗ[ZMod p] U)}
    (hgen : ReflGen p A) (ht : ∃ t ∈ A, IsTransvectionLin t) : ∃ r ∈ A, IsRefl p r := by
  by_contra h
  push Not at h
  have hempty : {t : U ≃ₗ[ZMod p] U | t ∈ A ∧ IsRefl p t} = ∅ := by
    ext t
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    exact fun ht => h t ht.1 ht.2
  have hAbot : A = ⊥ := by rw [hgen, hempty, Subgroup.closure_empty]
  obtain ⟨t, htA, htT⟩ := ht
  obtain ⟨u, ψ, hu, hψ, hψu, htψ⟩ := htT
  have htne : t ≠ 1 := by
    intro h1
    obtain ⟨v, hv⟩ : ∃ v : U, ψ v ≠ 0 := by
      by_contra hh
      push Not at hh
      exact hψ (LinearMap.ext fun x => by simpa using hh x)
    have hvv : t v = v := by rw [h1]; rfl
    have hzero : ψ v • u = 0 := by
      have h' : v + ψ v • u = v := by rw [← htψ v, hvv]
      exact add_left_cancel (show v + ψ v • u = v + 0 by simpa using h')
    exact (smul_eq_zero.mp hzero).elim hv hu
  have : t ∈ (⊥ : Subgroup (U ≃ₗ[ZMod p] U)) := hAbot ▸ htA
  exact htne (by simpa using this)

private theorem det_eq_pm_one_of_mem_reflGen [Fact p.Prime] [Module.Finite (ZMod p) U]
    (hp : p ≠ 2) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p A)
    {g : U ≃ₗ[ZMod p] U} (hg : g ∈ A) :
    LinearEquiv.det g = 1 ∨ LinearEquiv.det g = -1 := by
  let H : Subgroup (U ≃ₗ[ZMod p] U) :=
    { carrier := {h | LinearEquiv.det h = 1 ∨ LinearEquiv.det h = -1}
      one_mem' := Or.inl (map_one _)
      mul_mem' := by
        rintro h k (hh | hh) (hk | hk)
        · exact Or.inl (by rw [map_mul, hh, hk, one_mul])
        · exact Or.inr (by rw [map_mul, hh, hk, one_mul])
        · exact Or.inr (by rw [map_mul, hh, hk, mul_one])
        · exact Or.inl (by rw [map_mul, hh, hk, neg_mul_neg, one_mul])
      inv_mem' := by
        rintro h (hh | hh)
        · exact Or.inl (by rw [map_inv, hh, inv_one])
        · exact Or.inr (by rw [map_inv, hh, inv_neg, inv_one]) }
  have hAH : A ≤ H := by
    rw [hgen, Subgroup.closure_le]
    rintro s ⟨hsA, hsRefl⟩
    exact Or.inr (det_eq_neg_one_of_isRefl hp hsRefl)
  exact hAH hg

theorem slpm_of_transvection [Fact p.Prime] [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p A)
    (hirr : ∀ W : Submodule (ZMod p) U, (∀ a ∈ A, ∀ w ∈ W, a w ∈ W) → W = ⊥ ∨ W = ⊤)
    (ht : ∃ t ∈ A, IsTransvectionLin t) (g : U ≃ₗ[ZMod p] U) :
    g ∈ A ↔ (LinearEquiv.det g = 1 ∨ LinearEquiv.det g = -1) := by
  have hdet : ∀ h : U ≃ₗ[ZMod p] U,
      LinearMap.det (h : U →ₗ[ZMod p] U) = 1 ↔ LinearEquiv.det h = 1 := by
    intro h
    rw [← LinearEquiv.coe_det]
    exact ⟨fun hh => Units.ext hh, fun hh => by rw [hh, Units.val_one]⟩
  have hTgen : ∃ S : Set (U ≃ₗ[ZMod p] U),
      (∀ t ∈ S, ∃ v f, CFSG.RankThree.Classical.IsTransvectionWith t v f) ∧
        transvectionClosure A = Subgroup.closure S := by
    refine ⟨{t : U ≃ₗ[ZMod p] U | t ∈ A ∧ IsTransvectionLin t}, ?_, rfl⟩
    rintro t ⟨htA, htT⟩
    obtain ⟨u, ψ, hu, hψ, hψu, htψ⟩ := htT
    exact ⟨u, ψ, hu, hψ, hψu, htψ⟩
  obtain ⟨r, hrA, hrRefl⟩ := exists_refl_of_reflGen hgen ht
  rcases CFSG.StandardType.McLaughlinOdd.mcLaughlin_odd hp (transvectionClosure A)
      (fun W hW => transvectionClosure_irreducible hgen hirr ht W hW) hTgen with
    hsl | ⟨B, hBalt, hBnd, hBiso⟩
  · have hdetr : LinearEquiv.det r = -1 := det_eq_neg_one_of_isRefl hp hrRefl
    constructor
    · intro hg
      exact det_eq_pm_one_of_mem_reflGen hp hgen hg
    · rintro (hg | hg)
      · have hgT : g ∈ transvectionClosure A := (hsl g).mpr ((hdet g).mpr hg)
        exact transvectionClosure_le A hgT
      · have hrgT : r⁻¹ * g ∈ transvectionClosure A := by
          apply (hsl (r⁻¹ * g)).mpr
          apply (hdet (r⁻¹ * g)).mpr
          rw [map_mul, map_inv, hdetr, hg, inv_neg, inv_one, neg_mul_neg, one_mul]
        have := A.mul_mem hrA (transvectionClosure_le A hrgT)
        rwa [mul_inv_cancel_left] at this
  · exfalso
    have hrnorm : ∀ h ∈ transvectionClosure A, r * h * r⁻¹ ∈ transvectionClosure A :=
      fun h hh => conj_mem_transvectionClosure hrA hh
    exact false_of_isRefl_normalizes_sp hp h3 hBalt hBnd hrRefl
      (fun h hh x y => (hBiso (r * h * r⁻¹)).mp (hrnorm h ((hBiso h).mpr hh)) x y)

theorem family_of_transvection [Fact p.Prime] [Module.Finite (ZMod p) U] (hp : p ≠ 2)
    (h3 : 3 ≤ Module.finrank (ZMod p) U) {A : Subgroup (U ≃ₗ[ZMod p] U)} (hgen : ReflGen p A)
    (hirr : AbsIrred p A) (ht : ∃ t ∈ A, IsTransvectionLin t) : Family p A :=
  .slpm (slpm_of_transvection hp h3 hgen hirr.1 ht)

end CFSG.StandardType.ZS
