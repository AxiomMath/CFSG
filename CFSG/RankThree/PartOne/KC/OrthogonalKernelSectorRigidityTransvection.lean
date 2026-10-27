module

public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Dual.Lemmas
public import Mathlib.Tactic.NoncommRing

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open Module

section Det

variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W] [FiniteDimensional E W]

theorem det_one_add_of_range_le_ker (δ : Module.End E W) (U : Submodule E W)
    (h1 : ∀ v, δ v ∈ U) (h2 : ∀ u ∈ U, δ u = 0) : LinearMap.det (1 + δ) = 1 := by
  have hU : U ≤ U.comap (1 + δ) := by
    intro w hw
    simp only [Submodule.mem_comap, LinearMap.add_apply, Module.End.one_apply, h2 w hw, add_zero]
    exact hw
  rw [LinearMap.det_eq_det_mul_det U (1 + δ) hU]
  have e1 : (1 + δ).restrict hU = LinearMap.id := by
    ext ⟨w, hw⟩
    simp [LinearMap.restrict_apply, h2 w hw]
  have e2 : U.mapQ U (1 + δ) hU = LinearMap.id := by
    refine Submodule.linearMap_qext _ ?_
    ext v
    simp only [LinearMap.coe_comp, Function.comp_apply, Submodule.mkQ_apply, Submodule.mapQ_apply,
      LinearMap.add_apply, Module.End.one_apply, LinearMap.id_comp]
    rw [Submodule.Quotient.eq]
    simpa using U.neg_mem (h1 v)
  rw [e1, e2, LinearMap.det_id, LinearMap.det_id, one_mul]

end Det

section Transvection

variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W]

theorem smulRight_mul_self (φ : W →ₗ[E] E) (w : W) (hφ : φ w = 0) :
    φ.smulRight w * φ.smulRight w = 0 := by
  ext y
  simp [Module.End.mul_apply, hφ]

@[expose] def transvectionUnit (φ : W →ₗ[E] E) (w : W) (hφ : φ w = 0) : (Module.End E W)ˣ where
  val := 1 + φ.smulRight w
  inv := 1 - φ.smulRight w
  val_inv := by
    have h := smulRight_mul_self φ w hφ
    calc (1 + φ.smulRight w) * (1 - φ.smulRight w) = 1 - φ.smulRight w * φ.smulRight w := by
          noncomm_ring
      _ = 1 := by rw [h, sub_zero]
  inv_val := by
    have h := smulRight_mul_self φ w hφ
    calc (1 - φ.smulRight w) * (1 + φ.smulRight w) = 1 - φ.smulRight w * φ.smulRight w := by
          noncomm_ring
      _ = 1 := by rw [h, sub_zero]

theorem transvectionUnit_apply (φ : W →ₗ[E] E) (w : W) (hφ : φ w = 0) (y : W) :
    ((transvectionUnit φ w hφ : (Module.End E W)ˣ) : Module.End E W) y = y + φ y • w :=
  rfl

theorem det_transvectionUnit [FiniteDimensional E W] (φ : W →ₗ[E] E) (w : W) (hφ : φ w = 0) :
    LinearMap.det ((transvectionUnit φ w hφ : (Module.End E W)ˣ) : Module.End E W) = 1 := by
  refine det_one_add_of_range_le_ker (φ.smulRight w) (Submodule.span E {w}) (fun v => ?_)
    (fun u hu => ?_)
  · exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self w)
  · obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.mp hu
    simp [hφ]

theorem exists_functional_of_not_mem_span {u w : W} (h : u ∉ Submodule.span E {w}) :
    ∃ φ : W →ₗ[E] E, φ u = 1 ∧ φ w = 0 := by
  obtain ⟨f, hf, hmap⟩ := Submodule.exists_dual_map_eq_bot_of_notMem h inferInstance
  have hfw : f w = 0 := by
    have hw : f w ∈ (Submodule.span E {w}).map f :=
      Submodule.mem_map_of_mem (Submodule.mem_span_singleton_self w)
    rw [hmap] at hw
    simpa using hw
  refine ⟨(f u)⁻¹ • f, ?_, ?_⟩
  · simp [hf]
  · simp [hfw]

end Transvection

section Unitary

variable {E W : Type*} [Field E] [AddCommGroup W] [Module E W] (σ : E →+* E) (H : W → W → E)

@[expose] def hermTransvectionForm (hadd₂ : ∀ u w w', H u (w + w') = H u w + H u w')
    (hsm₂ : ∀ (c : E) u w, H u (c • w) = c * H u w) (e : W) (a : E) : W →ₗ[E] E where
  toFun y := a * H e y
  map_add' y z := by rw [hadd₂, mul_add]
  map_smul' c y := by
    rw [hsm₂, RingHom.id_apply, smul_eq_mul]
    ring

@[expose] def unitaryTransvection (hadd₂ : ∀ u w w', H u (w + w') = H u w + H u w')
    (hsm₂ : ∀ (c : E) u w, H u (c • w) = c * H u w) {e : W} (he : H e e = 0) (a : E) :
    (Module.End E W)ˣ :=
  transvectionUnit (hermTransvectionForm H hadd₂ hsm₂ e a) e (by simp [hermTransvectionForm, he])

theorem unitaryTransvection_apply (hadd₂ : ∀ u w w', H u (w + w') = H u w + H u w')
    (hsm₂ : ∀ (c : E) u w, H u (c • w) = c * H u w) {e : W} (he : H e e = 0) (a : E) (y : W) :
    ((unitaryTransvection H hadd₂ hsm₂ he a : (Module.End E W)ˣ) : Module.End E W) y =
      y + (a * H e y) • e :=
  rfl

theorem det_unitaryTransvection [FiniteDimensional E W]
    (hadd₂ : ∀ u w w', H u (w + w') = H u w + H u w')
    (hsm₂ : ∀ (c : E) u w, H u (c • w) = c * H u w) {e : W} (he : H e e = 0) (a : E) :
    LinearMap.det ((unitaryTransvection H hadd₂ hsm₂ he a : (Module.End E W)ˣ) :
      Module.End E W) = 1 :=
  det_transvectionUnit _ _ _

theorem hermitian_transvection_preserves (hadd₁ : ∀ u u' w, H (u + u') w = H u w + H u' w)
    (hadd₂ : ∀ u w w', H u (w + w') = H u w + H u w')
    (hsm₁ : ∀ (c : E) u w, H (c • u) w = σ c * H u w)
    (hsm₂ : ∀ (c : E) u w, H u (c • w) = c * H u w)
    (hsymm : ∀ u w, H w u = σ (H u w)) {e : W} (he : H e e = 0) {a : E} (ha : σ a = -a)
    (y z : W) :
    H (y + (a * H e y) • e) (z + (a * H e z) • e) = H y z := by
  simp only [hadd₁, hadd₂, hsm₁, hsm₂, he, hsymm e y, map_mul, ha]
  ring

end Unitary

end CFSG.RankThree.PartOne.KCOrthogonal
