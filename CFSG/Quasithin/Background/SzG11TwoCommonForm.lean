module

public import CFSG.Quasithin.Background.SzG11TwoCommonSyl

public section

namespace CFSG.Quasithin.G11.SzG11S.Two

open CFSG.Quasithin CFSG.Quasithin.SzG11NC

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]
  {B : LinearMap.BilinForm (ZMod 2) V} {Γ X X₀ : Subgroup (GLV V)} {v₁ : V}
  {W : Submodule (ZMod 2) V}

theorem exists_nonzero_addHom {E : Type} [Field E] [CharP E 2] : ∃ ℓ : E →+ ZMod 2, ℓ ≠ 0 := by
  let _ : Algebra (ZMod 2) E := ZMod.algebra E 2
  have h : ¬ ∀ φ : Module.Dual (ZMod 2) E, φ 1 = 0 := fun h' =>
    one_ne_zero ((Module.forall_dual_apply_eq_zero_iff (ZMod 2) (1 : E)).1 h')
  push Not at h
  obtain ⟨φ, hφ⟩ := h
  exact ⟨φ.toAddMonoidHom, fun h0 => hφ (by simpa using congrArg (fun f => f 1) h0)⟩

theorem exists_apply_ne_zero {E : Type} [Field E] (ℓ : E →+ ZMod 2) (hℓ : ℓ ≠ 0) :
    ∃ μ, ℓ μ ≠ 0 := by
  by_contra h
  push Not at h
  exact hℓ (AddMonoidHom.ext h)

theorem eq_zero_of_forall_ell {E : Type} [Field E] (ℓ : E →+ ZMod 2) (hℓ : ℓ ≠ 0) {j : E}
    (hj : ∀ κ, ℓ (κ * j) = 0) : j = 0 := by
  by_contra hj0
  obtain ⟨μ, hμ⟩ := exists_apply_ne_zero ℓ hℓ
  apply hμ
  have := hj (μ * j⁻¹)
  rwa [mul_assoc, inv_mul_cancel₀ hj0, mul_one] at this

theorem exists_scalar_form [Finite V] (hyp : G101Hyp B Γ v₁ W X X₀) {H : Subgroup (GLV V)}
    (hirr : IsIrr H ⊤) (hHΓ : H ≤ Γ) (J : LinearMap.BilinForm (CommF H hirr) V)
    (hJnd : J.Nondegenerate) (hJinv : ∀ h ∈ H, ∀ u v, J (h u) (h v) = J u v)
    (ℓ : CommF H hirr →+ ZMod 2) (hℓ : ℓ ≠ 0) :
    ∃ c : CommF H hirr, c ≠ 0 ∧ ∀ u v, B u v = ℓ (c * J u v) := by
  classical
  let Λ : LinearMap.BilinForm (ZMod 2) V :=
    LinearMap.mk₂ (ZMod 2) (fun w u => ℓ (J u w))
      (fun w w' u => by rw [map_add, map_add])
      (fun c w u => by rcases zmod_two_cases c with rfl | rfl <;> simp)
      (fun w u u' => by rw [map_add, LinearMap.add_apply, map_add])
      (fun c w u => by rcases zmod_two_cases c with rfl | rfl <;> simp)
  have hΛ : ∀ w u, Λ w u = ℓ (J u w) := fun w u => rfl
  have hΛnd : Λ.Nondegenerate := by
    refine ⟨fun w hw => ?_, fun u hu => ?_⟩
    · apply hJnd.2 w
      intro u
      apply eq_zero_of_forall_ell ℓ hℓ
      intro κ
      have := hw (κ • u)
      rw [hΛ, map_smul, LinearMap.smul_apply, smul_eq_mul] at this
      exact this
    · apply hJnd.1 u
      intro w
      apply eq_zero_of_forall_ell ℓ hℓ
      intro κ
      have := hu (κ • w)
      rw [hΛ, map_smul, smul_eq_mul] at this
      exact this
  let T : V ≃ₗ[ZMod 2] Module.Dual (ZMod 2) V := Λ.toDual hΛnd
  have hT : ∀ w u, T w u = ℓ (J u w) := fun w u => LinearMap.BilinForm.toDual_def hΛnd
  let Af : V →ₗ[ZMod 2] V := (T.symm : Module.Dual (ZMod 2) V →ₗ[ZMod 2] V).comp B.flip
  have hAf' : ∀ v u, ℓ (J u (Af v)) = B u v := fun v u => by
    have h1 : T (Af v) = B.flip v := T.apply_symm_apply (B.flip v)
    rw [← hT, h1]
    rfl
  have hAcomm : ∀ h ∈ H, ∀ v, Af (h v) = h (Af v) := by
    intro h hh v
    apply T.injective
    apply LinearMap.ext
    intro u
    rw [hT, hT, hAf']
    have hu : h (h⁻¹ u) = u := LinearEquiv.apply_symm_apply h u
    have h1 : J u (h (Af v)) = J (h⁻¹ u) (Af v) := by
      have := hJinv h hh (h⁻¹ u) (Af v)
      rwa [hu] at this
    rw [h1, hAf']
    have h2 := hyp.isometry h (hHΓ hh) (h⁻¹ u) v
    rw [hu] at h2
    exact h2
  have hAmem : (Af : Module.End (ZMod 2) V) ∈ commutantOf H :=
    mem_commutantOf.2 fun h hh v => hAcomm h hh v
  let e : CommF H hirr := CommF.mk (hirr := hirr) Af hAmem
  have hev : ∀ v, e • v = Af v := fun v => rfl
  refine ⟨e, ?_, fun u v => ?_⟩
  · intro he
    apply hyp.point
    apply hyp.nondegenerate
    intro w
    rw [← hAf' w v₁, ← hev, he, zero_smul, map_zero, map_zero]
  · rw [← hAf' v u, ← hev, map_smul, smul_eq_mul]

theorem Ysp_eq_ker {E : Type} [Field E] [Module E V] (J : LinearMap.BilinForm E V)
    (ℓ : E →+ ZMod 2) (hℓ : ℓ ≠ 0) {c : E} (hc : c ≠ 0)
    (hB : ∀ u v, B u v = ℓ (c * J u v)) (v₁ : V) :
    Ysp E B v₁ = LinearMap.ker (J v₁) := by
  ext y
  rw [LinearMap.mem_ker, mem_Ysp]
  constructor
  · intro h
    have hy : ∀ κ, ℓ (κ * (c * J v₁ y)) = 0 := fun κ => by
      have := h κ
      rw [hB, map_smul, smul_eq_mul] at this
      rw [← this]
      congr 1
      ring
    exact (mul_eq_zero.1 (eq_zero_of_forall_ell ℓ hℓ hy)).resolve_left hc
  · intro h κ
    rw [hB, map_smul, h]
    simp

end CFSG.Quasithin.G11.SzG11S.Two
