module

public import CFSG.Quasithin.EmptyFaithful.SzN28X0Form

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin.SzN28

open CFSG.Quasithin.G11

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem vadd_self' {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (w : W) : w + w = 0 := by
  have h2 : (2 : ZMod 2) = 0 := by decide
  rw [← two_smul (ZMod 2) w, h2, zero_smul]

theorem vneg_self {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (w : W) : -w = w :=
  neg_eq_of_add_eq_zero_right (vadd_self' w)

theorem vsub_eq_add {W : Type*} [AddCommGroup W] [Module (ZMod 2) W] (a b : W) : a - b = a + b := by
  rw [sub_eq_add_neg, vneg_self]

namespace F8Form

variable {B : LinearMap.BilinForm (ZMod 2) V} {Γ A : Subgroup (GLV V)} {I I' : Submodule (ZMod 2) V}
  {x : GLV V} (c : F8Form B Γ A I I' x)

include c in
theorem exists_t {e₀ f₀ : V} (he : e₀ ∈ I) (hf : f₀ ∈ I') (hB0 : B e₀ f₀ = 0) :
    ∃ t : GLV V, t ∈ A ∧ ∀ v, t v = v + B v f₀ • e₀ + B v e₀ • f₀ := by
  let φ : Module.Dual (ZMod 2) ↥I := (B.flip f₀).comp I.subtype
  have hφ : φ ⟨e₀, he⟩ = 0 := hB0
  let g₀ : ↥I ≃ₗ[ZMod 2] ↥I := LinearEquiv.transvection hφ
  obtain ⟨t, htA, ht⟩ := c.data.twoNat.surj g₀
  have htI : ∀ i ∈ I, t i = i + B i f₀ • e₀ := by
    intro i hi
    have := ht ⟨i, hi⟩
    simpa [g₀, LinearEquiv.transvection.apply, LinearMap.transvection.apply, φ] using this
  have htΓ : t ∈ Γ := c.data.A_le htA
  have htI' : ∀ j ∈ I', t j = j + B e₀ j • f₀ := by
    intro j hj
    have htj : t j ∈ I' := c.data.A_inv_I' t htA j hj
    have z4 : ∀ a b c d : ZMod 2, a + b * c = d → a + d = c * b := by decide
    have hu : ∀ i ∈ I, B i (t j + j) = B i (B e₀ (t j) • f₀) := by
      intro i hi
      have h1 := c.isom t htΓ i j
      rw [htI i hi] at h1
      simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul] at h1
      simp only [map_add, map_smul, smul_eq_mul]
      exact z4 _ _ _ _ h1
    have hw : B e₀ (t j) • f₀ ∈ I' := I'.smul_mem _ hf
    have h2 : t j + j = B e₀ (t j) • f₀ := by
      have := c.pair_I' (I'.sub_mem (I'.add_mem htj hj) hw) (fun i hi => by
        rw [map_sub, hu i hi, sub_self])
      exact sub_eq_zero.1 this
    have h3 : B e₀ (t j) = B e₀ j := by
      have h4 := congrArg (fun y => B e₀ y) h2
      simp only [map_add, map_smul, smul_eq_mul, hB0, mul_zero] at h4
      have z5 : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
      exact z5 _ _ h4
    rw [h3] at h2
    calc t j = j + (t j + j) := by rw [add_comm (t j) j, ← add_assoc, vadd_self', zero_add]
      _ = j + B e₀ j • f₀ := by rw [h2]
  refine ⟨t, htA, fun v => ?_⟩
  have hv : v ∈ I ⊔ I' := by rw [c.data.compl.sup_eq_top]; trivial
  obtain ⟨i, hi, j, hj, rfl⟩ := Submodule.mem_sup.1 hv
  rw [map_add, htI i hi, htI' j hj]
  simp only [map_add, LinearMap.add_apply]
  have e1 : B i f₀ + B j f₀ = B i f₀ := by rw [c.iso_I' j hj f₀ hf, add_zero]
  have e2 : B i e₀ + B j e₀ = B e₀ j := by rw [c.iso_I i hi e₀ he, zero_add, c.symm j e₀]
  rw [e1, e2]
  abel

include c in
theorem t_sq {e₀ f₀ : V} {t : GLV V} (hB0 : B e₀ f₀ = 0)
    (ht : ∀ v, t v = v + B v f₀ • e₀ + B v e₀ • f₀) : t * t = 1 := by
  have hB0' : B f₀ e₀ = 0 := by rw [c.symm]; exact hB0
  apply LinearEquiv.ext
  intro v
  show t (t v) = v
  have h1 : B (t v) f₀ = B v f₀ := by
    rw [ht v]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hB0,
      c.alt f₀, mul_zero, add_zero]
  have h2 : B (t v) e₀ = B v e₀ := by
    rw [ht v]
    simp only [map_add, LinearMap.add_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, hB0',
      c.alt e₀, mul_zero, add_zero]
  rw [ht (t v), h1, h2, ht v]
  have e3 : v + B v f₀ • e₀ + B v e₀ • f₀ + B v f₀ • e₀ + B v e₀ • f₀ =
      v + (B v f₀ • e₀ + B v f₀ • e₀) + (B v e₀ • f₀ + B v e₀ • f₀) := by abel
  rw [e3, vadd_self', vadd_self', add_zero, add_zero]

include c in
theorem t_fix {e₀ f₀ : V} {t : GLV V} (hB0 : B e₀ f₀ = 0)
    (ht : ∀ v, t v = v + B v f₀ • e₀ + B v e₀ • f₀) : t (e₀ + f₀) = e₀ + f₀ := by
  have hB0' : B f₀ e₀ = 0 := by rw [c.symm]; exact hB0
  rw [ht]
  simp only [map_add, LinearMap.add_apply, hB0, hB0', c.alt e₀, c.alt f₀, add_zero, zero_smul]

include c in
theorem t_ne_one {e₀ f₀ : V} {t : GLV V} (he : e₀ ∈ I) (hf : f₀ ∈ I') (he0 : e₀ ≠ 0) (hf0 : f₀ ≠ 0)
    (ht : ∀ v, t v = v + B v f₀ • e₀ + B v e₀ • f₀) : t ≠ 1 := by
  intro h1
  obtain ⟨i, hi, hBi⟩ : ∃ i ∈ I, B i f₀ ≠ 0 := by
    by_contra hall
    push Not at hall
    exact hf0 (c.pair_I' hf hall)
  have key2 : ∀ y : ZMod 2, y ≠ 0 → y = 1 := by decide
  have h2 := ht i
  rw [h1, c.iso_I i hi e₀ he, key2 _ hBi] at h2
  simp only [one_smul, zero_smul, add_zero] at h2
  have h3 : (1 : GLV V) i = i := rfl
  rw [h3] at h2
  have : e₀ = 0 := by simpa using h2
  exact he0 this

include c in
theorem t_comm {e₀ f₀ : V} {t : GLV V} (he : e₀ ∈ I) (hf : f₀ ∈ I')
    (ht : ∀ v, t v = v + B v f₀ • e₀ + B v e₀ • f₀) {γ : GLV V} (hγ : γ ∈ Γ)
    (hfix : γ (e₀ + f₀) = e₀ + f₀) : γ * t = t * γ := by
  apply LinearEquiv.ext
  intro v
  show γ (t v) = t (γ v)
  rw [ht v, ht (γ v)]
  simp only [map_add, map_smul]
  rcases c.act_fix hγ he hf hfix with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
  · have e1 : B (γ v) f₀ = B v f₀ := by
      have := c.isom γ hγ v f₀
      rwa [h2] at this
    have e2 : B (γ v) e₀ = B v e₀ := by
      have := c.isom γ hγ v e₀
      rwa [h1] at this
    rw [h1, h2, e1, e2]
  · have e1 : B (γ v) f₀ = B v e₀ := by
      have := c.isom γ hγ v e₀
      rwa [h1] at this
    have e2 : B (γ v) e₀ = B v f₀ := by
      have := c.isom γ hγ v f₀
      rwa [h2] at this
    rw [h1, h2, e1, e2]
    abel

include c in
theorem sub_perp {e₀ f₀ : V} (he : e₀ ∈ I) (hf : f₀ ∈ I') {γ : GLV V} (hγ : γ ∈ Γ)
    (hfix : γ (e₀ + f₀) = e₀ + f₀) {v : V} (hv : B (e₀ + f₀) v = 0) :
    B (γ v - v) e₀ = 0 ∧ B (γ v - v) f₀ = 0 := by
  have hγ' : γ⁻¹ ∈ Γ := Γ.inv_mem hγ
  have hfix' : γ⁻¹ (e₀ + f₀) = e₀ + f₀ := by
    have h2 : (γ⁻¹ * γ) (e₀ + f₀) = e₀ + f₀ := by rw [inv_mul_cancel]; rfl
    calc γ⁻¹ (e₀ + f₀) = γ⁻¹ (γ (e₀ + f₀)) := by rw [hfix]
      _ = e₀ + f₀ := h2
  have hvv : B v (e₀ + f₀) = 0 := by rw [c.symm]; exact hv
  have key : ∀ w : V, B (γ v) w = B v (γ⁻¹ w) := by
    intro w
    have := c.isom γ⁻¹ hγ' (γ v) w
    have h3 : γ⁻¹ (γ v) = v := by
      have : (γ⁻¹ * γ) v = v := by rw [inv_mul_cancel]; rfl
      exact this
    rw [h3] at this
    exact this.symm
  have hBv : B v e₀ = B v f₀ := by
    rw [map_add] at hvv
    have z : ∀ a b : ZMod 2, a + b = 0 → a = b := by decide
    exact z _ _ hvv
  rcases c.act_fix hγ' he hf hfix' with ⟨-, h1, h2⟩ | ⟨-, h1, h2⟩
  · refine ⟨?_, ?_⟩
    · rw [map_sub, LinearMap.sub_apply, key, h1, sub_self]
    · rw [map_sub, LinearMap.sub_apply, key, h2, sub_self]
  · refine ⟨?_, ?_⟩
    · rw [map_sub, LinearMap.sub_apply, key, h1, hBv, sub_self]
    · rw [map_sub, LinearMap.sub_apply, key, h2, hBv, sub_self]

end F8Form

end CFSG.Quasithin.SzN28
