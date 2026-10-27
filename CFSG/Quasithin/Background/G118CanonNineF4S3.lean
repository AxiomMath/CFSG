module

public import CFSG.Quasithin.Background.G11BridgeRestrict
public import CFSG.Quasithin.Background.G118CanonNineF2TensorBuild
public import CFSG.Quasithin.Background.G118CanonNineF2TensorPts

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

namespace Canon

namespace F4Tensor

open F2Tensor

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V] [Finite V]
  {H : Subgroup (GLV V)} {I : Submodule (ZMod 2) V}

@[expose] def fixSub (y : GLV V) : Submodule (ZMod 2) V :=
  LinearMap.ker ((y : V →ₗ[ZMod 2] V) - LinearMap.id)

omit [Finite V] in
theorem mem_fixSub {y : GLV V} {v : V} : v ∈ fixSub y ↔ y v = v := by
  simp [fixSub, LinearMap.mem_ker, sub_eq_zero]

omit [Finite V] in
theorem invariant_fixSub {c : GLV V} (hcH : ∀ h ∈ H, h * c = c * h) :
    Invariant H (fixSub c) := by
  intro h hh v hv
  rw [mem_fixSub] at hv ⊢
  have h1 : h (c v) = c (h v) := congrArg (fun g : GLV V => g v) (hcH h hh)
  rw [← h1, hv]

omit [Finite V] in
theorem add_eq_sub'' (a b : V) : a + b = a - b := by
  rw [sub_eq_add_neg, neg_eq_of_add_eq_zero_left (add_self_eq_zero'' b)]

omit [Finite V] in
theorem cube_apply {c : GLV V} (hc3 : c ^ 3 = 1) (v : V) : c (c (c v)) = v := by
  have h := congrArg (fun g : GLV V => g v) hc3
  simpa [pow_three, LinearEquiv.mul_apply] using h

omit [Finite V] in
theorem inv_apply_of_cube {c : GLV V} (hc3 : c ^ 3 = 1) (v : V) : c⁻¹ v = c (c v) := by
  have h : c⁻¹ = c * c :=
    inv_eq_of_mul_eq_one_right (by rw [← mul_assoc, ← pow_three']; exact hc3)
  rw [h]
  rfl

omit [Finite V] in
theorem conj_apply_s3 {c y : GLV V} (hc3 : c ^ 3 = 1) (hyc : y * c = c⁻¹ * y) (v : V) :
    y (c v) = c (c (y v)) := by
  have h := congrArg (fun g : GLV V => g v) hyc
  have h1 : y (c v) = c⁻¹ (y v) := h
  rw [h1, inv_apply_of_cube hc3]

theorem fixed_eq_zero_s3 (D : E11Data H I) (hU : Module.finrank D.F D.U = 2)
    (hdim : Module.finrank (ZMod 2) V = 8) {c y : GLV V}
    (hcH : ∀ h ∈ H, h * c = c * h) (hyH : ∀ h ∈ H, h * y = y * h)
    (hc3 : c ^ 3 = 1) (hc1 : c ≠ 1) (hy2 : y * y = 1) (hyc : y * c = c⁻¹ * y) :
    ∀ v : V, c v = v → v = 0 := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hc3' := cube_apply hc3
  have hy2' : ∀ v, y (y v) = v := fun v => by
    have h := congrArg (fun g : GLV V => g v) hy2
    simpa [LinearEquiv.mul_apply] using h
  have hyc' := conj_apply_s3 hc3 hyc
  have hcommc : ∀ h ∈ H, ∀ v, h (c v) = c (h v) := fun h hh v =>
    congrArg (fun g : GLV V => g v) (hcH h hh)
  have hcommy : ∀ h ∈ H, ∀ v, h (y v) = y (h v) := fun h hh v =>
    congrArg (fun g : GLV V => g v) (hyH h hh)
  let P : V →ₗ[ZMod 2] V :=
    (c : V →ₗ[ZMod 2] V) ∘ₗ (c : V →ₗ[ZMod 2] V) + (c : V →ₗ[ZMod 2] V) + LinearMap.id
  let M : Submodule (ZMod 2) V := fixSub c
  let N : Submodule (ZMod 2) V := LinearMap.ker P
  have hmemN : ∀ v, v ∈ N ↔ c (c v) + c v + v = 0 := fun v => by
    simp [N, P, LinearMap.mem_ker]
  have hmemM : ∀ v, v ∈ M ↔ c v = v := fun v => mem_fixSub
  have hMN : M ⊓ N = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxM, hxN⟩
    have h := (hmemN x).1 hxN
    rw [(hmemM x).1 hxM, (hmemM x).1 hxM, add_self_eq_zero'', zero_add] at h
    exact h
  have hMN' : M ⊔ N = ⊤ := by
    rw [eq_top_iff]
    intro v _
    have h1 : c (c v) + c v + v ∈ M := by
      rw [hmemM, map_add, map_add, hc3' v]
      abel
    have h2 : c (c v) + c v ∈ N := by
      rw [hmemN]
      have e1 : c (c (c v) + c v) = v + c (c v) := by rw [map_add, hc3' v]
      have e2 : c (c (c (c v) + c v)) = c v + v := by rw [e1, map_add, hc3' v]
      rw [e2, e1]
      have : c v + v + (v + c (c v)) + (c (c v) + c v) =
          (c v + c v) + (v + v) + (c (c v) + c (c v)) := by abel
      rw [this, add_self_eq_zero'' (c v), add_self_eq_zero'' v, add_self_eq_zero'' (c (c v)),
        add_zero, add_zero]
    have h3 : (c (c v) + c v + v) + (c (c v) + c v) = v := by
      have : (c (c v) + c v + v) + (c (c v) + c v) =
          (c (c v) + c (c v)) + (c v + c v) + v := by abel
      rw [this, add_self_eq_zero'' (c (c v)), add_self_eq_zero'' (c v), zero_add, zero_add]
    exact Submodule.mem_sup.2 ⟨_, h1, _, h2, h3⟩
  have hMinv : Invariant H M := invariant_fixSub hcH
  have hNinv : Invariant H N := by
    intro h hh v hv
    rw [hmemN] at hv ⊢
    rw [← hcommc h hh v, ← hcommc h hh (c v), ← map_add, ← map_add, hv, map_zero]
  have hcN : ∀ x ∈ N, c x ∈ N := by
    intro x hx
    rw [hmemN] at hx ⊢
    have := congrArg (fun z : V => c z) hx
    simp only [map_add, map_zero] at this
    exact this
  have hyN : ∀ x ∈ N, y x ∈ N := by
    intro x hx
    rw [hmemN] at hx ⊢
    have h1 : y (c (c x)) = c (y x) := by
      rw [hyc' (c x), hyc' x]
      exact hc3' (c (y x))
    have := congrArg (fun z : V => y z) hx
    simp only [map_add, map_zero] at this
    rw [h1, hyc' x] at this
    rw [add_comm (c (c (y x))) (c (y x))]
    exact this
  have hcompl : IsCompl M N := ⟨disjoint_iff.2 hMN, codisjoint_iff.2 hMN'⟩
  have hsum := Submodule.finrank_add_eq_of_isCompl hcompl
  rw [hdim] at hsum
  obtain ⟨a, ha⟩ := four_dvd D hU hdim hMinv
  obtain ⟨b, hb⟩ := four_dvd D hU hdim hNinv
  have hb012 : b = 0 ∨ b = 1 ∨ b = 2 := by omega
  rcases hb012 with rfl | rfl | rfl
  ·
    exfalso
    have hN0 : N = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
    apply hc1
    refine LinearEquiv.ext fun v => ?_
    have hv : v ∈ M ⊔ N := by rw [hMN']; exact Submodule.mem_top
    rw [hN0, sup_bot_eq] at hv
    exact (hmemM v).1 hv
  ·
    exfalso
    have h4 : Module.finrank (ZMod 2) N = 4 := by omega
    have hirr : IsIrr H N :=
      ⟨hNinv, bot_lt_iff_ne_bot.2 fun h => by rw [h, finrank_bot] at h4; omega,
        fun J hJ _ hJN => irr_of_finrank_four D hU hdim h4 hJ hJN⟩
    have hyNeq : conjSub y N = N := by
      refine Submodule.eq_of_le_of_finrank_eq ?_ (finrank_conjSub y N)
      rintro _ ⟨x, hx, rfl⟩
      exact hyN x hx
    have hyfix := fixes_of_commute_sq_eq_one hirr hy2 hyNeq
      (fun k hk i _ => (hcommy k hk i).symm)
    have hNM : N ≤ M := by
      intro x hx
      rw [hmemM]
      have h1 : y (c x) = c x := hyfix (c x) (hcN x hx)
      have h2 : y (c x) = c (c x) := by rw [hyc' x, hyfix x hx]
      exact c.injective (h2.symm.trans h1)
    have hN0 : N = ⊥ := by
      rw [← inf_eq_left.2 hNM, inf_comm]
      exact hMN
    rw [hN0, finrank_bot] at h4
    omega
  ·
    intro v hv
    have hM0 : M = ⊥ := Submodule.finrank_eq_zero.1 (by omega)
    have : v ∈ M := (hmemM v).2 hv
    rw [hM0, Submodule.mem_bot] at this
    exact this

theorem fixSub_s3 (hdim : Module.finrank (ZMod 2) V = 8) {c y : GLV V} (hc3 : c ^ 3 = 1)
    (hy2 : y * y = 1) (hyc : y * c = c⁻¹ * y) (hfree : ∀ v : V, c v = v → v = 0) :
    Module.finrank (ZMod 2) (fixSub y) = 4 ∧ fixSub y ⊓ conjSub c (fixSub y) = ⊥ ∧
      fixSub y ⊔ conjSub c (fixSub y) = ⊤ := by
  haveI : Module.Finite (ZMod 2) V := Module.Finite.of_finite
  have hy2' : ∀ v, y (y v) = v := fun v => by
    have h := congrArg (fun g : GLV V => g v) hy2
    simpa [LinearEquiv.mul_apply] using h
  have hyc' := conj_apply_s3 hc3 hyc
  have hinf : fixSub y ⊓ conjSub c (fixSub y) = ⊥ := by
    rw [eq_bot_iff]
    rintro x ⟨hxB, hxc⟩
    have hb' : c.symm x ∈ fixSub y := mem_conjSub.1 hxc
    have hxb : c (c.symm x) = x := c.apply_symm_apply x
    have h1 : y x = x := mem_fixSub.1 hxB
    have h2 : y (c.symm x) = c.symm x := mem_fixSub.1 hb'
    have h3 : c (c (c.symm x)) = c (c.symm x) := by
      have h4 := hyc' (c.symm x)
      rw [h2] at h4
      rw [← h4, hxb]
      exact h1
    have h5 : c (c.symm x) = c.symm x := c.injective h3
    have h6 : c.symm x = 0 := hfree _ h5
    rw [Submodule.mem_bot, ← hxb, h6, map_zero]
  have hge : 8 ≤ 2 * Module.finrank (ZMod 2) (fixSub y) := by
    let t : V →ₗ[ZMod 2] V := (y : V →ₗ[ZMod 2] V) - LinearMap.id
    have hker : LinearMap.ker t = fixSub y := rfl
    have hrange : LinearMap.range t ≤ fixSub y := by
      rintro _ ⟨v, rfl⟩
      rw [mem_fixSub]
      show y (y v - v) = y v - v
      rw [map_sub, hy2' v, ← add_eq_sub'', ← add_eq_sub'', add_comm]
    have h1 := LinearMap.finrank_range_add_finrank_ker t
    have h2 := Submodule.finrank_mono hrange
    rw [hker, hdim] at h1
    omega
  have hsum := Submodule.finrank_sup_add_finrank_inf_eq (fixSub y) (conjSub c (fixSub y))
  rw [hinf, finrank_bot, finrank_conjSub] at hsum
  have hle : Module.finrank (ZMod 2) ↥(fixSub y ⊔ conjSub c (fixSub y)) ≤ 8 := by
    rw [← hdim]
    exact Submodule.finrank_le _
  have h4 : Module.finrank (ZMod 2) (fixSub y) = 4 := by omega
  refine ⟨h4, hinf, Submodule.eq_top_of_finrank_eq ?_⟩
  rw [hdim]
  omega

omit [Finite V] in
theorem conj_fixSub_s3 {c y : GLV V} (hc3 : c ^ 3 = 1) (hyc : y * c = c⁻¹ * y) {b : V}
    (hb : b ∈ fixSub y) : y (c b) = c (c b) := by
  rw [conj_apply_s3 hc3 hyc, mem_fixSub.1 hb]

end F4Tensor

end Canon

end G11

end CFSG.Quasithin
