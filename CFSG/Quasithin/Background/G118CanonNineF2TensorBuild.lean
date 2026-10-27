module

public import CFSG.Quasithin.Background.G118CanonNineF2TensorPerm

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

namespace Canon

namespace F2Tensor

open scoped TensorProduct

variable {V : Type} [AddCommGroup V] [Module (ZMod 2) V]

theorem add_self_eq_zero'' (v : V) : v + v = 0 := by
  rw [← two_smul (ZMod 2) v, show (2 : ZMod 2) = 0 by decide, zero_smul]

theorem sq_eq_add_of_cube (c : GLV V) (h3 : c ^ 3 = 1) (hfix : ∀ v : V, c v = v → v = 0)
    (v : V) : c (c v) = c v + v := by
  have hc3 : c (c (c v)) = v := by
    rw [pow_three] at h3
    have h := congrArg (fun g : GLV V => g v) h3
    simpa only [LinearEquiv.mul_apply, LinearEquiv.coe_one, id_eq] using h
  have h0 : c (c v) + c v + v = 0 := hfix _ (by rw [map_add, map_add, hc3]; abel)
  calc c (c v) = c (c v) + c v + v + (c v + v) := by
        rw [add_assoc (c (c v)) (c v) v, add_assoc, add_self_eq_zero'' (c v + v), add_zero]
    _ = c v + v := by rw [h0, zero_add]

@[expose] noncomputable def tensorMap (β : ↥(permCore 5) →ₗ[ZMod 2] V) (c : GLV V) :
    (↥(permCore 3) ⊗[ZMod 2] ↥(permCore 5)) →ₗ[ZMod 2] V :=
  TensorProduct.lift (coord0.smulRight β + coord2.smulRight ((c : V →ₗ[ZMod 2] V) ∘ₗ β))

theorem tensorMap_tmul (β : ↥(permCore 5) →ₗ[ZMod 2] V) (c : GLV V) (x : ↥(permCore 3))
    (a : ↥(permCore 5)) : tensorMap β c (x ⊗ₜ a) = coord0 x • β a + coord2 x • c (β a) := by
  simp [tensorMap, TensorProduct.lift.tmul]

theorem tensorMap_w1 (β : ↥(permCore 5) →ₗ[ZMod 2] V) (c : GLV V) (a : ↥(permCore 5)) :
    tensorMap β c (w1 ⊗ₜ a) = β a := by
  rw [tensorMap_tmul, coord0_w1, coord2_w1, one_smul, zero_smul, add_zero]

theorem tensorMap_w2 (β : ↥(permCore 5) →ₗ[ZMod 2] V) (c : GLV V) (a : ↥(permCore 5)) :
    tensorMap β c (w2 ⊗ₜ a) = c (β a) := by
  rw [tensorMap_tmul, coord0_w2, coord2_w2, one_smul, zero_smul, zero_add]

section Equivariance

variable (β : ↥(permCore 5) →ₗ[ZMod 2] V) (c : GLV V)

theorem tensorMap_smul_tmul (u : ZMod 2) (x : ↥(permCore 3)) (a : ↥(permCore 5)) :
    tensorMap β c ((u • x) ⊗ₜ a) = u • tensorMap β c (x ⊗ₜ a) := by
  rw [← TensorProduct.smul_tmul', map_smul]

theorem tensorMap_rho (hcc : ∀ a, c (c (β a)) = c (β a) + β a) (x : ↥(permCore 3))
    (a : ↥(permCore 5)) :
    tensorMap β c (permActCore 3 rho3 x ⊗ₜ a) = c (tensorMap β c (x ⊗ₜ a)) := by
  have hx : permActCore 3 rho3 x = coord0 x • w2 + coord2 x • (w1 + w2) := by
    conv_lhs => rw [decomp3' x]
    rw [permActCore_add, permActCore_smul, permActCore_smul, rho3_w1, rho3_w2]
  simp only [hx, TensorProduct.add_tmul, map_add, tensorMap_smul_tmul, tensorMap_w1,
    tensorMap_w2]
  rw [tensorMap_tmul, map_add, map_smul, map_smul, hcc]
  module

theorem tensorMap_tau (y : GLV V) (hyβ : ∀ a, y (β a) = β a)
    (hyc : ∀ a, y (c (β a)) = c (c (β a))) (hcc : ∀ a, c (c (β a)) = c (β a) + β a)
    (x : ↥(permCore 3)) (a : ↥(permCore 5)) :
    tensorMap β c (permActCore 3 tau3 x ⊗ₜ a) = y (tensorMap β c (x ⊗ₜ a)) := by
  have hx : permActCore 3 tau3 x = coord0 x • w1 + coord2 x • (w1 + w2) := by
    conv_lhs => rw [decomp3' x]
    rw [permActCore_add, permActCore_smul, permActCore_smul, tau3_w1, tau3_w2]
  simp only [hx, TensorProduct.add_tmul, map_add, tensorMap_smul_tmul, tensorMap_w1,
    tensorMap_w2]
  rw [tensorMap_tmul, map_add, map_smul, map_smul, hyβ, hyc, hcc]
  module

theorem tensorMap_comm (d : GLV V) (hdc : ∀ v, d (c v) = c (d v)) (a a' : ↥(permCore 5))
    (hda : d (β a) = β a') (x : ↥(permCore 3)) :
    d (tensorMap β c (x ⊗ₜ a)) = tensorMap β c (x ⊗ₜ a') := by
  rw [tensorMap_tmul, tensorMap_tmul, map_add, map_smul, map_smul, hdc, hda]

end Equivariance

section Bijective

variable (β : ↥(permCore 5) →ₗ[ZMod 2] V) (c : GLV V)

theorem tensorMap_bijective (B : Submodule (ZMod 2) V) (hβinj : Function.Injective β)
    (hrange : LinearMap.range β = B) (hinf : B ⊓ conjSub c B = ⊥)
    (hsup : B ⊔ conjSub c B = ⊤) : Function.Bijective (tensorMap β c) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨a₁, a₂, rfl⟩ := tensor_decomp t
    rw [map_add, tensorMap_w1, tensorMap_w2] at ht
    have h1 : β a₁ = c (β a₂) :=
      (eq_neg_of_add_eq_zero_left ht).trans
        (neg_eq_of_add_eq_zero_left (add_self_eq_zero'' (c (β a₂))))
    have hmem : β a₁ ∈ B ⊓ conjSub c B := by
      refine Submodule.mem_inf.2 ⟨?_, ?_⟩
      · rw [← hrange]
        exact LinearMap.mem_range_self β a₁
      · rw [h1]
        refine apply_mem_conjSub ?_
        rw [← hrange]
        exact LinearMap.mem_range_self β a₂
    rw [hinf, Submodule.mem_bot] at hmem
    have ha₁ : a₁ = 0 := hβinj (by rw [hmem, map_zero])
    have ha₂ : a₂ = 0 := by
      apply hβinj
      rw [map_zero]
      apply c.injective
      rw [← h1, hmem, map_zero]
    rw [ha₁, ha₂]
    simp
  · intro v
    have hv : v ∈ B ⊔ conjSub c B := hsup ▸ Submodule.mem_top
    obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hv
    obtain ⟨u, hu, rfl⟩ := hz
    rw [← hrange] at hy hu
    obtain ⟨a₁, rfl⟩ := LinearMap.mem_range.1 hy
    obtain ⟨a₂, rfl⟩ := LinearMap.mem_range.1 hu
    exact ⟨w1 ⊗ₜ a₁ + w2 ⊗ₜ a₂, by rw [map_add, tensorMap_w1, tensorMap_w2]; rfl⟩

end Bijective

end F2Tensor

end Canon

end G11

end CFSG.Quasithin
