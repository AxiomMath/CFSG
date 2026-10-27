module

public import CFSG.Quasithin.Background.G118CanonNineF2TensorBuild

public section

attribute [-instance] instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent
  instCommGroupOfIsSimpleGroupOfIsNilpotent

namespace CFSG.Quasithin

namespace G11

namespace Canon

namespace F4Tensor

open scoped TensorProduct

open F2Tensor

variable {V W : Type} [AddCommGroup V] [Module (ZMod 2) V] [AddCommGroup W] [Module (ZMod 2) W]

theorem tensor_decompW (t : ↥(permCore 3) ⊗[ZMod 2] W) :
    ∃ a₁ a₂ : W, t = w1 ⊗ₜ a₁ + w2 ⊗ₜ a₂ := by
  induction t using TensorProduct.induction_on with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul x a =>
    refine ⟨coord0 x • a, coord2 x • a, ?_⟩
    conv_lhs => rw [decomp3' x]
    rw [TensorProduct.add_tmul, TensorProduct.smul_tmul, TensorProduct.smul_tmul]
  | add x y hx hy =>
    obtain ⟨a₁, a₂, rfl⟩ := hx
    obtain ⟨a₁', a₂', rfl⟩ := hy
    exact ⟨a₁ + a₁', a₂ + a₂', by rw [TensorProduct.tmul_add, TensorProduct.tmul_add]; abel⟩

@[expose] noncomputable def tensorMapW (β : W →ₗ[ZMod 2] V) (c : GLV V) :
    (↥(permCore 3) ⊗[ZMod 2] W) →ₗ[ZMod 2] V :=
  TensorProduct.lift (coord0.smulRight β + coord2.smulRight ((c : V →ₗ[ZMod 2] V) ∘ₗ β))

theorem tensorMapW_tmul (β : W →ₗ[ZMod 2] V) (c : GLV V) (x : ↥(permCore 3)) (a : W) :
    tensorMapW β c (x ⊗ₜ a) = coord0 x • β a + coord2 x • c (β a) := by
  simp [tensorMapW, TensorProduct.lift.tmul]

theorem tensorMapW_w1 (β : W →ₗ[ZMod 2] V) (c : GLV V) (a : W) :
    tensorMapW β c (w1 ⊗ₜ a) = β a := by
  rw [tensorMapW_tmul, coord0_w1, coord2_w1, one_smul, zero_smul, add_zero]

theorem tensorMapW_w2 (β : W →ₗ[ZMod 2] V) (c : GLV V) (a : W) :
    tensorMapW β c (w2 ⊗ₜ a) = c (β a) := by
  rw [tensorMapW_tmul, coord0_w2, coord2_w2, one_smul, zero_smul, zero_add]

section Equivariance

variable (β : W →ₗ[ZMod 2] V) (c : GLV V)

theorem tensorMapW_smul_tmul (u : ZMod 2) (x : ↥(permCore 3)) (a : W) :
    tensorMapW β c ((u • x) ⊗ₜ a) = u • tensorMapW β c (x ⊗ₜ a) := by
  rw [← TensorProduct.smul_tmul', map_smul]

theorem tensorMapW_rho (hcc : ∀ a, c (c (β a)) = c (β a) + β a) (x : ↥(permCore 3)) (a : W) :
    tensorMapW β c (permActCore 3 rho3 x ⊗ₜ a) = c (tensorMapW β c (x ⊗ₜ a)) := by
  have hx : permActCore 3 rho3 x = coord0 x • w2 + coord2 x • (w1 + w2) := by
    conv_lhs => rw [decomp3' x]
    rw [permActCore_add, permActCore_smul, permActCore_smul, rho3_w1, rho3_w2]
  simp only [hx, TensorProduct.add_tmul, map_add, tensorMapW_smul_tmul, tensorMapW_w1,
    tensorMapW_w2]
  rw [tensorMapW_tmul, map_add, map_smul, map_smul, hcc]
  module

theorem tensorMapW_tau (y : GLV V) (hyβ : ∀ a, y (β a) = β a)
    (hyc : ∀ a, y (c (β a)) = c (c (β a))) (hcc : ∀ a, c (c (β a)) = c (β a) + β a)
    (x : ↥(permCore 3)) (a : W) :
    tensorMapW β c (permActCore 3 tau3 x ⊗ₜ a) = y (tensorMapW β c (x ⊗ₜ a)) := by
  have hx : permActCore 3 tau3 x = coord0 x • w1 + coord2 x • (w1 + w2) := by
    conv_lhs => rw [decomp3' x]
    rw [permActCore_add, permActCore_smul, permActCore_smul, tau3_w1, tau3_w2]
  simp only [hx, TensorProduct.add_tmul, map_add, tensorMapW_smul_tmul, tensorMapW_w1,
    tensorMapW_w2]
  rw [tensorMapW_tmul, map_add, map_smul, map_smul, hyβ, hyc, hcc]
  module

theorem tensorMapW_comm (d : GLV V) (hdc : ∀ v, d (c v) = c (d v)) (a a' : W)
    (hda : d (β a) = β a') (x : ↥(permCore 3)) :
    d (tensorMapW β c (x ⊗ₜ a)) = tensorMapW β c (x ⊗ₜ a') := by
  rw [tensorMapW_tmul, tensorMapW_tmul, map_add, map_smul, map_smul, hdc, hda]

theorem tensorMapW_perm (s : Equiv.Perm (Fin 3) →* GLV V) (hρ : s rho3 = c)
    (hyβ : ∀ a, s tau3 (β a) = β a) (hyc : ∀ a, s tau3 (c (β a)) = c (c (β a)))
    (hcc : ∀ a, c (c (β a)) = c (β a) + β a) (π : Equiv.Perm (Fin 3)) (x : ↥(permCore 3))
    (a : W) :
    tensorMapW β c (permActCore 3 π x ⊗ₜ a) = s π (tensorMapW β c (x ⊗ₜ a)) := by
  have hmul : ∀ π₁ π₂ : Equiv.Perm (Fin 3),
      (∀ (x : ↥(permCore 3)) (a : W), tensorMapW β c (permActCore 3 π₁ x ⊗ₜ a) =
        s π₁ (tensorMapW β c (x ⊗ₜ a))) →
      (∀ (x : ↥(permCore 3)) (a : W), tensorMapW β c (permActCore 3 π₂ x ⊗ₜ a) =
        s π₂ (tensorMapW β c (x ⊗ₜ a))) →
      (∀ (x : ↥(permCore 3)) (a : W),
        tensorMapW β c (permActCore 3 (π₁ * π₂) x ⊗ₜ a) =
        s (π₁ * π₂) (tensorMapW β c (x ⊗ₜ a))) := by
    intro π₁ π₂ h₁ h₂ x a
    rw [permActCore_mul, h₁, h₂, map_mul]
    rfl
  have h1 : ∀ (x : ↥(permCore 3)) (a : W),
      tensorMapW β c (permActCore 3 1 x ⊗ₜ a) = s 1 (tensorMapW β c (x ⊗ₜ a)) := by
    intro x a
    rw [permActCore_one, map_one]
    rfl
  have hρ' : ∀ (x : ↥(permCore 3)) (a : W),
      tensorMapW β c (permActCore 3 rho3 x ⊗ₜ a) = s rho3 (tensorMapW β c (x ⊗ₜ a)) := by
    intro x a
    rw [hρ]
    exact tensorMapW_rho β c hcc x a
  have hτ' : ∀ (x : ↥(permCore 3)) (a : W),
      tensorMapW β c (permActCore 3 tau3 x ⊗ₜ a) = s tau3 (tensorMapW β c (x ⊗ₜ a)) :=
    fun x a => tensorMapW_tau β c (s tau3) hyβ hyc hcc x a
  revert x a
  rcases perm3_cases π with rfl | rfl | rfl | rfl | rfl | rfl
  · exact h1
  · exact hρ'
  · exact hmul _ _ hρ' hρ'
  · exact hτ'
  · exact hmul _ _ hτ' hρ'
  · exact hmul _ _ (hmul _ _ hτ' hρ') hρ'

end Equivariance

section Bijective

variable (β : W →ₗ[ZMod 2] V) (c : GLV V)

theorem tensorMapW_bijective (B : Submodule (ZMod 2) V) (hβinj : Function.Injective β)
    (hrange : LinearMap.range β = B) (hinf : B ⊓ conjSub c B = ⊥)
    (hsup : B ⊔ conjSub c B = ⊤) : Function.Bijective (tensorMapW β c) := by
  constructor
  · rw [injective_iff_map_eq_zero]
    intro t ht
    obtain ⟨a₁, a₂, rfl⟩ := tensor_decompW t
    rw [map_add, tensorMapW_w1, tensorMapW_w2] at ht
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
    exact ⟨w1 ⊗ₜ a₁ + w2 ⊗ₜ a₂, by rw [map_add, tensorMapW_w1, tensorMapW_w2]; rfl⟩

end Bijective

end F4Tensor

end Canon

end G11

end CFSG.Quasithin
