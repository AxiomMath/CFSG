module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.Certificates.ExtraspecialNormalForm

public section

namespace CFSG.Sporadic.Co2Smith

open CFSG.Certificates.ExtraspecialNF

section NF

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂] {n : ℕ} {z₁ : G₁} {q₁ : Fin n → G₁} {z₂ : G₂}
  {q₂ : Fin n → G₂} {cc : Fin n → Fin n → ZMod 2}

theorem ofBijective_symm_nf (hb : Function.Bijective (Function.uncurry (nf z₁ q₁)))
    (s : ZMod 2) (v : Fin n → ZMod 2) :
    (Equiv.ofBijective _ hb).symm (nf z₁ q₁ s v) = (s, v) :=
  (Equiv.ofBijective _ hb).symm_apply_apply (s, v)

@[expose] noncomputable def nfEquiv (h₁ : Rel z₁ q₁ cc) (h₂ : Rel z₂ q₂ cc)
    (hb₁ : Function.Bijective (Function.uncurry (nf z₁ q₁)))
    (hb₂ : Function.Bijective (Function.uncurry (nf z₂ q₂))) : G₁ ≃* G₂ :=
  MulEquiv.mk ((Equiv.ofBijective _ hb₁).symm.trans (Equiv.ofBijective _ hb₂)) (by
    intro x y
    obtain ⟨⟨s, v⟩, rfl⟩ := hb₁.2 x
    obtain ⟨⟨t, w⟩, rfl⟩ := hb₁.2 y
    show (Equiv.ofBijective _ hb₂) ((Equiv.ofBijective _ hb₁).symm (nf z₁ q₁ s v * nf z₁ q₁ t w)) =
      (Equiv.ofBijective _ hb₂) ((Equiv.ofBijective _ hb₁).symm (nf z₁ q₁ s v)) *
        (Equiv.ofBijective _ hb₂) ((Equiv.ofBijective _ hb₁).symm (nf z₁ q₁ t w))
    rw [nf_mul_nf h₁, ofBijective_symm_nf, ofBijective_symm_nf, ofBijective_symm_nf]
    show nf z₂ q₂ _ _ = nf z₂ q₂ s v * nf z₂ q₂ t w
    rw [nf_mul_nf h₂])

theorem nfEquiv_nf (h₁ : Rel z₁ q₁ cc) (h₂ : Rel z₂ q₂ cc)
    (hb₁ : Function.Bijective (Function.uncurry (nf z₁ q₁)))
    (hb₂ : Function.Bijective (Function.uncurry (nf z₂ q₂))) (s : ZMod 2) (v : Fin n → ZMod 2) :
    nfEquiv h₁ h₂ hb₁ hb₂ (nf z₁ q₁ s v) = nf z₂ q₂ s v := by
  show (Equiv.ofBijective _ hb₂) ((Equiv.ofBijective _ hb₁).symm (nf z₁ q₁ s v)) = _
  rw [ofBijective_symm_nf]
  rfl

theorem closure_eq_top_of_surj (hb : Function.Surjective (Function.uncurry (nf z₁ q₁))) :
    Subgroup.closure (insert z₁ (Set.range q₁)) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨⟨s, v⟩, rfl⟩ := hb x
  exact nf_mem_closure z₁ q₁ s v

end NF

section Defect

variable {G₁ G₂ : Type*} [Group G₁] [Group G₂]

@[expose] def defect (φ ψ : G₁ →* G₂) (x : G₁) : G₂ := (φ x)⁻¹ * ψ x

theorem defect_mul_of_central (φ ψ : G₁ →* G₂) {x : G₁} (hx : defect φ ψ x ∈ Subgroup.center G₂)
    (y : G₁) : defect φ ψ (x * y) = defect φ ψ x * defect φ ψ y := by
  have hc : ∀ g, g * ((φ x)⁻¹ * ψ x) = ((φ x)⁻¹ * ψ x) * g := Subgroup.mem_center_iff.mp hx
  simp only [defect, map_mul, mul_inv_rev]
  calc (φ y)⁻¹ * (φ x)⁻¹ * (ψ x * ψ y) = (φ y)⁻¹ * ((φ x)⁻¹ * ψ x) * ψ y := by group
    _ = ((φ x)⁻¹ * ψ x) * (φ y)⁻¹ * ψ y := by rw [hc (φ y)⁻¹]
    _ = (φ x)⁻¹ * ψ x * ((φ y)⁻¹ * ψ y) := by group

theorem defect_central (φ ψ : G₁ →* G₂) {S : Set G₁} (hS : Subgroup.closure S = ⊤)
    (h : ∀ s ∈ S, defect φ ψ s ∈ Subgroup.center G₂) (x : G₁) :
    defect φ ψ x ∈ Subgroup.center G₂ := by
  have hx : x ∈ Subgroup.closure S := hS ▸ Subgroup.mem_top x
  induction hx using Subgroup.closure_induction with
  | mem s hs => exact h s hs
  | one =>
    rw [defect, map_one, map_one, inv_one, one_mul]
    exact Subgroup.one_mem _
  | mul x y _ _ hx hy =>
    rw [defect_mul_of_central φ ψ hx]
    exact Subgroup.mul_mem _ hx hy
  | inv x _ hx =>
    have hψ : ψ x = φ x * defect φ ψ x := by rw [defect, mul_inv_cancel_left]
    have hc := Subgroup.mem_center_iff.mp (Subgroup.inv_mem _ hx)
    have e : defect φ ψ x⁻¹ = (defect φ ψ x)⁻¹ := by
      rw [defect, map_inv, map_inv, inv_inv, hψ, mul_inv_rev, ← mul_assoc, hc (φ x), mul_assoc,
        mul_inv_cancel, mul_one]
    rw [e]
    exact Subgroup.inv_mem _ hx

theorem defect_mul (φ ψ : G₁ →* G₂) {S : Set G₁} (hS : Subgroup.closure S = ⊤)
    (h : ∀ s ∈ S, defect φ ψ s ∈ Subgroup.center G₂) (x y : G₁) :
    defect φ ψ (x * y) = defect φ ψ x * defect φ ψ y :=
  defect_mul_of_central φ ψ (defect_central φ ψ hS h x) y

theorem eq_of_defect (φ ψ : G₁ →* G₂) (h : ∀ x, defect φ ψ x = 1) : φ = ψ := by
  ext x
  have := h x
  rw [defect, inv_mul_eq_one] at this
  exact this

end Defect

end CFSG.Sporadic.Co2Smith
