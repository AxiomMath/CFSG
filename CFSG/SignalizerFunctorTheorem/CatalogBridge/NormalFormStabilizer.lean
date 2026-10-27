module

public import CFSG.Assembly.LowTwoRankDefs
public import CFSG.SignalizerFunctorTheorem.Nonsolvable.ASimple.Factors

public section

namespace CFSG.SignalizerFunctorTheorem.CatalogBridge

theorem mulAut_mul_conj_mul_inv' {Γ : Type*} [Group Γ] (s : MulAut Γ) (y : Γ) :
    s * MulAut.conj y * s⁻¹ = MulAut.conj (s y) :=
  MulEquiv.ext fun u => by
    simp only [MulAut.mul_apply, MulAut.conj_apply, map_mul, map_inv, MulAut.apply_inv_self]

theorem mem_zpowers_of_fixes_of_normalForm {Γ A : Type*} [Group Γ] [Group A]
    (hA : ∀ u v : A, u * v = v * u) (φ : A →* MulAut Γ)
    (hNF : ∀ α : MulAut Γ, ∃ (x : Γ) (τ : A), α = MulAut.conj x * φ τ)
    (σ : A) (N : Subgroup Γ) (hN : ∀ t, φ σ t = t ↔ t ∈ N)
    (hC : Subgroup.centralizer (N : Set Γ) = ⊥)
    (hres : ∀ (x : Γ) (τ : A), x ∈ N → (∀ j ∈ N, x * φ τ j * x⁻¹ = j) → τ ∈ Subgroup.zpowers σ)
    {g : MulAut Γ} (hg : ∀ j ∈ N, g j = j) : g ∈ Subgroup.zpowers (φ σ) := by
  obtain ⟨x, τ, rfl⟩ := hNF g
  have hmem : ∀ h : MulAut Γ, h ∈ fixingSubgroup (MulAut Γ) (N : Set Γ) ↔ ∀ j ∈ N, h j = j :=
    fun h => mem_fixingSubgroup_iff _
  have hσP : φ σ ∈ fixingSubgroup (MulAut Γ) (N : Set Γ) :=
    (hmem _).2 fun j hj => (hN j).2 hj
  have hgP : MulAut.conj x * φ τ ∈ fixingSubgroup (MulAut Γ) (N : Set Γ) := (hmem _).2 hg
  have hconjP : ∀ y : Γ, MulAut.conj y ∈ fixingSubgroup (MulAut Γ) (N : Set Γ) → y = 1 := by
    intro y hy
    have hy' := (hmem _).1 hy
    have hyC : y ∈ Subgroup.centralizer (N : Set Γ) := by
      rw [Subgroup.mem_centralizer_iff]
      intro j hj
      have := hy' j hj
      rw [MulAut.conj_apply] at this
      calc j * y = y * j * y⁻¹ * y := by rw [this]
        _ = y * j := by group
    rw [hC, Subgroup.mem_bot] at hyC
    exact hyC
  have hts : φ τ * φ σ = φ σ * φ τ := by rw [← map_mul, ← map_mul, hA]
  have hcomm : (MulAut.conj x * φ τ) * φ σ * (MulAut.conj x * φ τ)⁻¹ * (φ σ)⁻¹ =
      MulAut.conj (x * (φ σ x)⁻¹) := by
    have h1 : φ τ * φ σ * (φ τ)⁻¹ = φ σ := mul_inv_eq_iff_eq_mul.2 hts
    have h2 : (MulAut.conj x * φ τ) * φ σ * (MulAut.conj x * φ τ)⁻¹ * (φ σ)⁻¹ =
        MulAut.conj x * (φ τ * φ σ * (φ τ)⁻¹) * (MulAut.conj x)⁻¹ * (φ σ)⁻¹ := by
      simp only [mul_inv_rev, mul_assoc]
    rw [h2, h1]
    have h3 : φ σ * (MulAut.conj x)⁻¹ * (φ σ)⁻¹ = (MulAut.conj (φ σ x))⁻¹ := by
      rw [← mulAut_mul_conj_mul_inv' (φ σ) x]
      group
    rw [show MulAut.conj x * φ σ * (MulAut.conj x)⁻¹ * (φ σ)⁻¹ =
      MulAut.conj x * (φ σ * (MulAut.conj x)⁻¹ * (φ σ)⁻¹) by simp only [mul_assoc], h3,
      ← map_inv, ← map_mul]
  have hcommP : MulAut.conj (x * (φ σ x)⁻¹) ∈ fixingSubgroup (MulAut Γ) (N : Set Γ) := by
    rw [← hcomm]
    exact mul_mem (mul_mem (mul_mem hgP hσP) (inv_mem hgP)) (inv_mem hσP)
  have hz : x * (φ σ x)⁻¹ = 1 := hconjP _ hcommP
  have hxσ : φ σ x = x := by
    have : x = φ σ x := mul_inv_eq_one.1 hz
    exact this.symm
  have hxN : x ∈ N := (hN x).1 hxσ
  have hτ : τ ∈ Subgroup.zpowers σ := hres x τ hxN fun j hj => by
    have := hg j hj
    rwa [MulAut.mul_apply, MulAut.conj_apply] at this
  have hτP : φ τ ∈ fixingSubgroup (MulAut Γ) (N : Set Γ) := by
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hτ
    rw [map_zpow]
    exact zpow_mem hσP n
  have hxP : MulAut.conj x ∈ fixingSubgroup (MulAut Γ) (N : Set Γ) := by
    have := mul_mem hgP (inv_mem hτP)
    rwa [mul_inv_cancel_right] at this
  have hx1 : x = 1 := hconjP x hxP
  subst hx1
  rw [map_one, one_mul]
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hτ
  rw [map_zpow]
  exact Subgroup.zpow_mem_zpowers _ n

end CFSG.SignalizerFunctorTheorem.CatalogBridge
