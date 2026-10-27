module

public import Mathlib.GroupTheory.IsPerfect

public section

namespace CFSG.Quasithin.SBd14

theorem mulAut_mem_center_iff {L : Type*} [Group L] (φ : MulAut L) (z : L) :
    φ z ∈ Subgroup.center L ↔ z ∈ Subgroup.center L := by
  simp only [Subgroup.mem_center_iff]
  constructor
  · intro h y
    apply φ.injective
    rw [map_mul, map_mul]
    exact h (φ y)
  · intro h y
    obtain ⟨y', rfl⟩ := φ.surjective y
    rw [← map_mul, ← map_mul, h y']

theorem exists_induced_aut {L P : Type*} [Group L] [Group P] {ρ : L →* P}
    (hρ : Function.Surjective ρ) (hker : ρ.ker = Subgroup.center L) (φ : MulAut L) :
    ∃ α : MulAut P, ∀ x : L, α (ρ x) = ρ (φ x) := by
  classical
  have hs : Function.RightInverse (Function.surjInv hρ) ρ := Function.rightInverse_surjInv hρ
  have hf : ρ.ker ≤ (ρ.comp φ.toMonoidHom).ker := by
    intro z hz
    have hz' : z ∈ Subgroup.center L := hker ▸ hz
    have h1 : φ z ∈ ρ.ker := hker ▸ (mulAut_mem_center_iff φ z).2 hz'
    exact h1
  have hf' : ρ.ker ≤ (ρ.comp φ.symm.toMonoidHom).ker := by
    intro z hz
    have hz' : z ∈ Subgroup.center L := hker ▸ hz
    have h1 : φ.symm z ∈ ρ.ker := hker ▸ (mulAut_mem_center_iff φ.symm z).2 hz'
    exact h1
  let α₀ : P →* P := ρ.liftOfRightInverse (Function.surjInv hρ) hs ⟨ρ.comp φ.toMonoidHom, hf⟩
  let β₀ : P →* P :=
    ρ.liftOfRightInverse (Function.surjInv hρ) hs ⟨ρ.comp φ.symm.toMonoidHom, hf'⟩
  have hα₀ : ∀ x, α₀ (ρ x) = ρ (φ x) := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply ρ _ hs ⟨ρ.comp φ.toMonoidHom, hf⟩ x
  have hβ₀ : ∀ x, β₀ (ρ x) = ρ (φ.symm x) := fun x =>
    MonoidHom.liftOfRightInverse_comp_apply ρ _ hs ⟨ρ.comp φ.symm.toMonoidHom, hf'⟩ x
  refine ⟨{ toFun := α₀, invFun := β₀, left_inv := ?_, right_inv := ?_, map_mul' := α₀.map_mul },
    hα₀⟩
  · intro p
    obtain ⟨x, rfl⟩ := hρ p
    show β₀ (α₀ (ρ x)) = ρ x
    rw [hα₀, hβ₀]
    simp
  · intro p
    obtain ⟨x, rfl⟩ := hρ p
    show α₀ (β₀ (ρ x)) = ρ x
    rw [hβ₀, hα₀]
    simp

theorem eq_one_of_central_perfect {L : Type*} [Group L] (hL : Group.IsPerfect L) (ψ : MulAut L)
    (h : ∀ x : L, ψ x * x⁻¹ ∈ Subgroup.center L) : ψ = 1 := by
  let lam : L →* Subgroup.center L :=
    { toFun := fun x => ⟨ψ x * x⁻¹, h x⟩
      map_one' := by ext; simp
      map_mul' := fun x y => by
        ext
        have hy := Subgroup.mem_center_iff.mp (h y) x
        simp only [map_mul, Subgroup.coe_mul, mul_inv_rev]
        calc ψ x * ψ y * (y⁻¹ * x⁻¹) = ψ x * (ψ y * y⁻¹) * x⁻¹ := by group
          _ = ψ x * (x⁻¹ * (x * (ψ y * y⁻¹))) * x⁻¹ := by group
          _ = ψ x * (x⁻¹ * ((ψ y * y⁻¹) * x)) * x⁻¹ := by rw [hy.symm]
          _ = ψ x * x⁻¹ * (ψ y * y⁻¹) := by group }
  have hker : commutator L ≤ lam.ker := Abelianization.commutator_subset_ker lam
  rw [hL.commutator_eq_top] at hker
  ext x
  have hx : lam x = 1 := hker (Subgroup.mem_top x)
  have := congrArg Subtype.val hx
  simp only [lam, MonoidHom.coe_mk, OneHom.coe_mk, Subgroup.coe_one] at this
  simpa [mul_inv_eq_one] using this

theorem exists_conj_of_induced_inner {L P : Type*} [Group L] [Group P] {ρ : L →* P}
    (hρ : Function.Surjective ρ) (hker : ρ.ker = Subgroup.center L) (hL : Group.IsPerfect L)
    (φ : MulAut L) (α : MulAut P) (hα : ∀ x : L, α (ρ x) = ρ (φ x))
    (hin : α ∈ (MulAut.conj : P →* MulAut P).range) :
    ∃ x₀ : L, ∀ x : L, φ x = x₀ * x * x₀⁻¹ := by
  obtain ⟨g, hg⟩ := hin
  obtain ⟨x₀, rfl⟩ := hρ g
  refine ⟨x₀, ?_⟩
  have h1 : ∀ x : L, ρ (φ x) = ρ x₀ * ρ x * (ρ x₀)⁻¹ := fun x => by
    rw [← hα, ← hg]; simp
  let ψ : MulAut L := φ.trans (MulAut.conj x₀⁻¹)
  have hψx : ∀ x, ψ x = x₀⁻¹ * φ x * x₀ := fun x => by simp [ψ]
  have hψ : ψ = 1 := by
    apply eq_one_of_central_perfect hL
    intro x
    rw [← hker, MonoidHom.mem_ker, hψx, map_mul, map_mul, map_inv, map_mul, map_inv, h1 x]
    group
  intro x
  have := congrArg (fun e : MulAut L => e x) hψ
  simp only [hψx, MulAut.one_apply] at this
  calc φ x = x₀ * (x₀⁻¹ * φ x * x₀) * x₀⁻¹ := by group
    _ = x₀ * x * x₀⁻¹ := by rw [this]

end CFSG.Quasithin.SBd14
