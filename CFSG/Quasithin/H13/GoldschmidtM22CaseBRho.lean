module

public import CFSG.Quasithin.H13.GoldschmidtM22EndN5a

public section

namespace CFSG.Quasithin.H13.GM22

variable {G : Type} [Group G]

structure PermRho (V : Subgroup G) where
  φ : ↥(Subgroup.normalizer (V : Set G)) →* Equiv.Perm (Fin 5)
  surj : Function.Surjective φ
  ker : φ.ker = (Subgroup.centralizer (V : Set G)).subgroupOf (Subgroup.normalizer (V : Set G))

namespace PermRho

variable {V : Subgroup G} (ρ : PermRho V)

open scoped Classical in
@[expose] noncomputable def toFun (x : G) : Equiv.Perm (Fin 5) :=
  if hx : x ∈ Subgroup.normalizer (V : Set G) then ρ.φ ⟨x, hx⟩ else 1

noncomputable instance : CoeFun (PermRho V) fun _ => G → Equiv.Perm (Fin 5) := ⟨toFun⟩

variable {ρ} {x y : G}

theorem apply_of_mem (hx : x ∈ Subgroup.normalizer (V : Set G)) : ρ x = ρ.φ ⟨x, hx⟩ := by
  simp only [toFun, hx, ↓reduceDIte]

theorem apply_mul (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hy : y ∈ Subgroup.normalizer (V : Set G)) : ρ (x * y) = ρ x * ρ y := by
  rw [apply_of_mem ((Subgroup.normalizer (V : Set G)).mul_mem hx hy), apply_of_mem hx,
    apply_of_mem hy, ← _root_.map_mul]
  rfl

theorem apply_one : ρ 1 = 1 := by
  rw [apply_of_mem (Subgroup.normalizer (V : Set G)).one_mem]
  exact ρ.φ.map_one

theorem apply_inv (hx : x ∈ Subgroup.normalizer (V : Set G)) : ρ x⁻¹ = (ρ x)⁻¹ := by
  rw [apply_of_mem ((Subgroup.normalizer (V : Set G)).inv_mem hx), apply_of_mem hx,
    ← _root_.map_inv]
  rfl

theorem apply_pow (hx : x ∈ Subgroup.normalizer (V : Set G)) (n : ℕ) : ρ (x ^ n) = ρ x ^ n := by
  rw [apply_of_mem ((Subgroup.normalizer (V : Set G)).pow_mem hx n), apply_of_mem hx,
    ← _root_.map_pow]
  rfl

theorem apply_conj (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hy : y ∈ Subgroup.normalizer (V : Set G)) : ρ (x * y * x⁻¹) = ρ x * ρ y * (ρ x)⁻¹ := by
  rw [apply_mul ((Subgroup.normalizer (V : Set G)).mul_mem hx hy)
    ((Subgroup.normalizer (V : Set G)).inv_mem hx), apply_mul hx hy, apply_inv hx]

theorem eq_one_iff (hx : x ∈ Subgroup.normalizer (V : Set G)) :
    ρ x = 1 ↔ x ∈ Subgroup.centralizer (V : Set G) := by
  have h1 : (⟨x, hx⟩ : ↥(Subgroup.normalizer (V : Set G))) ∈ ρ.φ.ker ↔
      x ∈ Subgroup.centralizer (V : Set G) := by
    rw [ρ.ker, Subgroup.mem_subgroupOf]
  rw [← h1, MonoidHom.mem_ker, apply_of_mem hx]

theorem eq_iff (hx : x ∈ Subgroup.normalizer (V : Set G))
    (hy : y ∈ Subgroup.normalizer (V : Set G)) :
    ρ x = ρ y ↔ x⁻¹ * y ∈ Subgroup.centralizer (V : Set G) := by
  rw [← eq_one_iff (mul_mem ((Subgroup.normalizer (V : Set G)).inv_mem hx) hy),
    apply_mul ((Subgroup.normalizer (V : Set G)).inv_mem hx) hy, apply_inv hx, inv_mul_eq_one]

theorem exists_eq (ρ : PermRho V) (σ : Equiv.Perm (Fin 5)) :
    ∃ x ∈ Subgroup.normalizer (V : Set G), ρ x = σ := by
  obtain ⟨x, rfl⟩ := ρ.surj σ
  exact ⟨x, x.2, apply_of_mem x.2⟩

end PermRho

omit [Group G] in
theorem nonempty_permRho [Group G] {T L V : Subgroup G}
    (hNeq : Subgroup.normalizer (V : Set G) = L ⊔ T)
    (e : ↥(CFSG.Quasithin.autOn (L ⊔ T) V) ≃* Equiv.Perm (Fin 5)) : Nonempty (PermRho V) := by
  obtain ⟨φ, hs, hk⟩ := exists_hom_perm5 hNeq e
  exact ⟨⟨φ, hs, hk⟩⟩

end CFSG.Quasithin.H13.GM22
