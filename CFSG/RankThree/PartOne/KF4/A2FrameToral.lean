module

public import CFSG.RankThree.PartOne.KF4.A2Frame
import CFSG.HardMathSupport.Malle.Coordinator.CoverThree.SL3Closure

public section

namespace CFSG.RankThree.PartOne.KF4

open Matrix CFSG.Blueprint CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
open scoped MatrixGroups

theorem exists_conj_diag_prod {F : Type} [Field F] (P : Subgroup (SL(3, F) × SL(3, F)))
    {m : ℕ} [NeZero m] {ζ : F} (hζ : IsPrimitiveRoot ζ m)
    (hcomm : ∀ x ∈ P, ∀ y ∈ P, x * y = y * x) (hexp : ∀ x ∈ P, x ^ m = 1) :
    ∃ γ : SL(3, F) × SL(3, F), ∀ x ∈ P, ∀ i j : Fin 3, i ≠ j →
      ((γ * x * γ⁻¹).1 : Matrix (Fin 3) (Fin 3) F) i j = 0 ∧
        ((γ * x * γ⁻¹).2 : Matrix (Fin 3) (Fin 3) F) i j = 0 := by
  have hc1 : ∀ x ∈ P.map (MonoidHom.fst _ _), ∀ y ∈ P.map (MonoidHom.fst _ _), x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simpa using congrArg Prod.fst (hcomm x hx y hy)
  have hc2 : ∀ x ∈ P.map (MonoidHom.snd _ _), ∀ y ∈ P.map (MonoidHom.snd _ _), x * y = y * x := by
    rintro _ ⟨x, hx, rfl⟩ _ ⟨y, hy, rfl⟩
    simpa using congrArg Prod.snd (hcomm x hx y hy)
  have he1 : ∀ x ∈ P.map (MonoidHom.fst _ _), x ^ m = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using congrArg Prod.fst (hexp x hx)
  have he2 : ∀ x ∈ P.map (MonoidHom.snd _ _), x ^ m = 1 := by
    rintro _ ⟨x, hx, rfl⟩
    simpa using congrArg Prod.snd (hexp x hx)
  obtain ⟨γ₁, hγ₁⟩ :=
    CFSG.HardMathSupport.Malle.Coordinator.CoverThree.exists_sl_conj_diag _ hζ hc1 he1
  obtain ⟨γ₂, hγ₂⟩ :=
    CFSG.HardMathSupport.Malle.Coordinator.CoverThree.exists_sl_conj_diag _ hζ hc2 he2
  refine ⟨(γ₁, γ₂), fun x hx i j hij => ⟨?_, ?_⟩⟩
  · exact hγ₁ x.1 ⟨x, hx, rfl⟩ i j hij
  · exact hγ₂ x.2 ⟨x, hx, rfl⟩ i j hij

variable {τ : Tag} {L : Type} [Field L]

namespace IsA2Frame

variable {ψ ψ' : SL(3, L) →* ModGL τ L} {σ σ' : Fin 3 → Fin 3 → Fin τ.rank → ℤ}

private theorem ker_le_center_of_injective {G H : Type*} [Group G] [Group H] {f g : G →* H}
    (hf : Function.Injective f) (hg : Function.Injective g) (hc : ∀ a b, Commute (f a) (g b)) :
    (f.noncommCoprod g hc).ker ≤ Subgroup.center (G × G) := by
  rintro ⟨a, b⟩ hab
  rw [MonoidHom.mem_ker, MonoidHom.noncommCoprod_apply] at hab
  have hfa : f a = g b⁻¹ := by rw [map_inv]; exact eq_inv_of_mul_eq_one_left hab
  have hgb : g b = f a⁻¹ := by rw [map_inv]; exact eq_inv_of_mul_eq_one_right hab
  rw [Subgroup.mem_center_iff]
  rintro ⟨c, d⟩
  refine Prod.ext (hf ?_) (hg ?_)
  · show f (c * a) = f (a * c)
    rw [map_mul, map_mul, hfa]
    exact (hc c b⁻¹).eq
  · show g (d * b) = g (b * d)
    rw [map_mul, map_mul, hgb]
    exact (hc a⁻¹ d).eq.symm

theorem ker_noncommCoprod_le_center (hψ : IsA2Frame ψ σ) (hψ' : IsA2Frame ψ' σ')
    (hc : ∀ A B, Commute (ψ A) (ψ' B)) :
    (ψ.noncommCoprod ψ' hc).ker ≤ Subgroup.center (SL(3, L) × SL(3, L)) :=
  ker_le_center_of_injective hψ.injective hψ'.injective hc

private theorem pow_three_eq_one_of_mem_center {A : SL(3, L)}
    (hA : A ∈ Subgroup.center (SL(3, L))) : A ^ 3 = 1 := by
  obtain ⟨r, hr, hrA⟩ := Matrix.SpecialLinearGroup.mem_center_iff.mp hA
  rw [Fintype.card_fin] at hr
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_pow, ← hrA, Matrix.SpecialLinearGroup.coe_one,
    ← map_pow, hr, map_one]

theorem exists_conj_torus_of_comm_preimage (hψ : IsA2Frame ψ σ) (hψ' : IsA2Frame ψ' σ')
    (hc : ∀ A B, Commute (ψ A) (ψ' B)) {ζ : L} (hζ : IsPrimitiveRoot ζ 9)
    {E : Subgroup (ModGL τ L)} (hE3 : ∀ x ∈ E, x ^ 3 = 1)
    (hEμ : E ≤ (ψ.noncommCoprod ψ' hc).range)
    (hcomm : ∀ u ∈ E.comap (ψ.noncommCoprod ψ' hc), ∀ v ∈ E.comap (ψ.noncommCoprod ψ' hc),
      u * v = v * u) :
    ∃ g ∈ (ψ.noncommCoprod ψ' hc).range, ∀ x ∈ E, g⁻¹ * x * g ∈ torusGroup τ L := by
  set μ := ψ.noncommCoprod ψ' hc with hμ
  have hexp : ∀ u ∈ E.comap μ, u ^ 9 = 1 := by
    intro u hu
    have hker : u ^ 3 ∈ μ.ker := by
      rw [MonoidHom.mem_ker, map_pow]
      exact hE3 _ hu
    have hcen := ker_noncommCoprod_le_center hψ hψ' hc hker
    have hc1 : (u ^ 3).1 ∈ Subgroup.center (SL(3, L)) := Subgroup.mem_center_iff.mpr fun c => by
      simpa using congrArg Prod.fst (Subgroup.mem_center_iff.mp hcen (c, 1))
    have hc2 : (u ^ 3).2 ∈ Subgroup.center (SL(3, L)) := Subgroup.mem_center_iff.mpr fun c => by
      simpa using congrArg Prod.snd (Subgroup.mem_center_iff.mp hcen (1, c))
    have h9 : u ^ 9 = (u ^ 3) ^ 3 := by rw [← pow_mul]
    rw [h9]
    exact Prod.ext (by rw [Prod.pow_fst, pow_three_eq_one_of_mem_center hc1]; rfl)
      (by rw [Prod.pow_snd, pow_three_eq_one_of_mem_center hc2]; rfl)
  obtain ⟨γ, hγ⟩ := exists_conj_diag_prod (E.comap μ) hζ hcomm hexp
  refine ⟨(μ γ)⁻¹, Subgroup.inv_mem _ ⟨γ, rfl⟩, fun x hx => ?_⟩
  obtain ⟨u, rfl⟩ := hEμ hx
  have hu : u ∈ E.comap μ := hx
  have hconj : (μ γ)⁻¹⁻¹ * μ u * (μ γ)⁻¹ = μ (γ * u * γ⁻¹) := by simp [map_mul, map_inv]
  rw [hconj, hμ, MonoidHom.noncommCoprod_apply]
  exact Subgroup.mul_mem _ (hψ.diag _ fun i j hij => (hγ u hu i j hij).1)
    (hψ'.diag _ fun i j hij => (hγ u hu i j hij).2)

end IsA2Frame

end CFSG.RankThree.PartOne.KF4
