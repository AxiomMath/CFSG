module

public import CFSG.RankThree.PartOne.NF7J.Model4

public section

namespace CFSG.RankThree.PartOne.NF7J

open Matrix CFSG CFSG.RankThree.PartOne CFSG.Assembly.LowTwoRank CFSG.LieType.SteinbergBR.AutGL32

section NormSec

variable {G : Type} [Group G] [Finite G] {p : ℕ} {c : G} {L E : Subgroup G} {f : ℕ} {K : Type}
  [Field K] [Finite K] [CharP K 2] (F : RFrame G p c L E f K) (D : Datum p E)
  (X : EFacts G p c E)

@[expose] def Datum.withE (φ : GL (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2)) : Datum p E :=
  { D with e := D.e.trans φ }

include X in
theorem exists_norm_aut :
    ∃ φ : GL (Fin 3) (ZMod 2) ≃* GL (Fin 3) (ZMod 2), Norm F (D.withE φ) := by
  set u₁ := D.e ⟨D.ν * F.r₀, a₁_mem F D⟩ with hu₁
  set u₂ := D.e ⟨D.ν * F.r₁, a₂_mem F D⟩ with hu₂
  have hu₁sq : u₁ * u₁ = 1 := by
    rw [hu₁, ← map_mul]
    have : (⟨D.ν * F.r₀, a₁_mem F D⟩ : ↥D.H) * ⟨D.ν * F.r₀, a₁_mem F D⟩ = 1 :=
      Subtype.ext (a₁_sq F D)
    rw [this, map_one]
  have hu₂sq : u₂ * u₂ = 1 := by
    rw [hu₂, ← map_mul]
    have : (⟨D.ν * F.r₁, a₂_mem F D⟩ : ↥D.H) * ⟨D.ν * F.r₁, a₂_mem F D⟩ = 1 :=
      Subtype.ext (a₂_sq F D)
    rw [this, map_one]
  have hu₁ne : u₁ ≠ 1 := by
    intro h
    apply a₁_ne_one F D X
    have : (⟨D.ν * F.r₀, a₁_mem F D⟩ : ↥D.H) = 1 := D.e.injective (h.trans (map_one D.e).symm)
    exact congrArg Subtype.val this
  have hu₂ne : u₂ ≠ 1 := by
    intro h
    have h' : (⟨D.ν * F.r₁, a₂_mem F D⟩ : ↥D.H) = 1 := D.e.injective (h.trans (map_one D.e).symm)
    exact a₂_ne_one F D X (congrArg Subtype.val h')
  have hρ : (⟨F.r₀ * F.r₁, rho_mem F D⟩ : ↥D.H) =
      ⟨D.ν * F.r₀, a₁_mem F D⟩ * ⟨D.ν * F.r₁, a₂_mem F D⟩ :=
    Subtype.ext (D.νmul_νmul F.r₀ F.r₁).symm
  have hw : IsOrd4 ((u₁ * u₂ : GL (Fin 3) (ZMod 2)) : M32) := by
    rw [isOrd4_iff]
    have e1 : u₁ * u₂ = D.e ⟨F.r₀ * F.r₁, rho_mem F D⟩ := by rw [hρ, map_mul]
    rw [e1]
    refine ⟨?_, ?_⟩
    · rw [← map_pow, map_eq_one_iff _ D.e.injective]
      apply Subtype.ext
      simpa using rho_pow_four F
    · intro h
      apply rho_sq_ne F
      have : (⟨F.r₀ * F.r₁, rho_mem F D⟩ : ↥D.H) * ⟨F.r₀ * F.r₁, rho_mem F D⟩ = 1 :=
        D.e.injective (by rw [map_mul, h, map_one])
      exact congrArg Subtype.val this
  have hA2 : ((u₁ : GL (Fin 3) (ZMod 2)) : M32) * (u₁ : M32) = 1 := by
    rw [← Units.val_mul, hu₁sq]
    rfl
  have hB2 : ((u₂ : GL (Fin 3) (ZMod 2)) : M32) * (u₂ : M32) = 1 := by
    rw [← Units.val_mul, hu₂sq]
    rfl
  have hA1 : ((u₁ : GL (Fin 3) (ZMod 2)) : M32) ≠ 1 := fun h => hu₁ne (Units.ext h)
  have hB1 : ((u₂ : GL (Fin 3) (ZMod 2)) : M32) ≠ 1 := fun h => hu₂ne (Units.ext h)
  have hAB : IsOrd4 (((u₁ : GL (Fin 3) (ZMod 2)) : M32) * (u₂ : M32)) := by
    rw [← Units.val_mul]
    exact hw
  rcases exists_canon (u₁ : M32) (u₂ : M32) (det3_GL u₁) hA1 hA2 (det3_GL u₂) hB1 hB2 hAB with
    ⟨h, hh, h1, h2⟩ | ⟨h, hh, h1, h2⟩
  · obtain ⟨hu, hhu⟩ := exists_unit_of_det hh
    have k1 : (hu : M32) * (u₁ : M32) = mk32 84 * (hu : M32) := by rw [hhu]; exact h1
    have k2 : (hu : M32) * (u₂ : M32) = mk32 167 * (hu : M32) := by rw [hhu]; exact h2
    refine ⟨MulAut.conj hu, ?_, ?_⟩
    · show (((MulAut.conj hu) u₁ : GL (Fin 3) (ZMod 2)) : M32) = mk32 84
      rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, k1, mul_assoc, Units.mul_inv, mul_one]
    · show (((MulAut.conj hu) u₂ : GL (Fin 3) (ZMod 2)) : M32) = mk32 167
      rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, k2, mul_assoc, Units.mul_inv, mul_one]
  · obtain ⟨hu, hhu⟩ := exists_unit_of_det hh
    have k1 : (hu : M32) * (u₁ : M32)ᵀ = mk32 84 * (hu : M32) := by rw [hhu]; exact h1
    have k2 : (hu : M32) * (u₂ : M32)ᵀ = mk32 167 * (hu : M32) := by rw [hhu]; exact h2
    have t1 : ((tau u₁ : GL (Fin 3) (ZMod 2)) : M32) = (u₁ : M32)ᵀ := by
      rw [tau_val, inv_eq_of_mul_eq_one_right hu₁sq]
    have t2 : ((tau u₂ : GL (Fin 3) (ZMod 2)) : M32) = (u₂ : M32)ᵀ := by
      rw [tau_val, inv_eq_of_mul_eq_one_right hu₂sq]
    refine ⟨tau.trans (MulAut.conj hu), ?_, ?_⟩
    · show (((MulAut.conj hu) (tau u₁) : GL (Fin 3) (ZMod 2)) : M32) = mk32 84
      rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, t1, k1, mul_assoc, Units.mul_inv, mul_one]
    · show (((MulAut.conj hu) (tau u₂) : GL (Fin 3) (ZMod 2)) : M32) = mk32 167
      rw [MulAut.conj_apply, Units.val_mul, Units.val_mul, t2, k2, mul_assoc, Units.mul_inv, mul_one]

end NormSec

end CFSG.RankThree.PartOne.NF7J
