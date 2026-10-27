module

public import CFSG.LocalAnalysis.QuasithinUnique.Constrained.Setup.X7aAut

public section

namespace CFSG.Quasithin.G11.Harris.L3

open scoped MatrixGroups
open CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.QuasithinUnique.Setup.X7a

variable {F : Type*} [Field F] [CharP F 2]

theorem eq_one_of_mem_scalars_of_mul_self {z : SL(3, F)} (hz : z ∈ scalars 3 F) (h : z * z = 1) :
    z = 1 := by
  obtain ⟨c, -, hc⟩ := hz
  have h1 := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F) 0 0) h
  simp only [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_one, hc,
    Matrix.scalar_apply, Matrix.diagonal_mul_diagonal, Matrix.diagonal_apply_eq,
    Matrix.one_apply_eq] at h1
  have h2 : ((c : F) - 1) ^ 2 = 0 := by
    have h2' : (2 : F) = 0 := by exact_mod_cast CharP.cast_eq_zero F 2
    linear_combination h1 + (-(c : F) + 1) * h2'
  have h3 : (c : F) = 1 := sub_eq_zero.mp (pow_eq_zero_iff two_ne_zero |>.mp h2)
  apply Subtype.ext
  rw [hc]
  simp [Matrix.scalar_apply, h3]

theorem commute_of_commutator_mem_scalars {s t : SL(3, F)} (hs : s * s = 1) (ht : t * t = 1)
    (hst : s * t * s⁻¹ * t⁻¹ ∈ scalars 3 F) : s * t = t * s := by
  have hs' : s⁻¹ = s := inv_eq_of_mul_eq_one_right hs
  have ht' : t⁻¹ = t := inv_eq_of_mul_eq_one_right ht
  rw [hs', ht'] at hst
  have hs2 : ∀ x : SL(3, F), s * (s * x) = x := fun x => by rw [← mul_assoc, hs, one_mul]
  have ht2 : ∀ x : SL(3, F), t * (t * x) = x := fun x => by rw [← mul_assoc, ht, one_mul]
  have hzc : (s * t * s * t) * s = s * (s * t * s * t) :=
    (Subgroup.mem_center_iff.mp (scalars_le_center 3 F hst) s).symm
  have h1 : s * t * s * t = t * s * t * s := by
    calc s * t * s * t = s * t * s * t * (s * s) := by rw [hs, mul_one]
      _ = (s * t * s * t * s) * s := by simp only [mul_assoc]
      _ = (s * (s * t * s * t)) * s := by rw [hzc]
      _ = t * s * t * s := by simp only [mul_assoc, hs2]
  have hz2 : (s * t * s * t) * (s * t * s * t) = 1 := by
    have := congrArg (fun x => (s * t * s * t) * x) h1
    refine this.trans ?_
    simp only [mul_assoc, hs2, ht2, hs]
  have hz1 := eq_one_of_mem_scalars_of_mul_self hst hz2
  have h2 : (s * t) * (s * t) = 1 := by
    simpa only [mul_assoc] using hz1
  have h3 := inv_eq_of_mul_eq_one_right h2
  rw [mul_inv_rev, hs', ht'] at h3
  exact h3.symm

theorem card_map_proj_of_involutions (S : Subgroup SL(3, F)) (hS2 : ∀ s ∈ S, s * s = 1) :
    Nat.card (S.map (proj 3 F)) = Nat.card S := by
  have hinj : Function.Injective ((proj 3 F).comp S.subtype) := by
    rw [injective_iff_map_eq_one]
    rintro ⟨s, hs⟩ h
    apply Subtype.ext
    exact eq_one_of_mem_scalars_of_mul_self (proj_eq_one_iff.mp h) (hS2 s hs)
  have hrange : S.map (proj 3 F) = ((proj 3 F).comp S.subtype).range := by
    rw [MonoidHom.range_comp, Subgroup.range_subtype]
  rw [hrange]
  exact Nat.card_congr (MonoidHom.ofInjective hinj).toEquiv.symm

theorem card_le_of_involutions [Finite F] (S : Subgroup SL(3, F)) (hS2 : ∀ s ∈ S, s * s = 1)
    (hSc : ∀ s ∈ S, ∀ t ∈ S, s * t = t * s) : Nat.card S ≤ Nat.card F ^ 2 := by
  rw [← card_map_proj_of_involutions S hS2]
  refine card_le_of_elementary_abelian_projectiveSL _ ?_ ?_
  · rintro _ ⟨s, hs, rfl⟩
    rw [← map_mul, hS2 s hs, map_one]
  · rintro _ ⟨s, hs, rfl⟩ _ ⟨t, ht, rfl⟩
    rw [← map_mul, ← map_mul, hSc s hs t ht]

end CFSG.Quasithin.G11.Harris.L3
