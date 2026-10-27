module

public import CFSG.Quasithin.Background.ONanE68Lin3Mat
public import CFSG.Quasithin.Background.ONanE68Sp4Torus

public section

namespace CFSG.Quasithin.RonanE611

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.LinearFlag
  CFSG.LocalAnalysis.ComponentInitial.LinearFieldFour CFSG.LocalAnalysis.ComponentInitial.LinearCover
  CFSG.QuasithinUnique.Lin2.L3Core CFSG.QuasithinUnique.Setup.X7a
  CFSG.Quasithin.E6.E68Proof CFSG.Quasithin.E6.E68Proof.Lin3

section Lin3

variable {F : Type} [Field F] [Finite F]

theorem units_pow_card_sub_one (α : Fˣ) : α ^ (Nat.card F - 1) = 1 := by
  rw [← Nat.card_units]
  exact pow_card_eq_one'

theorem coe_pow_apply_self {n : ℕ} {A : SpecialLinearGroup (Fin n) F}
    (hA : (A : Matrix (Fin n) (Fin n) F).IsUpperTriangular) (i : Fin n) (k : ℕ) :
    ((A ^ k : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F) i i =
      (A : Matrix (Fin n) (Fin n) F) i i ^ k := by
  induction k with
  | zero => simp
  | succ k ih =>
    have hAk : ((A ^ k : SpecialLinearGroup (Fin n) F) : Matrix (Fin n) (Fin n) F).IsUpperTriangular :=
      fun a b hab => (upperTriangular n F).pow_mem (fun a b hab => hA hab) k a b hab
    rw [pow_succ, Matrix.SpecialLinearGroup.coe_mul, mul_apply_self_of_isUpperTriangular hAk hA, ih,
      pow_succ]

variable [CharP F 2]

theorem pow_card_sub_one_mem_projUnitriangular {g : projectiveSL 3 F}
    (hg : g ∈ Subgroup.normalizer ((projUnitriangular 3 F : Subgroup (projectiveSL 3 F)) :
      Set (projectiveSL 3 F))) : g ^ (Nat.card F - 1) ∈ projUnitriangular 3 F := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  rw [normalizer_projUnitriangular 2] at hg
  obtain ⟨A, hA, rfl⟩ := hg
  have hA' : (A : Matrix (Fin 3) (Fin 3) F).IsUpperTriangular := fun a b hab => hA a b hab
  have hAk : A ^ (Nat.card F - 1) ∈ unitriangular 3 F := by
    refine ⟨fun i j hij => (upperTriangular 3 F).pow_mem hA _ i j hij, fun i => ?_⟩
    rw [coe_pow_apply_self hA' i]
    have hne : (A : Matrix (Fin 3) (Fin 3) F) i i ≠ 0 := diag_ne_zero_of_upperTriangular hA i
    have := units_pow_card_sub_one (Units.mk0 _ hne)
    exact congrArg Units.val this
  rw [← map_pow]
  exact Subgroup.mem_map_of_mem _ hAk

theorem sq_eq_one_of_central_projUnitriangular {z : projectiveSL 3 F}
    (hz : z ∈ projUnitriangular 3 F) (hc : ∀ y ∈ projUnitriangular 3 F, z * y = y * z) :
    z * z = 1 := by
  obtain ⟨x, y, c, rfl⟩ := exists_hei hz
  have h1 := hc (hei 0 1 0) (hei_mem 0 1 0)
  have h2 := hc (hei 1 0 0) (hei_mem 1 0 0)
  rw [hei_mul, hei_mul] at h1 h2
  have e1 := (hei_inj h1).2.2
  have e2 := (hei_inj h2).2.2
  have hx : x = 0 := by linear_combination (-1 : F) * e1
  have hy : y = 0 := by linear_combination e2
  subst hx
  subst hy
  rw [hei_mul, ← hei_zero]
  exact hei_congr (by simp) (by simp) (by simp [CharTwo.add_self_eq_zero])

end Lin3

end CFSG.Quasithin.RonanE611
