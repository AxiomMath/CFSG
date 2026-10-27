module

public import CFSG.Quasithin.H13.GoldschmidtCTKFamTwoClass
public import CFSG.LocalAnalysis.QuasithinUnique.K1.EvenClassicalLinear
public import CFSG.Quasithin.H13.GoldschmidtCTKFamImg

public section

namespace CFSG.Quasithin.H13.CTK

open CFSG.Open CFSG.QuasithinUnique CFSG.Assembly.LowTwoRank CFSG.LocalAnalysis.ComponentInitial
open CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix
open scoped commutatorElement

variable {K : Type} [Field K]

theorem unitri3_entries {u : SpecialLinearGroup (Fin 3) K} (hu : u ∈ unitriangular 3 K) :
    (u : Matrix (Fin 3) (Fin 3) K) = !![1, u 0 1, u 0 2; 0, 1, u 1 2; 0, 0, 1] := by
  obtain ⟨h1, h2⟩ := mem_unitriangular.1 hu
  ext i j
  fin_cases i <;> fin_cases j <;> simp [h2, h1]

theorem unitri3_mul_comm {u v : SpecialLinearGroup (Fin 3) K} (hu : u ∈ unitriangular 3 K)
    (hv : v ∈ unitriangular 3 K) :
    (u : Matrix (Fin 3) (Fin 3) K) * v =
      (1 + Matrix.single (0 : Fin 3) (2 : Fin 3) (u 0 1 * v 1 2 - v 0 1 * u 1 2)) *
        ((v : Matrix (Fin 3) (Fin 3) K) * u) := by
  rw [unitri3_entries hu, unitri3_entries hv]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply, Matrix.single_apply]
  all_goals ring

theorem single_comm_unitri3 {w : SpecialLinearGroup (Fin 3) K} (hw : w ∈ unitriangular 3 K)
    (t : K) :
    (1 + Matrix.single (0 : Fin 3) (2 : Fin 3) t) * (w : Matrix (Fin 3) (Fin 3) K) =
      (w : Matrix (Fin 3) (Fin 3) K) * (1 + Matrix.single (0 : Fin 3) (2 : Fin 3) t) := by
  rw [unitri3_entries hw]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, Matrix.add_apply, Matrix.single_apply]
  ring

theorem unitriangular3_class_two {u v w : SpecialLinearGroup (Fin 3) K}
    (hu : u ∈ unitriangular 3 K) (hv : v ∈ unitriangular 3 K) (hw : w ∈ unitriangular 3 K) :
    ⁅⁅u, v⁆, w⁆ = 1 := by
  set t : K := u 0 1 * v 1 2 - v 0 1 * u 1 2 with ht
  let z : SpecialLinearGroup (Fin 3) K :=
    Matrix.SpecialLinearGroup.transvection (show (0 : Fin 3) ≠ 2 by decide) t
  have hz : (z : Matrix (Fin 3) (Fin 3) K) = 1 + Matrix.single (0 : Fin 3) (2 : Fin 3) t :=
    Matrix.SpecialLinearGroup.transvection_coe _ _
  have h1 : u * v = z * (v * u) := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, hz]
    exact unitri3_mul_comm hu hv
  have h2 : ⁅u, v⁆ = z := by
    rw [commutatorElement_def]
    calc u * v * u⁻¹ * v⁻¹ = (u * v) * (v * u)⁻¹ := by group
      _ = z := by rw [h1]; group
  have h3 : z * w = w * z := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, hz]
    exact single_comm_unitri3 hw t
  rw [h2, commutatorElement_eq_one_iff_mul_comm]
  exact h3

theorem twoGroupsClassTwo_projectiveSL_three [Finite K] [CharP K 2] :
    TwoGroupsClassTwo (projectiveSL 3 K) := by
  obtain ⟨Q, hQ⟩ := exists_sylow_projUnitriangular (K := K) 2 (n := 3) (by norm_num)
  refine TwoGroupsClassTwo.of_sylow Q fun x hx y hy z hz => ?_
  rw [hQ] at hx hy hz
  obtain ⟨u, hu, rfl⟩ := Subgroup.mem_map.1 hx
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.1 hy
  obtain ⟨w, hw, rfl⟩ := Subgroup.mem_map.1 hz
  rw [← map_commutatorElement, ← map_commutatorElement, unitriangular3_class_two hu hv hw,
    map_one]

theorem exclA5BlockFor_two_lin :
    ExclA5BlockFor fun S _ =>
      ∃ f : ℕ, 1 ≤ f ∧ CFSG.Assembly.LowTwoRank.StatedClassicalModel S .PSL 3 2 f := by
  refine ExclA5BlockFor.of_not_config fun S _ _ hS hc => ?_
  obtain ⟨f, hf, -, K, _, hfin, hcard, ⟨e⟩⟩ := hS
  have : CharP K 2 := finite_field_prime_power_characteristic Nat.prime_two hf hcard
  exact hc.false_of_classTwo (twoGroupsClassTwo_projectiveSL_three.of_mulEquiv
    (e.trans (K1.statedProjEquivProjectiveSL 3 K)))

end CFSG.Quasithin.H13.CTK
