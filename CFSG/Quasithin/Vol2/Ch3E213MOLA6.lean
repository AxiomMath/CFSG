module

public import CFSG.Quasithin.Vol2.Ch3E213MOLA1
public import CFSG.Quasithin.Vol2.Ch3E213MOLA5
public import CFSG.ClassicalInvolution.AschTight.S19MInv
public import CFSG.Quasithin.Vol2.Ch3E213MOLA4

public section

namespace CFSG.Quasithin.Ch3E213M.OLA

open CFSG.ClassicalInvolution CFSG.ClassicalInvolution.Models.Transfer
  CFSG.ClassicalInvolution.Disconnected.AschTight.S19K
open scoped MatrixGroups

variable {F : Type} [Field F] [Finite F] {K : Type} [Group K]

theorem lin_commute_two (hodd : Odd (Nat.card F)) (θ : SL(3, F) →* K)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center SL(3, F)) :
    ∀ y ∈ Subgroup.centralizer ({θ (Models.rootInv F (n := 3) (by norm_num))} : Set K),
      ∀ a ∈ (Models.rootSL2 F (n := 3) (by norm_num)).map θ,
      ∀ b ∈ (Models.rootSL2 F (n := 3) (by norm_num)).map θ, a * b ≠ b * a →
      y * a = a * y → y * b = b * y → y ∈ Subgroup.centralizer
        (((Models.rootSL2 F (n := 3) (by norm_num)).map θ : Subgroup K) : Set K) := by
  have h2 : (2 : F) ≠ 0 := Models.two_ne_zero_of_odd_natCard hodd
  have hst := Models.isLongRootSL2_standard (K := F) (by norm_num : 2 ≤ 3)
  intro y hy
  rw [centralizer_map_eq_of_isLongRootSL2 h2 hθ hker (Or.inl (by norm_num)) hst] at hy
  obtain ⟨x, hx, rfl⟩ := hy
  rintro _ ⟨_, ⟨A, rfl⟩, rfl⟩ _ ⟨_, ⟨B, rfl⟩, rfl⟩ hab hxa hxb
  set X := ((x : SL(3, F)) : Matrix (Fin 3) (Fin 3) F) with hX
  have hXB : IsBlockDiag X := by
    refine isBlockDiag_of_commute_negBlock h2 X ?_
    have h1 := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F))
      (Subgroup.mem_centralizer_singleton_iff.mp hx)
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_rootInv_three] at h1
    exact h1
  obtain ⟨g02, g12, g20, g21⟩ := hXB
  have hR : ∀ C : SL(2, F), θ x * θ (WeakCT.blockSL F 3 2 0 (by norm_num) C) =
      θ (WeakCT.blockSL F 3 2 0 (by norm_num) C) * θ x →
      x * WeakCT.blockSL F 3 2 0 (by norm_num) C = WeakCT.blockSL F 3 2 0 (by norm_num) C * x := by
    intro C hc
    set r := WeakCT.blockSL F 3 2 0 (by norm_num) C
    have hr : r ∈ Models.rootSL2 F (n := 3) (by norm_num) := ⟨C, rfl⟩
    have hcl := Models.isClassicalSL2_rootSL2 (K := F) h2 (by norm_num : 2 ≤ 3)
    have hN := hcl.centralizer_le_normalizer hx
    have h1 : x * r * x⁻¹ * r⁻¹ ∈ Models.rootSL2 F (n := 3) (by norm_num) :=
      Subgroup.mul_mem _ ((Subgroup.mem_normalizer_iff.mp hN r).mp hr) (Subgroup.inv_mem _ hr)
    have h3 : x * r * x⁻¹ * r⁻¹ ∈ θ.ker := by
      rw [MonoidHom.mem_ker, map_mul, map_mul, map_mul, map_inv, map_inv, hc]
      group
    have h4 := eq_one_of_mem_ker_of_isLongRootSL2 hodd (le_refl 3) hst hker _ h1 h3
    calc x * r = x * r * x⁻¹ * r⁻¹ * (r * x) := by group
      _ = r * x := by rw [h4, one_mul]
  set Y : Matrix (Fin 2) (Fin 2) F := !![X 0 0, X 0 1; X 1 0, X 1 1] with hY
  have hmat : ∀ C : SL(2, F),
      x * WeakCT.blockSL F 3 2 0 (by norm_num) C = WeakCT.blockSL F 3 2 0 (by norm_num) C * x →
      Y * (C : Matrix (Fin 2) (Fin 2) F) = (C : Matrix (Fin 2) (Fin 2) F) * Y := by
    intro C hC
    have h1 := congrArg (fun g : SL(3, F) => (g : Matrix (Fin 3) (Fin 3) F)) hC
    simp only [Matrix.SpecialLinearGroup.coe_mul, coe_blockSL3] at h1
    have e00 := congrFun (congrFun h1 0) 0
    have e01 := congrFun (congrFun h1 0) 1
    have e10 := congrFun (congrFun h1 1) 0
    have e11 := congrFun (congrFun h1 1) 1
    simp [Matrix.mul_apply, Fin.sum_univ_three, ← hX, g02, g12, g20, g21] at e00 e01 e10 e11
    ext i j
    fin_cases i <;> fin_cases j <;> simp [hY, Matrix.mul_apply, Fin.sum_univ_two] <;>
      first
        | linear_combination e00
        | linear_combination e01
        | linear_combination e10
        | linear_combination e11
  have hAB : (A : Matrix (Fin 2) (Fin 2) F) * B ≠ B * A := fun h => hab (by
    rw [← map_mul, ← map_mul, ← map_mul, ← map_mul]
    congr 2
    exact Subtype.ext (by rw [Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_mul, h]))
  obtain ⟨y01, y10, y0011⟩ := isScalar_of_commute_two (hmat A (hR A hxa)) (hmat B (hR B hxb)) hAB
  simp only [hY, Matrix.of_apply, Matrix.cons_val', Matrix.cons_val_zero, Matrix.cons_val_one,
    Matrix.empty_val', Matrix.cons_val_fin_one] at y01 y10 y0011
  rw [Subgroup.mem_centralizer_iff]
  rintro _ ⟨_, ⟨C, rfl⟩, rfl⟩
  rw [← map_mul, ← map_mul]
  congr 1
  apply Subtype.ext
  rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul, coe_blockSL3, ← hX]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_three, g02, g12, g20, g21, y01, y10, ← y0011] <;> ring

theorem lin_conj_inv (hodd : Odd (Nat.card F)) (θ : SL(3, F) →* K)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center SL(3, F)) :
    ∀ t : K, orderOf t = 2 →
      ∃ g : K, t = g * θ (Models.rootInv F (n := 3) (by norm_num)) * g⁻¹ := by
  intro t ht
  have h2 : (2 : F) ≠ 0 := Models.two_ne_zero_of_odd_natCard hodd
  obtain ⟨y₀, rfl⟩ := hθ t
  have ht2 : θ y₀ * θ y₀ = 1 := by rw [← pow_two, ← ht, pow_orderOf_eq_one]
  have hy₀ : y₀ * y₀ ∈ θ.ker := by rw [MonoidHom.mem_ker, map_mul, ht2]
  have hy2 : y₀ ^ 3 * y₀ ^ 3 = 1 := by
    rw [← pow_add, show 3 + 3 = 2 * 3 from rfl, pow_mul, pow_two]
    exact center_pow_three_sl3 _ (hker hy₀)
  have hθy : θ (y₀ ^ 3) = θ y₀ := by
    rw [map_pow, pow_succ, pow_two, ht2, one_mul]
  have hy1 : y₀ ^ 3 ≠ 1 := fun h => by
    have h1 : θ y₀ = 1 := by rw [← hθy, h, map_one]
    rw [h1, orderOf_one] at ht
    omega
  have hcl := Models.isClassicalSL2_rootSL2 (K := F) h2 (by norm_num : 2 ≤ 3)
  have hz2 : Models.rootInv F (n := 3) (by norm_num) * Models.rootInv F (n := 3) (by norm_num) =
      1 := by
    have h1 := pow_orderOf_eq_one (Models.rootInv F (n := 3) (by norm_num))
    rw [hcl.orderOf_eq_two, pow_two] at h1
    exact h1
  have hz1 : Models.rootInv F (n := 3) (by norm_num) ≠ 1 := fun h => by
    have h1 := hcl.orderOf_eq_two
    rw [h, orderOf_one] at h1
    omega
  obtain ⟨g, hg⟩ := Disconnected.AschTight.S19M.involutionsConj_sl3 h2 _ _ hz2 hy2 hz1 hy1
  refine ⟨θ g, ?_⟩
  rw [← hθy, ← hg, map_mul, map_mul, map_inv]

variable [Finite K]

theorem lin_kfact (hq : Nat.card F % 4 = 3) (h5 : 5 ≤ Nat.card F)
    (hcl : RouteD.Gaps.LinearAutClassification F 3) (θ : SL(3, F) →* K)
    (hθ : Function.Surjective θ) (hker : θ.ker ≤ Subgroup.center SL(3, F)) (S : Sylow 2 K) :
    ∃ z' : K, orderOf z' = 2 ∧ E2P.zOf (S : Subgroup K) = Subgroup.zpowers z' ∧
      (∀ Q : Subgroup K, Q ≤ Subgroup.centralizer ({z'} : Set K) → IsPGroup 2 Q →
        Subgroup.centralizer ({z'} : Set K) ≤ Subgroup.normalizer (Q : Set K) →
        Q ≤ Subgroup.zpowers z') ∧
      ∀ v : MulAut K, orderOf v = 2 →
        (∀ x ∈ Subgroup.centralizer ({z'} : Set K), v x * x⁻¹ ∈ Subgroup.zpowers z') →
        v ∈ (MulAut.conj : K →* MulAut K).range := by
  have hodd : Odd (Nat.card F) := Nat.odd_iff.mpr (by omega)
  have hL : IsClassicalSL2 F ((Models.rootSL2 F (n := 3) (by norm_num)).map θ)
      (θ (Models.rootInv F (n := 3) (by norm_num))) :=
    IsLongRootImage.isClassicalSL2 hodd (le_refl 3) hθ hker (Or.inl (by norm_num))
      ⟨_, _, Models.isLongRootSL2_standard (K := F) (by norm_num : 2 ≤ 3), rfl, rfl⟩
  refine kfact_of_classical hodd (by omega) hL (lin_centralizer_two hq (by omega) θ hθ hker)
    (lin_commute_two hodd θ hθ hker) (fun v hv2 hfix => ?_) (lin_conj_inv hodd θ hθ hker) S
  obtain ⟨y, hy⟩ := inner_of_fix_root hodd h5 hcl θ hθ hker hv2 fun A =>
    hfix _ ⟨_, ⟨A, rfl⟩, rfl⟩
  exact ⟨y, hy.symm⟩

end CFSG.Quasithin.Ch3E213M.OLA
