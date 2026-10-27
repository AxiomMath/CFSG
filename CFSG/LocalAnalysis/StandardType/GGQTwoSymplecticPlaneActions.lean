module

public import CFSG.LocalAnalysis.GLTheoremA.CatA.S265SGSpFrame
public import CFSG.LocalAnalysis.StandardType.GGTableBExcTwoTBTorus
public import CFSG.LocalAnalysis.SeitzReduction.SymplecticPilotBlocks
public import CFSG.LocalAnalysis.StandardType.GGSixRootFusionWitSpNsDiag
public import CFSG.LieType.Chevalley.RankOneGaussian
public import CFSG.Timmesfeld.Orders.Classical
public import CFSG.Sporadic.Suz.Setup
public import CFSG.LocalAnalysis.SectionRank.SporadicCover
public import CFSG.Sporadic.M23.M23Group
public import CFSG.Sporadic.Suz.W64Spec

public section

open Matrix CFSG.LieType.Chevalley CFSG.ClassicalInvolution.Models.SymplecticPairs
open CFSG.Open CFSG.StandardType.WitSpNs CFSG.SeitzReduction.SymplecticPilot
open CFSG.LieType.Universal.Symplectic.SpExtras (mat)

namespace CFSG.StandardType.SymplecticPlaneActions

variable {K : Type} [Field K] [Finite K] {n : ℕ}

theorem pow_three_eq_one_of_sq_add_self_add_one {M : Matrix (Fin 2) (Fin 2) K}
    (hM : M * M + M + 1 = 0) : M ^ 3 = 1 := by
  have : M ^ 3 - 1 = (M - 1) * (M * M + M + 1) := by noncomm_ring
  rwa [hM, mul_zero, sub_eq_zero] at this

theorem ne_one_of_sq_add_self_add_one (hK : Nat.card K = 2)
    {M : Matrix (Fin 2) (Fin 2) K} (hM : M * M + M + 1 = 0) : M ≠ 1 := by
  intro h1
  haveI : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 1) (by simpa using hK)
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h2' : (1 : K) + 1 = 0 := by
    rw [← show (2 : K) = 1 + 1 by norm_num]; exact h2
  rw [h1] at hM
  have h := congrFun (congrFun hM (0 : Fin 2)) (0 : Fin 2)
  simp [Matrix.add_apply, Matrix.mul_apply, Matrix.one_apply, Fin.sum_univ_two,
    h2', add_assoc] at h

theorem WSL_conj_mkSL_eq_inv (hK : Nat.card K = 2) {M : Matrix (Fin 2) (Fin 2) K}
    (hdet : M.det = 1) (hM : M * M + M + 1 = 0) :
    (WSL : SL2 K) * mkSL M hdet * (WSL : SL2 K)⁻¹ = (mkSL M hdet)⁻¹ := by
  classical
  haveI : CharP K 2 :=
    CFSG.Timmesfeld.ClassicalOrders.charP_two_of_card_eq (f := 1) (by simpa using hK)
  have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
  have h2' : (1 : K) + 1 = 0 := by
    rw [← show (2 : K) = 1 + 1 by norm_num]; exact h2
  have hneg : (-1 : K) = 1 := (neg_eq_iff_add_eq_zero).mpr h2'
  have h3 : M * M * M = 1 := by
    calc M * M * M = M ^ 3 := by rw [pow_succ, pow_succ, pow_one, mul_assoc]
      _ = 1 := pow_three_eq_one_of_sq_add_self_add_one hM
  have h1 : M ≠ 1 := ne_one_of_sq_add_self_add_one hK hM
  have hM1inv : (!![0, 1; 1, 1] : Matrix (Fin 2) (Fin 2) K)⁻¹ = !![1, 1; 1, 0] := by
    rw [Matrix.inv_eq_right_inv (A := !![0, 1; 1, 1])]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h2']
  have hM2inv : (!![1, 1; 1, 0] : Matrix (Fin 2) (Fin 2) K)⁻¹ = !![0, 1; 1, 1] := by
    rw [Matrix.inv_eq_right_inv (A := !![1, 1; 1, 0])]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, h2']
  have hW2 : (WSL : SL2 K) * WSL = 1 := by
    apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [WSL, coe_WSL, h2', hneg, Matrix.mul_apply, Fin.sum_univ_two]
  have hWi : (WSL : SL2 K)⁻¹ = WSL := inv_eq_of_mul_eq_one_right hW2
  rw [hWi]
  rcases CFSG.StandardType.TableBExcTwoTB.mat_eq_of_pow_three hK M hdet h3 h1 with rfl | rfl
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, coe_mkSL]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [WSL, coe_WSL, h2', hneg, Matrix.mul_apply, Fin.sum_univ_two, hM1inv, hM2inv]
  · apply Subtype.ext
    rw [Matrix.SpecialLinearGroup.coe_mul, Matrix.SpecialLinearGroup.coe_mul,
      Matrix.SpecialLinearGroup.coe_inv, coe_mkSL]
    ext i j <;> fin_cases i <;> fin_cases j <;>
      simp [WSL, coe_WSL, h2', hneg, Matrix.mul_apply, Fin.sum_univ_two, hM1inv, hM2inv]


open CFSG.LieType.Universal.Symplectic.SpExtras (mat)
open CFSG.Assembly.LowTwoRank
open CFSG.SeitzReduction.SymplecticPilot (permSp mat_conj_permSp_apply)
open CFSG.StandardType.WitSpNs

omit [Finite K] in
theorem mat_longBlock_conj_planeMat {n : ℕ} {g : StatedSp n K}
    {P : Fin n → Matrix (Fin 2) (Fin 2) K} (hg : mat n K g = planeMat P)
    (i : Fin n) (A : Matrix.SpecialLinearGroup (Fin 2) K) :
    mat n K (longBlock K n i A * g * (longBlock K n i A)⁻¹) =
      planeMat (fun j => if j = i then
        (A : Matrix (Fin 2) (Fin 2) K) * P j *
          ((A⁻¹ : Matrix.SpecialLinearGroup (Fin 2) K) : Matrix (Fin 2) (Fin 2) K)
        else P j) := by
  classical
  rw [map_mul, map_mul, ← map_inv, mat_longBlock_eq_planeMat,
    mat_longBlock_eq_planeMat, hg, planeMat_mul, planeMat_mul]
  congr 1
  funext j
  by_cases hji : j = i
  · subst j
    simp
  · simp [hji, Function.update_apply]

omit [Finite K] in
theorem mat_permSp_conj_planeMat {n : ℕ} {g : StatedSp n K}
    {P : Fin n → Matrix (Fin 2) (Fin 2) K} (hg : mat n K g = planeMat P)
    (π : Equiv.Perm (Fin n)) :
    mat n K (permSp K π * g * (permSp K π)⁻¹) =
      planeMat (fun j => P (π.symm j)) := by
  ext a b
  have h := mat_conj_permSp_apply π g (Sum.map π.symm π.symm a) (Sum.map π.symm π.symm b)
  have ha : Sum.map π π (Sum.map π.symm π.symm a) = a := by
    rcases a with a | a <;> simp
  have hb : Sum.map π π (Sum.map π.symm π.symm b) = b := by
    rcases b with b | b <;> simp
  rw [ha, hb] at h
  rw [h, hg, planeMat_apply, planeMat_apply]
  rcases a with a | a <;> rcases b with b | b
  all_goals
    by_cases hab : a = b
    · subst b
      simp [plane, side]
    · have hp : π.symm a ≠ π.symm b := fun he => hab (π.symm.injective he)
      simp [plane, side, hab, hp]

end CFSG.StandardType.SymplecticPlaneActions

end
