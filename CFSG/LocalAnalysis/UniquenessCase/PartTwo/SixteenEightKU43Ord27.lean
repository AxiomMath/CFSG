module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43Leaves
import CFSG.RankThree.PartTwo.Sec4.Item426A6U43
public import CFSG.ClassicalInvolution.Q3.ModelOddCentralizerGaussUnitary
public import CFSG.Quasithin.Background.A318PL3Inst
public import CFSG.RankThree.PartTwo.Sec4.Item47CasesEven

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43

open Matrix CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSU)
open CFSG.ClassicalGroups.UnitaryFlag CFSG.LocalAnalysis.ComponentInitial
open CFSG.Quasithin.A318P (projSU_of_statedClassicalModel_gen)
open CFSG.RankThree.PartTwo.Sec4.Item426 (pow_mul_four_eq_one)

theorem pow_nine_of_pow_twentyseven {K : Type*} [Field K] [CharP K 3]
    {M : Matrix (Fin 4) (Fin 4) K} (h : M ^ 27 = 1) : M ^ 9 = 1 := by
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hc : Commute M 1 := Commute.one_right M
  have h27 : (M - 1) ^ (3 ^ 3) = 0 := by
    rw [sub_pow_char_pow_of_commute (p := 3) (n := _) hc, one_pow, show 3 ^ 3 = 27 by norm_num, h,
      sub_self]
  set f := Matrix.toLinAlgEquiv' (M - 1) with hf
  have hf27 : f ^ (3 ^ 3) = 0 := by rw [hf, ← map_pow, h27, map_zero]
  have hker : LinearMap.ker (f ^ 4) = ⊤ := by
    have h1 := Module.End.ker_pow_eq_ker_pow_finrank_of_le (f := f) (m := 3 ^ 3)
      (by rw [Module.finrank_fin_fun]; norm_num)
    rw [Module.finrank_fin_fun, hf27, LinearMap.ker_zero] at h1
    exact h1.symm
  have hf4 : f ^ 4 = 0 := LinearMap.ker_eq_top.mp hker
  have hM4 : (M - 1) ^ 4 = 0 := by
    apply Matrix.toLinAlgEquiv'.injective
    rw [map_pow, ← hf, hf4, map_zero]
  have h9 : (M - 1) ^ (3 ^ 2) = 0 := by
    rw [show 3 ^ 2 = 4 + 5 by norm_num, pow_add, hM4, zero_mul]
  rw [sub_pow_char_pow_of_commute (p := 3) (n := _) hc, one_pow, show 3 ^ 2 = 9 by norm_num] at h9
  exact sub_eq_zero.mp h9

theorem orderOf_ne_twentyseven_projSU (x : projSU 4 3 1) : orderOf x ≠ 27 := by
  intro hx
  set K := GaloisField 3 (2 * 1) with hKdef
  have hU : UnitaryFieldData 3 1 K :=
    ⟨Nat.prime_three, le_rfl, GaloisField.card 3 (2 * 1) (by norm_num)⟩
  have : CharP K 3 := hU.charP
  obtain ⟨X, hX, hXx⟩ : ∃ X : GL (Fin 4) K, X ∈ unitarySU 3 1 K 4 ∧
      ProjGenLinGroup.mk X = (x : ProjGenLinGroup (Fin 4) K) :=
    Subgroup.mem_map.mp
      ((SetLike.ext_iff.mp (CFSG.RankThree.PartTwo.Sec4.projSU_eq_map_statedSU 4 3 1) _).mp x.2)
  have hXdet := ((mem_unitarySU_iff hU).mp hX).1
  have hx27 : (x : ProjGenLinGroup (Fin 4) K) ^ 27 = 1 := by
    have h := pow_orderOf_eq_one x
    rw [hx] at h
    rw [← Subgroup.coe_pow, h, OneMemClass.coe_one]
  have hX108 : X ^ (27 * 4) = 1 := pow_mul_four_eq_one hXdet (by rw [hXx, hx27])
  have hM : ((X ^ 4 : GL (Fin 4) K) : Matrix (Fin 4) (Fin 4) K) ^ 27 = 1 := by
    have h4 : (X ^ 4) ^ 27 = 1 := by rw [← pow_mul, show 4 * 27 = 27 * 4 by norm_num, hX108]
    rw [← Units.val_pow_eq_pow_val, h4, Units.val_one]
  have hM9 := pow_nine_of_pow_twentyseven hM
  have hX36 : X ^ (4 * 9) = 1 := by
    rw [pow_mul]; exact Units.ext (by rw [Units.val_pow_eq_pow_val, hM9, Units.val_one])
  have hx36 : x ^ 36 = 1 := by
    apply Subtype.ext
    rw [Subgroup.coe_pow, ← hXx, ← map_pow, show 36 = 4 * 9 by norm_num, hX36, map_one,
      OneMemClass.coe_one]
  have := orderOf_dvd_of_pow_eq_one hx36
  rw [hx] at this
  norm_num at this

theorem u43NoOrder27 : U43NoOrder27Statement := by
  unfold U43NoOrder27Statement
  intro S _ _ hS g
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  obtain ⟨e⟩ := projSU_of_statedClassicalModel_gen (hS.statedClassicalModel (by decide))
  rw [← MulEquiv.orderOf_eq e]
  exact orderOf_ne_twentyseven_projSU (e g)

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightKU43

