module

public import CFSG.Certificates.Kernel.BabyMonster.PairSound

public section

namespace CFSG.KC.BM.MemChain

open CFSG.KC.BM

local notation "sm" => stripMat

theorem allStrips_of_nil {Ws : List (List Nat)} : ∀ {A C : List Nat}, AllStrips2 Ws [] A C →
    AllStrips Ws A C
  | _, _, .nil => .nil
  | _, _, .cons a c _ _ hb h => .cons a c _ _ hb (allStrips_of_nil h)

variable {S : Submonoid (Matrix (Fin 4370) (Fin 4370) (ZMod 2))}

theorem mem_of_mul_eq_one {X Y : Matrix (Fin 4370) (Fin 4370) (ZMod 2)} (mX : X ∈ S)
    (h : X * Y = 1) : Y ∈ S := by
  let u : (Matrix (Fin 4370) (Fin 4370) (ZMod 2))ˣ := ⟨X, Y, h, mul_eq_one_comm.1 h⟩
  have hfin : IsOfFinOrder u := isOfFinOrder_of_finite u
  have hpos := hfin.orderOf_pos
  have hinv : u⁻¹ = u ^ (orderOf u - 1) := by
    refine inv_eq_of_mul_eq_one_left ?_
    rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
  have hY : Y = X ^ (orderOf u - 1) := by
    have := congrArg Units.val hinv
    simpa [u] using this
  rw [hY]
  exact S.pow_mem mX _

theorem mem1 {A B C : List Nat} (wA : wfMat A = true) (wB : wfMat B = true) (_ : wfMat C = true)
    (mA : sm A ∈ S) (mB : sm B ∈ S) (h : AllStrips2 [B] [] A C) : sm C ∈ S := by
  have e := stripMat_mul_of_allStrips (Ws := [B]) (by simp [wB]) wA (allStrips_of_nil h)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e
  rw [← e]
  exact S.mul_mem mA mB

theorem mem2 {A B B' C : List Nat} (wA : wfMat A = true) (wB : wfMat B = true)
    (wB' : wfMat B' = true) (_ : wfMat C = true) (mA : sm A ∈ S) (mB : sm B ∈ S) (mB' : sm B' ∈ S)
    (h : AllStrips2 [B, B'] [] A C) : sm C ∈ S := by
  have e := stripMat_mul_of_allStrips (Ws := [B, B']) (by simp [wB, wB']) wA (allStrips_of_nil h)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e
  rw [← e]
  exact S.mul_mem (S.mul_mem mA mB) mB'

theorem memI {A B : List Nat} (wA : wfMat A = true) (wB : wfMat B = true) (mA : sm A ∈ S)
    (h : AllStrips2 [B] [] A idStrips) : sm B ∈ S := by
  have e := stripMat_mul_eq_one (Ws := [B]) (by simp [wB]) wA (allStrips_of_nil h)
  simp only [List.map_cons, List.map_nil, List.foldl_cons, List.foldl_nil] at e
  exact mem_of_mul_eq_one mA e

end CFSG.KC.BM.MemChain

end
