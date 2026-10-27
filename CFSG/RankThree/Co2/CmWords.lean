module

public import CFSG.RankThree.Co2.CrConj
public import CFSG.Certificates.Kernel.Co2Syl.Words
public import Mathlib.LinearAlgebra.Matrix.NonsingularInverse

public section

namespace CFSG.RankThree.Co2

open CFSG.KC.Co2Syl CFSG.Monster.B.TwoA.Co2Inv

local notation "M22" => Matrix (Fin 22) (Fin 22) (ZMod 2)

theorem rowsMat_congr {A B : Array ℕ} (h : ∀ t < 22, A[t]! = B[t]!) : rowsMat A = rowsMat B := by
  ext t j
  rw [rowsMat_apply, rowsMat_apply, h t t.isLt]

theorem wordMat_singleton (l : ℕ) : wordMat [l] = rowsMat (letterRows l) := by
  rw [wordMat_eq_prod, List.map_singleton, List.prod_singleton]

theorem letterMat_mem_Cm_of_ge {l : ℕ} (hl : 21 ≤ l) (hl' : l < 42) :
    rowsMat (letterRows l) ∈ Cm := by
  have hget : ∀ k < 21, letters21[k]! = [k + 21] := by decide
  have hk : l - 21 < letters21.size := by
    change l - 21 < 21
    omega
  have e : wordMat letters21[l - 21] = rowsMat (letterRows l) := by
    rw [← getElem!_pos letters21 (l - 21) hk, hget (l - 21) (by omega),
      show l - 21 + 21 = l by omega, wordMat_singleton]
  rw [← e]
  exact Submonoid.subset_closure ⟨⟨l - 21, hk⟩, rfl⟩

theorem letterMat_mem_Cm {l : ℕ} (hl : l < 42) : rowsMat (letterRows l) ∈ Cm := by
  rcases Nat.lt_or_ge l 21 with h | h
  · have hu := letterMat_mem_Cm_of_ge (l := l + 21) (by omega) (by omega)
    have hx : rowsMat (letterRows l) = rowsMat candRows[l]! := by
      rw [letterRows, if_pos h]
    have hu' : rowsMat (letterRows (l + 21)) = rowsMat invC[l]! := by
      rw [letterRows, if_neg (by omega), show l + 21 - 21 = l by omega]
    rw [hx]
    rw [hu'] at hu
    have hxu : rowsMat candRows[l]! * rowsMat invC[l]! = 1 := by
      rw [← rowsMat_rowsMul, ← rowsMat_idRows]
      exact rowsMat_congr (invC_check l h)
    have hux : rowsMat invC[l]! * rowsMat candRows[l]! = 1 := (Matrix.mul_eq_one_comm_of_card_eq (R := ZMod 2) (m := Fin 22) (n := Fin 22)
      (eq := rfl)).1 hxu
    let U : M22ˣ := ⟨rowsMat invC[l]!, rowsMat candRows[l]!, hux, hxu⟩
    have : Finite M22ˣ := Finite.of_injective (fun v : M22ˣ => (v : M22)) Units.val_injective
    have hpos := orderOf_pos U
    have hinv : U ^ (orderOf U - 1) = U⁻¹ := by
      apply eq_inv_of_mul_eq_one_left
      rw [← pow_succ, Nat.sub_add_cancel hpos, pow_orderOf_eq_one]
    have hval : rowsMat candRows[l]! = rowsMat invC[l]! ^ (orderOf U - 1) := by
      change ((U⁻¹ : M22ˣ) : M22) = (U : M22) ^ (orderOf U - 1)
      rw [← hinv, Units.val_pow_eq_pow_val]
    rw [hval]
    exact Submonoid.pow_mem _ hu _
  · exact letterMat_mem_Cm_of_ge h hl

theorem wordMat_mem_Cm {w : List ℕ} (hw : ∀ l ∈ w, l < 42) : wordMat w ∈ Cm := by
  rw [wordMat_eq_prod]
  apply Submonoid.list_prod_mem
  intro x hx
  obtain ⟨l, hl, rfl⟩ := List.mem_map.1 hx
  exact letterMat_mem_Cm (hw l hl)

end CFSG.RankThree.Co2

end
