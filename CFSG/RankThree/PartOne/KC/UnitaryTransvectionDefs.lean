module

public import CFSG.Adapters.ProjectiveSpecialLinear
public import CFSG.LocalAnalysis.ComponentInitial.UnitaryHigherPrimeForm

public section

namespace CFSG.RankThree.PartOne

open Matrix CFSG.LocalAnalysis.ComponentInitial CFSG.LocalAnalysis.ComponentInitial.UnitaryHigher
  CFSG.ClassicalGroups.UnitaryFlag

@[expose] def trvPerm (m : ℕ) : Equiv.Perm (Fin (m + 2)) := Equiv.swap 0 (Fin.last (m + 1))

@[expose] def trvGram (K : Type) [Field K] (m : ℕ) : Matrix (Fin (m + 2)) (Fin (m + 2)) K :=
  Matrix.of fun i j => if j = trvPerm m i then 1 else 0

namespace KCUnitaryTrv

variable {K : Type} [Field K] {m : ℕ}

theorem trvPerm_trvPerm (i : Fin (m + 2)) : trvPerm m (trvPerm m i) = i :=
  Equiv.swap_apply_self _ _ _

theorem trvPerm_zero : trvPerm m 0 = Fin.last (m + 1) := Equiv.swap_apply_left _ _

theorem trvPerm_last : trvPerm m (Fin.last (m + 1)) = 0 := Equiv.swap_apply_right _ _

theorem trvPerm_of_mid {i : Fin (m + 2)} (h0 : i ≠ 0) (hL : i ≠ Fin.last (m + 1)) :
    trvPerm m i = i := Equiv.swap_apply_of_ne_of_ne h0 hL

theorem zero_ne_last : (0 : Fin (m + 2)) ≠ Fin.last (m + 1) := by
  intro e
  have := congrArg Fin.val e
  simp at this

theorem trvGram_apply (i j : Fin (m + 2)) :
    trvGram K m i j = if j = trvPerm m i then 1 else 0 := rfl

theorem trvGram_one : trvGram K 1 = !![0, 0, 1; 0, 1, 0; 1, 0, 0] := by
  ext i j
  rw [trvGram_apply]
  fin_cases i <;> fin_cases j <;>
    simp [trvPerm, Equiv.swap_apply_def, Fin.ext_iff, Fin.last]

theorem trvGram_two : trvGram K 2 = !![0, 0, 0, 1; 0, 1, 0, 0; 0, 0, 1, 0; 1, 0, 0, 0] := by
  ext i j
  rw [trvGram_apply]
  fin_cases i <;> fin_cases j <;>
    simp [trvPerm, Equiv.swap_apply_def, Fin.ext_iff, Fin.last]

theorem trvGram_mulVec (x : Fin (m + 2) → K) :
    trvGram K m *ᵥ x = fun i => x (trvPerm m i) := by
  funext i
  simp [mulVec, dotProduct, trvGram_apply]

theorem trvGram_transpose : (trvGram K m)ᵀ = trvGram K m := by
  ext i j
  simp only [transpose_apply, trvGram_apply]
  have hiff : (j = trvPerm m i) ↔ (i = trvPerm m j) :=
    ⟨fun e => by rw [e, trvPerm_trvPerm], fun e => by rw [e, trvPerm_trvPerm]⟩
  simp only [hiff]

theorem trvGram_mul_self : trvGram K m * trvGram K m = 1 := by
  ext i j
  simp only [mul_apply, trvGram_apply, one_apply]
  rw [Finset.sum_eq_single (trvPerm m i)]
  · simp [trvPerm_trvPerm, eq_comm]
  · intro k _ hk
    simp [hk]
  · simp

abbrev trvGL (K : Type) [Field K] (m : ℕ) : GL (Fin (m + 2)) K :=
  ⟨trvGram K m, trvGram K m, trvGram_mul_self, trvGram_mul_self⟩

theorem coe_trvGL : ((trvGL K m : GL (Fin (m + 2)) K) : Matrix (Fin (m + 2)) (Fin (m + 2)) K) =
    trvGram K m := rfl

theorem isPrimeFormGram_trv : IsPrimeFormGram (trvGL K m) := by
  refine ⟨by rw [coe_trvGL]; exact trvGram_transpose, fun i j => ?_⟩
  rw [coe_trvGL, trvGram_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

variable {p f : ℕ} (h : UnitaryFieldData p f K)

theorem gramForm_trv (x y : Fin (m + 2) → K) :
    gramForm h (trvGram K m) x y = ∑ i, h.bar (x i) * y (trvPerm m i) := by
  rw [gramForm_apply, trvGram_mulVec]
  rfl

theorem gramForm_trv_single_left (a : Fin (m + 2)) (y : Fin (m + 2) → K) :
    gramForm h (trvGram K m) (Pi.single a 1) y = y (trvPerm m a) := by
  rw [gramForm_trv, Finset.sum_eq_single a]
  · simp
  · intro b _ hb
    simp [hb]
  · simp

end KCUnitaryTrv

end CFSG.RankThree.PartOne
