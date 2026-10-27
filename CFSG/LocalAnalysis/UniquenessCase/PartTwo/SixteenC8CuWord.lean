module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuRoot

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

open Matrix

@[expose] def wordProd (l : List (Fin 3)) : G6 := l.foldr (fun s g => sE s * g) 1

@[expose] def bword (l : List (Fin 3)) : BM := l.foldr (fun s M => bmul (sB s) M) bone

theorem wordProd_cons (s : Fin 3) (l : List (Fin 3)) :
    wordProd (s :: l) = sE s * wordProd l := rfl

theorem wordProd_coe (l : List (Fin 3)) : gM (wordProd l) = toMat (bword l) := by
  induction l with
  | nil => exact toMat_bone.symm
  | cons s l ih =>
    change sM s * gM (wordProd l) = toMat (bmul (sB s) (bword l))
    rw [ih, toMat_bmul, sM_eq_toMat]

theorem wordProd_append (l l' : List (Fin 3)) :
    wordProd (l ++ l') = wordProd l * wordProd l' := by
  induction l with
  | nil => simp [wordProd]
  | cons s l ih => rw [List.cons_append, wordProd_cons, wordProd_cons, ih, mul_assoc]

theorem wordProd_reverse_mul (l : List (Fin 3)) : wordProd l.reverse * wordProd l = 1 := by
  induction l with
  | nil => simp [wordProd]
  | cons s l ih =>
    rw [List.reverse_cons, wordProd_append, wordProd_cons s l]
    have e : wordProd [s] = sE s := by simp [wordProd]
    rw [e, mul_assoc, ← mul_assoc (sE s), sE_mul_self, one_mul, ih]

theorem wordProd_inv (l : List (Fin 3)) : (wordProd l)⁻¹ = wordProd l.reverse :=
  (eq_inv_of_mul_eq_one_left (wordProd_reverse_mul l)).symm

@[expose] def rootE : Bool × Fin 3 → G6
  | (true, s) => xE s
  | (false, s) => yE s

@[expose] def rootProd (l : List (Bool × Fin 3)) : G6 := l.foldr (fun a g => rootE a * g) 1

@[expose] def rootB : Bool × Fin 3 → BM
  | (true, s) => xB s
  | (false, s) => yB s

@[expose] def rootBM (l : List (Bool × Fin 3)) : BM := l.foldr (fun a M => bmul (rootB a) M) bone

theorem rootE_mul_self (a : Bool × Fin 3) : rootE a * rootE a = 1 := by
  obtain ⟨b, s⟩ := a
  cases b
  · exact yE_mul_self s
  · exact xE_mul_self s

theorem rootE_coe (a : Bool × Fin 3) : gM (rootE a) = toMat (rootB a) := by
  obtain ⟨b, s⟩ := a
  cases b
  · exact yM_eq_toMat s
  · exact xM_eq_toMat s

theorem rootProd_cons (a : Bool × Fin 3) (l : List (Bool × Fin 3)) :
    rootProd (a :: l) = rootE a * rootProd l := rfl

theorem rootProd_append (l l' : List (Bool × Fin 3)) :
    rootProd (l ++ l') = rootProd l * rootProd l' := by
  induction l with
  | nil => simp [rootProd]
  | cons a l ih => rw [List.cons_append, rootProd_cons, rootProd_cons, ih, mul_assoc]

theorem rootProd_coe (l : List (Bool × Fin 3)) : gM (rootProd l) = toMat (rootBM l) := by
  induction l with
  | nil => exact toMat_bone.symm
  | cons a l ih =>
    change gM (rootE a) * gM (rootProd l) = toMat (bmul (rootB a) (rootBM l))
    rw [ih, toMat_bmul, rootE_coe]

theorem rootProd_reverse_mul (l : List (Bool × Fin 3)) :
    rootProd l.reverse * rootProd l = 1 := by
  induction l with
  | nil => simp [rootProd]
  | cons a l ih =>
    rw [List.reverse_cons, rootProd_append, rootProd_cons a l]
    have e : rootProd [a] = rootE a := by simp [rootProd]
    rw [e, mul_assoc, ← mul_assoc (rootE a), rootE_mul_self, one_mul, ih]

theorem rootProd_inv (l : List (Bool × Fin 3)) : (rootProd l)⁻¹ = rootProd l.reverse :=
  (eq_inv_of_mul_eq_one_left (rootProd_reverse_mul l)).symm

theorem rootProd_mem_Ugrp {l : List (Bool × Fin 3)} (h : IsUpU (toMat (rootBM l))) :
    rootProd l ∈ Ugrp := by
  rw [mem_Ugrp, rootProd_coe]
  exact h

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis
