module

public import Certificates.Certificate17026


public section

namespace CFSG.Quasithin.JonesParshall.Curtis

open Matrix

theorem sM_eq_toMat : ∀ s, sM s = toMat (sB s) :=
  Certificates.certificate17026.1

theorem xM_eq_toMat : ∀ s, xM s = toMat (xB s) :=
  Certificates.certificate17026.2.1

theorem yM_eq_toMat : ∀ s, yM s = toMat (yB s) :=
  Certificates.certificate17026.2.2.1

@[expose] def wordProd (l : List (Fin 4)) : G5 := l.foldr (fun s g => sE s * g) 1

theorem wordProd_cons (s : Fin 4) (l : List (Fin 4)) :
    wordProd (s :: l) = sE s * wordProd l := rfl

theorem wordProd_coe (l : List (Fin 4)) :
    (wordProd l : Matrix (Fin 5) (Fin 5) (ZMod 2)) = toMat (bword l) := by
  induction l with
  | nil => exact toMat_bone.symm
  | cons s l ih =>
    change sM s * (wordProd l : Matrix (Fin 5) (Fin 5) (ZMod 2)) = toMat (bmul (sB s) (bword l))
    rw [ih, toMat_bmul, sM_eq_toMat]

theorem wordProd_append (l l' : List (Fin 4)) :
    wordProd (l ++ l') = wordProd l * wordProd l' := by
  induction l with
  | nil => simp [wordProd]
  | cons s l ih => rw [List.cons_append, wordProd_cons, wordProd_cons, ih, mul_assoc]

theorem wordProd_reverse_mul
    (l : List (Fin 4)) : wordProd l.reverse * wordProd l = 1 := by
  induction l with
  | nil => simp [wordProd]
  | cons s l ih =>
    rw [List.reverse_cons, wordProd_append, wordProd_cons s l]
    have e : wordProd [s] = sE s := by simp [wordProd]
    rw [e, mul_assoc, ← mul_assoc (sE s), sE_mul_self, one_mul, ih]

theorem wordProd_inv
    (l : List (Fin 4)) : (wordProd l)⁻¹ = wordProd l.reverse :=
  (eq_inv_of_mul_eq_one_left (wordProd_reverse_mul l)).symm

@[expose] def wE (k : Fin 120) : G5 := wordProd (canW k)

theorem canW_zero : canW 0 = [] := rfl

theorem wE_zero : wE 0 = 1 := rfl

theorem canW_cons : ∀ k : Fin 120, k ≠ 0 → canW k = headS k :: canW (tailIdx k) :=
  Certificates.certificate17026.2.2.2.1

theorem wE_eq_cons
    {k : Fin 120} (hk : k ≠ 0) : wE k = sE (headS k) * wE (tailIdx k) := by
  rw [wE, wE, canW_cons k hk, wordProd_cons]

theorem length_tailIdx {k : Fin 120} (hk : k ≠ 0) :
    (canW (tailIdx k)).length + 1 = (canW k).length := by
  rw [canW_cons k hk, List.length_cons]

theorem sE_mul_wE_bits : ∀ (s : Fin 4) (k : Fin 120),
    bmul (sB s) (bword (canW k)) = bword (canW (mulTab s k)) :=
  Certificates.certificate17026.2.2.2.2.1

theorem sE_mul_wE
    (s : Fin 4) (k : Fin 120) : sE s * wE k = wE (mulTab s k) := by
  apply Subtype.ext
  change sM s * (wordProd (canW k) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
    (wordProd (canW (mulTab s k)) : Matrix (Fin 5) (Fin 5) (ZMod 2))
  rw [wordProd_coe, wordProd_coe, sM_eq_toMat, ← toMat_bmul, sE_mul_wE_bits]

theorem wE_conj_bits : ∀ (k : Fin 120) (s : Fin 4),
    IsUpU (toMat (bmul (bmul (bword (canW k).reverse) (xB s)) (bword (canW k)))) ∨
      IsUpU (toMat (bmul (bmul (bword (canW k).reverse) (yB s)) (bword (canW k)))) :=
  Certificates.certificate17026.2.2.2.2.2.1

theorem conj_coe (l : List (Fin 4)) (g : G5) :
    ((wordProd l.reverse * g * wordProd l : G5) : Matrix (Fin 5) (Fin 5) (ZMod 2)) =
      (wordProd l.reverse : Matrix (Fin 5) (Fin 5) (ZMod 2)) *
        (g : Matrix (Fin 5) (Fin 5) (ZMod 2)) * (wordProd l : Matrix (Fin 5) (Fin 5) (ZMod 2)) :=
  rfl

theorem wE_conj
    (k : Fin 120) (s : Fin 4) :
    (wE k)⁻¹ * xE s * wE k ∈ Ugrp ∨ (wE k)⁻¹ * yE s * wE k ∈ Ugrp := by
  rw [wE, wordProd_inv, mem_Ugrp, mem_Ugrp, conj_coe, conj_coe, wordProd_coe, wordProd_coe]
  change IsUpU (_ * xM s * _) ∨ IsUpU (_ * yM s * _)
  rw [xM_eq_toMat, yM_eq_toMat, ← toMat_bmul, ← toMat_bmul, ← toMat_bmul, ← toMat_bmul]
  exact wE_conj_bits k s

theorem wE_tail_conj_bits : ∀ k : Fin 120, k ≠ 0 →
    IsUpU (toMat (bmul (bmul (bword (canW (tailIdx k)).reverse) (xB (headS k)))
      (bword (canW (tailIdx k))))) :=
  Certificates.certificate17026.2.2.2.2.2.2

theorem wE_tail_conj
    {k : Fin 120} (hk : k ≠ 0) :
    (wE (tailIdx k))⁻¹ * xE (headS k) * wE (tailIdx k) ∈ Ugrp := by
  rw [wE, wordProd_inv, mem_Ugrp, conj_coe, wordProd_coe, wordProd_coe]
  change IsUpU (_ * xM (headS k) * _)
  rw [xM_eq_toMat, ← toMat_bmul, ← toMat_bmul]
  exact wE_tail_conj_bits k hk

end CFSG.Quasithin.JonesParshall.Curtis
