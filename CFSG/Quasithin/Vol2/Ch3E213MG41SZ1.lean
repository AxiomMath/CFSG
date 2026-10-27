module

public import CFSG.Quasithin.Vol2.Ch3E213MSp4Irr

public section

namespace CFSG.Quasithin.Ch3E213M.G41.CTwo

open CFSG.ComponentClassification.UnbalancedCatalog.SpChain
  (antiSp glMat uMat uElt antiSp_ext uMat_zero antiUnipotent mem_antiUnipotent_iff_upper
    mem_antiSp transpose_mul_minorJ_mul_apply minorJ_apply)

variable {k : Type} [Field k]

theorem mul_uMat_center_apply (M : Matrix (Fin 4) (Fin 4) k) (b c : k) (i : Fin 4) :
    (M * uMat 0 b c 0) i 2 = M i 0 * b + M i 2 ∧
      (M * uMat 0 b c 0) i 3 = M i 0 * c + M i 1 * b + M i 3 := by
  constructor <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem uMat_center_mul_apply (M : Matrix (Fin 4) (Fin 4) k) (b c : k) (j : Fin 4) :
    (uMat 0 b c 0 * M) 0 j = M 0 j + b * M 2 j + c * M 3 j ∧
      (uMat 0 b c 0 * M) 1 j = M 1 j + b * M 3 j ∧ (uMat 0 b c 0 * M) 2 j = M 2 j ∧
        (uMat 0 b c 0 * M) 3 j = M 3 j := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem sp_apply (g : antiSp k) (i j : Fin 4) :
    glMat (g : GL (Fin 4) k) 0 i * glMat (g : GL (Fin 4) k) 3 j +
        glMat (g : GL (Fin 4) k) 1 i * glMat (g : GL (Fin 4) k) 2 j +
        glMat (g : GL (Fin 4) k) 2 i * glMat (g : GL (Fin 4) k) 1 j +
        glMat (g : GL (Fin 4) k) 3 i * glMat (g : GL (Fin 4) k) 0 j =
      if i.val + j.val = 3 then 1 else 0 := by
  have h := congrFun (congrFun (mem_antiSp.mp g.2) i) j
  rwa [transpose_mul_minorJ_mul_apply, minorJ_apply] at h

theorem uMat_mul_apply (M : Matrix (Fin 4) (Fin 4) k) (a b c d : k) (j : Fin 4) :
    (uMat a b c d * M) 0 j = M 0 j + a * M 1 j + b * M 2 j + c * M 3 j ∧
      (uMat a b c d * M) 1 j = M 1 j + d * M 2 j + (b + a * d) * M 3 j ∧
        (uMat a b c d * M) 2 j = M 2 j + a * M 3 j ∧ (uMat a b c d * M) 3 j = M 3 j := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_four]

theorem mul_uMat_apply (M : Matrix (Fin 4) (Fin 4) k) (a b c d : k) (i : Fin 4) :
    (M * uMat a b c d) i 0 = M i 0 ∧ (M * uMat a b c d) i 1 = M i 0 * a + M i 1 := by
  constructor <;> simp [uMat, Matrix.mul_apply, Fin.sum_univ_four]

section CharTwo

variable [CharP k 2]

theorem mem_antiUnipotent_of_comm {b c : k} (hb : b ≠ 0) (hc : c ≠ 0) {g : antiSp k}
    (hg : g * uElt 0 b c 0 = uElt 0 b c 0 * g) : g ∈ antiUnipotent k := by
  have h2 : (2 : k) = 0 := CharTwo.two_eq_zero
  have hm : glMat (g : GL (Fin 4) k) * uMat 0 b c 0 = uMat 0 b c 0 * glMat (g : GL (Fin 4) k) :=
    congrArg (fun x : antiSp k => glMat (x : GL (Fin 4) k)) hg
  have s02 : _ = (0 : k) := sp_apply g 0 2
  have s03 : _ = (1 : k) := sp_apply g 0 3
  have s12 : _ = (1 : k) := sp_apply g 1 2
  have s13 : _ = (0 : k) := sp_apply g 1 3
  set M := glMat (g : GL (Fin 4) k) with hM
  have E : ∀ i j, (M * uMat 0 b c 0) i j = (uMat 0 b c 0 * M) i j := fun i j => by rw [hm]
  have L := mul_uMat_center_apply M b c
  have R := uMat_center_mul_apply M b c
  have e22 := E 2 2
  rw [(L 2).1, (R 2).2.2.1] at e22
  have e32 := E 3 2
  rw [(L 3).1, (R 2).2.2.2] at e32
  have e23 := E 2 3
  rw [(L 2).2, (R 3).2.2.1] at e23
  have e33 := E 3 3
  rw [(L 3).2, (R 3).2.2.2] at e33
  have e12 := E 1 2
  rw [(L 1).1, (R 2).2.1] at e12
  have e02 := E 0 2
  rw [(L 0).1, (R 2).1] at e02
  have e13 := E 1 3
  rw [(L 1).2, (R 3).2.1] at e13
  have e03 := E 0 3
  rw [(L 0).2, (R 3).1] at e03
  have m20 : M 2 0 = 0 :=
    (mul_eq_zero.mp (by linear_combination e22 : M 2 0 * b = 0)).resolve_right hb
  have m30 : M 3 0 = 0 :=
    (mul_eq_zero.mp (by linear_combination e32 : M 3 0 * b = 0)).resolve_right hb
  have m21 : M 2 1 = 0 :=
    (mul_eq_zero.mp (by linear_combination e23 - c * m20 : M 2 1 * b = 0)).resolve_right hb
  have m31 : M 3 1 = 0 :=
    (mul_eq_zero.mp (by linear_combination e33 - c * m30 : M 3 1 * b = 0)).resolve_right hb
  have m10 : M 1 0 = M 3 2 := sub_eq_zero.mp
    ((mul_eq_zero.mp (by linear_combination e12 : (M 1 0 - M 3 2) * b = 0)).resolve_right hb)
  have m32 : M 3 2 = 0 := by
    have h1 : c * (M 3 2 * M 3 2) = 0 := by
      linear_combination (-(M 3 2)) * e02 + b * s02 - b * M 1 2 * m20 - b * M 0 2 * m30 -
        b * M 2 2 * m10 - b * M 2 2 * M 3 2 * h2
    exact mul_self_eq_zero.mp ((mul_eq_zero.mp h1).resolve_left hc)
  have m10' : M 1 0 = 0 := m10.trans m32
  have d02 : M 0 0 = M 2 2 := sub_eq_zero.mp ((mul_eq_zero.mp
    (by linear_combination e02 + c * m32 : (M 0 0 - M 2 2) * b = 0)).resolve_right hb)
  have d13 : M 1 1 = M 3 3 := sub_eq_zero.mp ((mul_eq_zero.mp
    (by linear_combination e13 - c * m10' : (M 1 1 - M 3 3) * b = 0)).resolve_right hb)
  have h11 : M 1 1 * M 2 2 = 1 := by
    linear_combination s12 - M 0 1 * m32 - M 1 2 * m21 - M 0 2 * m31
  have h0123 : M 0 1 + M 2 3 = 0 := by
    have h1 : M 1 1 * (M 0 1 + M 2 3) = 0 := by
      linear_combination s13 + M 0 1 * d13 - M 1 3 * m21 - M 0 3 * m31
    exact (mul_eq_zero.mp h1).resolve_left (left_ne_zero_of_mul_eq_one h11)
  have d03 : M 0 0 = M 3 3 := sub_eq_zero.mp ((mul_eq_zero.mp
    (by linear_combination e03 - b * h0123 + b * M 2 3 * h2 :
      (M 0 0 - M 3 3) * c = 0)).resolve_right hc)
  have m00 : M 0 0 = 1 := by
    have h1 : (M 0 0 - 1) * (M 0 0 - 1) = 0 := by
      linear_combination s03 + M 0 0 * d03 - M 2 3 * m10' - M 1 3 * m20 - M 0 3 * m30 +
        (1 - M 0 0) * h2
    exact sub_eq_zero.mp (mul_self_eq_zero.mp h1)
  have m22 : M 2 2 = 1 := d02.symm.trans m00
  have m33 : M 3 3 = 1 := d03.symm.trans m00
  have m11 : M 1 1 = 1 := d13.trans m33
  refine (mem_antiUnipotent_iff_upper g).mpr ⟨fun i j hij => ?_, fun i => ?_⟩
  · fin_cases i <;> fin_cases j <;> first | exact absurd hij (by decide) | assumption
  · fin_cases i <;> assumption

theorem eq_one_of_mul_eq_mul {g u v : antiSp k} (hg : IsOppStd g) (hu : u ∈ antiUnipotent k)
    (hv : v ∈ antiUnipotent k) (h : u * g = g * v) : u = 1 := by
  obtain ⟨a, b, c, d, rfl⟩ := hu
  obtain ⟨a', b', c', d', rfl⟩ := hv
  have hm : uMat a b c d * glMat (g : GL (Fin 4) k) =
      glMat (g : GL (Fin 4) k) * uMat a' b' c' d' :=
    congrArg (fun x : antiSp k => glMat (x : GL (Fin 4) k)) h
  obtain ⟨h30, hdet⟩ := hg
  set G := glMat (g : GL (Fin 4) k) with hG
  have E : ∀ i j, (uMat a b c d * G) i j = (G * uMat a' b' c' d') i j := fun i j => by rw [hm]
  have L := uMat_mul_apply G a b c d
  have R := mul_uMat_apply G a' b' c' d'
  have e20 := E 2 0
  rw [(L 0).2.2.1, (R 2).1] at e20
  have e31 := E 3 1
  rw [(L 1).2.2.2, (R 3).2] at e31
  have e10 := E 1 0
  rw [(L 0).2.1, (R 1).1] at e10
  have e11 := E 1 1
  rw [(L 1).2.1, (R 1).2] at e11
  have e00 := E 0 0
  rw [(L 0).1, (R 0).1] at e00
  have e01 := E 0 1
  rw [(L 1).1, (R 0).2] at e01
  have ha : a = 0 := (mul_eq_zero.mp (by linear_combination e20 : a * G 3 0 = 0)).resolve_right h30
  have ha' : a' = 0 :=
    (mul_eq_zero.mp (by linear_combination -e31 : G 3 0 * a' = 0)).resolve_left h30
  subst ha ha'
  have hd : d = 0 := (mul_eq_zero.mp (by linear_combination G 3 1 * e10 - G 3 0 * e11 :
    d * (G 2 0 * G 3 1 - G 2 1 * G 3 0) = 0)).resolve_right hdet
  have hb : b = 0 := (mul_eq_zero.mp (by linear_combination G 3 1 * e00 - G 3 0 * e01 :
    b * (G 2 0 * G 3 1 - G 2 1 * G 3 0) = 0)).resolve_right hdet
  subst hd hb
  have hc : c = 0 := (mul_eq_zero.mp (by linear_combination e00 : c * G 3 0 = 0)).resolve_right h30
  subst hc
  exact antiSp_ext uMat_zero

end CharTwo

end CFSG.Quasithin.Ch3E213M.G41.CTwo
