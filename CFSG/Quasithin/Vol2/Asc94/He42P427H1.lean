module

public import CFSG.Quasithin.Vol2.Asc94.He42SE4
public import CFSG.Quasithin.Vol2.Asc94.HeM2

public section

namespace CFSG.Quasithin.A94.He42P427H

open CFSG.Quasithin.A94.L52 Matrix

@[expose] def Xm (r0 r1 r2 s a b e k0 k1 : ZMod 2) : Mt :=
  !![1, r0, r1, r2, s; 0, 1, a, b, k0; 0, 0, 1, e, k1; 0, 0, 0, 1, r0; 0, 0, 0, 0, 1]

theorem Xm_lower (r0 r1 r2 s a b e k0 k1 : ZMod 2) (i j : Fin 5) (hij : j < i) :
    Xm r0 r1 r2 s a b e k0 k1 i j = 0 := by
  fin_cases i <;> fin_cases j <;> simp_all [Xm]

theorem Xm_det (r0 r1 r2 s a b e k0 k1 : ZMod 2) : (Xm r0 r1 r2 s a b e k0 k1).det = 1 := by
  rw [Matrix.det_of_isUpperTriangular (fun i j hij => Xm_lower r0 r1 r2 s a b e k0 k1 i j hij)]
  simp [Xm, Fin.prod_univ_five]

theorem Xm_comm (r0 r1 r2 s a b e k0 k1 : ZMod 2) :
    Xm r0 r1 r2 s a b e k0 k1 * tt = tt * Xm r0 r1 r2 s a b e k0 k1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Xm, tt, Matrix.mul_apply, Fin.sum_univ_five,
    Matrix.one_apply, Matrix.single_apply] <;> ring

@[expose] def SXm (r0 r1 r2 s a b e k0 k1 : ZMod 2) : Matrix.SpecialLinearGroup (Fin 5) (ZMod 2) :=
  ⟨Xm r0 r1 r2 s a b e k0 k1, Xm_det r0 r1 r2 s a b e k0 k1⟩

theorem SXm_mem (r0 r1 r2 s a b e k0 k1 : ZMod 2) :
    SXm r0 r1 r2 s a b e k0 k1 ∈ CFSG.CGT.M24S.tCent := by
  show SXm r0 r1 r2 s a b e k0 k1 ∈ Subgroup.centralizer
    ({CFSG.Quasithin.H13.transvection15} : Set (Matrix.SpecialLinearGroup (Fin 5) (ZMod 2)))
  rw [Subgroup.mem_centralizer_singleton_iff]
  apply Subtype.ext
  simp only [Matrix.SpecialLinearGroup.coe_mul]
  rw [coe_tt]
  exact Xm_comm r0 r1 r2 s a b e k0 k1

@[expose] def Phi' (r0 r1 r2 s a b e k0 k1 : ZMod 2) : Hc :=
  ⟨SXm r0 r1 r2 s a b e k0 k1, SXm_mem r0 r1 r2 s a b e k0 k1⟩

@[expose] def Phi (p : Fin 9 → ZMod 2) : Hc :=
  Phi' (p 0) (p 1) (p 2) (p 3) (p 4) (p 5) (p 6) (p 7) (p 8)

@[expose] def prm (x : Hc) : Fin 9 → ZMod 2 :=
  ![cm x 0 1, cm x 0 2, cm x 0 3, cm x 0 4, cm x 1 2, cm x 1 3, cm x 2 3, cm x 1 4, cm x 2 4]

theorem cm_Phi' (r0 r1 r2 s a b e k0 k1 : ZMod 2) :
    cm (Phi' r0 r1 r2 s a b e k0 k1) = Xm r0 r1 r2 s a b e k0 k1 := rfl

theorem prm_Phi (p : Fin 9 → ZMod 2) : prm (Phi p) = p := by
  funext i
  fin_cases i <;> simp only [prm, Phi, cm_Phi'] <;> simp [Xm]

@[expose] def abar : Hc := Phi ![0, 0, 1, 0, 0, 0, 0, 1, 0]

theorem cm_abar : cm abar = !![1, 0, 0, 1, 0; 0, 1, 0, 0, 1; 0, 0, 1, 0, 0; 0, 0, 0, 1, 0; 0, 0, 0, 0, 1] := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp only [abar, Phi, cm_Phi'] <;> simp [Xm]

end CFSG.Quasithin.A94.He42P427H
