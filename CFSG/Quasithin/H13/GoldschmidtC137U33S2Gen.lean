module

public import CFSG.Quasithin.Vol2.Ch3Sec3G2Data

public section

namespace CFSG.Quasithin.H13.U3.GC137.S2

open CFSG.Open CFSG.Quasithin CFSG.Quasithin.H13 CFSG.Quasithin.H13.Orbit
  CFSG.Quasithin.H13.G2Dat

abbrev Gam : Type := ↥(quasithinG2 (ZMod 2))

@[expose] def zT01G : Gam := ⟨zT01, mem_quasithinG2 zT01_mul⟩

@[expose] def bgen (j : ℕ) : Gam :=
  if j = 0 then zT01G else if j = 1 then zT10G else if j = 2 then zXG else zTauG

@[expose] def bcode (j : ℕ) : List ℕ :=
  if j = 0 then matT01 else if j = 1 then matT10 else if j = 2 then matX else matTau

theorem matCode_bgen {j : ℕ} (hj : j < 4) : matCode (bgen j).1 = bcode j := by
  interval_cases j
  · exact matCode_zT01
  · exact matCode_zT10
  · exact matCode_zX
  · exact matCode_zTau

@[expose] def wd (w : List ℕ) : Gam := w.foldl (fun g j => g * bgen j) 1

@[expose] def wcode (w : List ℕ) : List ℕ := w.foldl (fun m j => mmul m (bcode j)) idMat

theorem wd_foldl (w : List ℕ) (g : Gam) : w.foldl (fun g j => g * bgen j) g = g * wd w := by
  induction w generalizing g with
  | nil => simp [wd]
  | cons j w ih =>
    have h2 : wd (j :: w) = bgen j * wd w := by
      rw [wd, List.foldl_cons, one_mul, ih (bgen j)]
    rw [List.foldl_cons, ih, h2, mul_assoc]

theorem wd_append (a b : List ℕ) : wd (a ++ b) = wd a * wd b := by
  unfold wd
  rw [List.foldl_append, wd_foldl]
  rfl

theorem matCode_foldl_wd (w : List ℕ) (hw : ∀ j ∈ w, j < 4) (g : Gam) :
    matCode (w.foldl (fun g j => g * bgen j) g).1 =
      w.foldl (fun m j => mmul m (bcode j)) (matCode g.1) := by
  induction w generalizing g with
  | nil => rfl
  | cons j w ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (fun k hk => hw k (List.mem_cons_of_mem _ hk)),
      matCode_mulG, matCode_bgen (hw j List.mem_cons_self)]

theorem matCode_wd {w : List ℕ} (hw : ∀ j ∈ w, j < 4) : matCode (wd w).1 = wcode w := by
  rw [wd, wcode, matCode_foldl_wd w hw, show (1 : Gam).1 = 1 from rfl, matCode_one]

@[expose] def gprod (gl : List Gam) (w : List ℕ) : Gam := w.foldl (fun g j => g * gl.getD j 1) 1

@[expose] def gcode (cl : List (List ℕ)) (w : List ℕ) : List ℕ :=
  w.foldl (fun m j => mmul m (cl.getD j [])) idMat

theorem gprod_foldl_mem {H : Subgroup Gam} {gl : List Gam} (h : ∀ x ∈ gl, x ∈ H) (w : List ℕ)
    {g : Gam} (hg : g ∈ H) : w.foldl (fun g j => g * gl.getD j 1) g ∈ H := by
  induction w generalizing g with
  | nil => exact hg
  | cons j w ih =>
    rw [List.foldl_cons]
    refine ih (mul_mem hg ?_)
    by_cases hj : j < gl.length
    · rw [List.getD_eq_getElem _ _ hj]
      exact h _ (List.getElem_mem hj)
    · rw [List.getD_eq_default _ _ (by omega)]
      exact one_mem H

theorem gprod_mem {H : Subgroup Gam} {gl : List Gam} (h : ∀ x ∈ gl, x ∈ H) (w : List ℕ) :
    gprod gl w ∈ H :=
  gprod_foldl_mem h w (one_mem H)

theorem matCode_gprod_foldl (gl : List Gam) (w : List ℕ) (hw : ∀ j ∈ w, j < gl.length) (g : Gam) :
    matCode (w.foldl (fun g j => g * gl.getD j 1) g).1 =
      w.foldl (fun m j => mmul m ((gl.map fun x => matCode x.1).getD j [])) (matCode g.1) := by
  induction w generalizing g with
  | nil => rfl
  | cons j w ih =>
    rw [List.foldl_cons, List.foldl_cons, ih (fun k hk => hw k (List.mem_cons_of_mem _ hk)),
      matCode_mulG]
    have hj := hw j List.mem_cons_self
    rw [List.getD_eq_getElem _ _ hj, List.getD_eq_getElem _ _ (by simpa using hj)]
    simp

theorem matCode_gprod (gl : List Gam) (w : List ℕ) (hw : ∀ j ∈ w, j < gl.length) :
    matCode (gprod gl w).1 = gcode (gl.map fun x => matCode x.1) w := by
  rw [gprod, gcode, matCode_gprod_foldl gl w hw, show (1 : Gam).1 = 1 from rfl, matCode_one]

end CFSG.Quasithin.H13.U3.GC137.S2
