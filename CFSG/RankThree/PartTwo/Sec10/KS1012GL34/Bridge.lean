module

public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Checks
import all CFSG.Fischer.F4
public import CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Defs
public import Mathlib.RingTheory.WittVector.IsPoly
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.Polynomial.Basic
public import Mathlib.Tactic.ReduceModChar
public import Std.Tactic.BVDecide.Normalize.Prop

public section

namespace CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Bridge

open CFSG.Fischer CFSG.RankThree.PartTwo.Sec10.KS1012GL34
open CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Light

def toMat (A : M3) : Matrix (Fin 3) (Fin 3) F4 :=
  !![A.a00, A.a01, A.a02; A.a10, A.a11, A.a12; A.a20, A.a21, A.a22]

def ofMat (M : Matrix (Fin 3) (Fin 3) F4) : M3 :=
  ⟨M 0 0, M 0 1, M 0 2, M 1 0, M 1 1, M 1 2, M 2 0, M 2 1, M 2 2⟩

def vec3 (w : V3) : Fin 3 → F4 := ![w.x, w.y, w.z]

theorem toMat_ofMat (M : Matrix (Fin 3) (Fin 3) F4) : toMat (ofMat M) = M := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, ofMat]

theorem ofMat_toMat (A : M3) : ofMat (toMat A) = A := by
  cases A
  simp [ofMat, toMat]

theorem toMat_injective : Function.Injective toMat := by
  intro A B h
  rw [← ofMat_toMat A, ← ofMat_toMat B, h]

theorem toMat_mulL (A B : M3) : toMat (mulL A B) = toMat A * toMat B := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [toMat, mulL, Matrix.mul_apply, Fin.sum_univ_three] <;> ring

theorem toMat_oneL : toMat oneL = 1 := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, oneL, Matrix.one_apply]

theorem toMat_mulV (A : M3) (w : V3) : Matrix.mulVec (toMat A) (vec3 w) = vec3 (mulV A w) := by
  ext i
  fin_cases i <;> simp [toMat, vec3, mulV, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

theorem smul_vec3 (c : F4) (u : V3) : c • vec3 u = vec3 (smulV c u) := by
  ext i
  fin_cases i <;> simp [vec3, smulV]

theorem vec3_inj (u w : V3) : vec3 u = vec3 w ↔ u = w := by
  constructor
  · intro h
    have h0 := congrFun h 0
    have h1 := congrFun h 1
    have h2 := congrFun h 2
    simp [vec3] at h0 h1 h2
    cases u
    cases w
    simp_all
  · rintro rfl
    rfl

theorem det_toMat (A : M3) : (toMat A).det = detL A := by
  rw [Matrix.det_fin_three]
  simp [toMat, detL, CharTwo.sub_eq_add]
  ring

theorem om2_eq : om2 = ⟨3⟩ := by decide

theorem toMat_XdL : toMat XdL = Xd := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, XdL, Xd, om2_eq, F4.ω]

theorem toMat_ZsL : toMat ZsL = Zs := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, ZsL, Zs, Matrix.one_apply, F4.ω]

theorem toMat_WmL (μ : F4) : toMat (WmL μ) = Wm μ := by
  ext i j
  fin_cases i <;> fin_cases j <;> simp [toMat, WmL, Wm]

theorem NZL_iff : ∀ c : F4, c ∈ NZL ↔ c ≠ 0 := by decide

theorem omega_mem_iff : ∀ (k : Fin 6) (x y z : F4),
    ![x, y, z] ∈ Omega k ↔ ∃ w ∈ omegaL k.val, vec3 w = ![x, y, z] := by
  decide

theorem omega_mem_iff' (k : Fin 6) (v : Fin 3 → F4) :
    v ∈ Omega k ↔ ∃ w ∈ omegaL k.val, vec3 w = v := by
  obtain ⟨x, y, z, rfl⟩ : ∃ x y z : F4, v = ![x, y, z] :=
    ⟨v 0, v 1, v 2, by ext i; fin_cases i <;> rfl⟩
  exact omega_mem_iff k x y z

abbrev elemM (i j : Fin 3) (c : F4) : Matrix (Fin 3) (Fin 3) F4 := 1 + Matrix.single i j c

theorem toMat_E01L : toMat E01L = elemM 0 1 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toMat, E01L, elemM, Matrix.single_apply]

theorem toMat_E02L : toMat E02L = elemM 0 2 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toMat, E02L, elemM, Matrix.single_apply]

theorem toMat_E10L : toMat E10L = elemM 1 0 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toMat, E10L, elemM, Matrix.single_apply]

theorem toMat_E12L : toMat E12L = elemM 1 2 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toMat, E12L, elemM, Matrix.single_apply]

theorem toMat_E20L : toMat E20L = elemM 2 0 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toMat, E20L, elemM, Matrix.single_apply]

theorem toMat_E21L : toMat E21L = elemM 2 1 1 := by
  ext i j; fin_cases i <;> fin_cases j <;> simp [toMat, E21L, elemM, Matrix.single_apply]

theorem allF4_mem (x : F4) : x ∈ allF4 := by
  revert x
  decide

theorem mem_allM3L (A : M3) : A ∈ allM3L () := by
  obtain ⟨a00, a01, a02, a10, a11, a12, a20, a21, a22⟩ := A
  simp only [allM3L, List.mem_flatMap, List.mem_map]
  exact ⟨a00, allF4_mem _, a01, allF4_mem _, a02, allF4_mem _, a10, allF4_mem _, a11,
    allF4_mem _, a12, allF4_mem _, a20, allF4_mem _, a21, allF4_mem _, a22, allF4_mem _, rfl⟩

theorem detL_ofMat (M : Matrix (Fin 3) (Fin 3) F4) : detL (ofMat M) = M.det := by
  rw [← det_toMat, toMat_ofMat]

theorem mem_omega_vec (k : Fin 6) (w : V3) (hw : w ∈ omegaL k.val) : vec3 w ∈ Omega k :=
  (omega_mem_iff' k (vec3 w)).2 ⟨w, hw, rfl⟩

theorem stab_iff (k : Fin 6) (A : M3) : stabilizes k (toMat A) ↔ stabLn k.val A = true := by
  unfold stabLn stabOf
  rw [List.all_eq_true]
  constructor
  · intro h x hx
    obtain ⟨w, hw, rfl⟩ := List.mem_map.1 hx
    obtain ⟨u, hu, c, hc, hmul⟩ := h (vec3 w) (mem_omega_vec k w hw)
    obtain ⟨u', hu', rfl⟩ := (omega_mem_iff' k u).1 hu
    rw [toMat_mulV, smul_vec3, vec3_inj] at hmul
    rw [List.any_eq_true]
    refine ⟨u', hu', ?_⟩
    rw [List.any_eq_true]
    refine ⟨c, (NZL_iff c).2 hc, ?_⟩
    simp [hmul]
  · intro h v hv
    obtain ⟨w, hw, rfl⟩ := (omega_mem_iff' k v).1 hv
    have hx := h (mulV A w) (List.mem_map.2 ⟨w, hw, rfl⟩)
    rw [List.any_eq_true] at hx
    obtain ⟨u, hu, hu2⟩ := hx
    rw [List.any_eq_true] at hu2
    obtain ⟨c, hc, hcx⟩ := hu2
    have hceq : mulV A w = smulV c u := by simpa using hcx
    refine ⟨vec3 u, mem_omega_vec k u hu, c, (NZL_iff c).1 hc, ?_⟩
    rw [toMat_mulV, hceq, smul_vec3]

end CFSG.RankThree.PartTwo.Sec10.KS1012GL34.Bridge

end
