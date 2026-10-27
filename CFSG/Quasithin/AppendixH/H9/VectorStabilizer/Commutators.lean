module

public import CFSG.Quasithin.AppendixH.H9.VectorStabilizer.Action
public import CFSG.Quasithin.AppendixH.H9.VectorStabilizer.Model
public import CFSG.Quasithin.AppendixH.H9.VectorStabilizer.Hyperplane
public import CFSG.Quasithin.AppendixH.H9.GLBasics

public section

open scoped Matrix

namespace CFSG.ASVolI.ChH.VectorStabilizer

open CFSG.Quasithin CFSG.Open

variable {m : ℕ}

private theorem exists_ne_zero_ne_pair (hm : 2 ≤ m) (s : Fin m → ZMod 2) :
    ∃ r₀ : Fin m → ZMod 2, r₀ ≠ 0 ∧ r₀ ≠ s := by
  let i0 : Fin m := ⟨0, by omega⟩
  let i1 : Fin m := ⟨1, by omega⟩
  have h01 : i0 ≠ i1 := by
    intro h
    have := congrArg Fin.val h
    simp [i0, i1] at this
  have he0 : (Pi.single i0 (1 : ZMod 2) : Fin m → ZMod 2) ≠ 0 := by
    intro h
    have := congrFun h i0
    simp at this
  have he1 : (Pi.single i1 (1 : ZMod 2) : Fin m → ZMod 2) ≠ 0 := by
    intro h
    have := congrFun h i1
    simp at this
  have he01 : (Pi.single i0 (1 : ZMod 2) : Fin m → ZMod 2) ≠ Pi.single i1 1 := by
    intro h
    have := congrFun h i0
    simp [Pi.single_apply, h01] at this
  by_cases hs : s = Pi.single i0 1
  · exact ⟨Pi.single i1 1, he1, fun h => he01 (hs ▸ h.symm)⟩
  · exact ⟨Pi.single i0 1, he0, fun h => hs h.symm⟩

private theorem zmod2_add_add (a b : ZMod 2) : a + (a + b) = b := by
  revert a b
  decide

private theorem exists_x_ne (hm : 2 ≤ m) (c' : Fin m → ZMod 2) :
    ∃ x' : Fin m → ZMod 2, x' ≠ 0 ∧ x' + c' ≠ 0 := by
  obtain ⟨x', h1, h2⟩ := exists_ne_zero_ne_pair hm c'
  refine ⟨x', h1, fun h => h2 ?_⟩
  have h3 : x' + c' + c' = c' := by rw [h, zero_add]
  rw [add_assoc, add_self_vec, add_zero] at h3
  exact h3

theorem exists_mulVec_add_eq (hm : 2 ≤ m) (c : Fin (m + 1) → ZMod 2) :
    ∃ A ∈ stabGL m, ∃ x : Fin (m + 1) → ZMod 2,
      (A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ x + x = c := by
  obtain ⟨x', hx', hy'⟩ := exists_x_ne hm (fun j : Fin m => c j.succ)
  obtain ⟨B, hB⟩ := exists_GL_mulVec_eq hx' hy'
  obtain ⟨k, hk⟩ : ∃ k, x' k ≠ 0 := by
    by_contra h
    exact hx' (funext fun i => by_contra fun hi => h ⟨i, hi⟩)
  let r : Fin m → ZMod 2 := fun j => if j = k then c 0 else 0
  have hr : r ⬝ᵥ x' = c 0 := by
    have hk1 : x' k = 1 := by
      revert hk
      generalize x' k = a
      revert a
      decide
    simp [r, dotProduct, ite_mul, hk1]
  refine ⟨blockGL r B, blockGL_mem_stabGL r B, Matrix.vecCons 0 x', ?_⟩
  funext i
  induction i using Fin.cases with
  | zero =>
    simp [blockGL_val, blockMat_mulVec_zero, hr]
  | succ j =>
    simp [blockGL_val, blockMat_mulVec_succ, hB, add_comm, zmod2_add_add]

theorem exists_dual_mulVec_add_eq (hm : 2 ≤ m) (c : Fin (m + 1) → ZMod 2) (hc : c 0 = 0) :
    ∃ A ∈ stabGL m, ∃ b : Fin (m + 1) → ZMod 2, b 0 = 0 ∧
      ((dualGLn (m + 1) A : GL (Fin (m + 1)) (ZMod 2)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ b + b = c := by
  obtain ⟨x', hx', hy'⟩ := exists_x_ne hm (fun j : Fin m => c j.succ)
  obtain ⟨X, hX⟩ := exists_GL_mulVec_eq hx' hy'
  refine ⟨leviHom m (dualGLn m X), leviHom_mem _, Matrix.vecCons 0 x', by simp, ?_⟩
  funext i
  induction i using Fin.cases with
  | zero =>
    simp [dualGLn_stabGL_mulVec_zero (leviHom_mem (dualGLn m X)), hc]
  | succ j =>
    have h := dualGLn_stabGL_mulVec_succ (leviHom_mem (dualGLn m X)) (Matrix.vecCons 0 x') j
    rw [blockHom_leviHom, dualGLn_dualGLn] at h
    simp [h, hX, add_comm, zmod2_add_add]


private theorem comm_gen_V1 (A : GL (Fin (m + 1)) (ZMod 2)) (x₀ : Fin (m + 1) → ZMod 2) :
    (pairActN (m + 1) A) (pairVec x₀ 0) * (pairVec x₀ 0)⁻¹ =
      pairVec ((A : Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ x₀ + x₀) 0 := by
  rw [pairActN_pairVec, Matrix.mulVec_zero, pairVec_inv, pairVec_mul]
  simp

private theorem comm_gen_V2 (A : GL (Fin (m + 1)) (ZMod 2)) (b : Fin (m + 1) → ZMod 2) :
    (pairActN (m + 1) A) (pairVec 0 b) * (pairVec 0 b)⁻¹ =
      pairVec 0 ((((dualGLn (m + 1) A : GL (Fin (m + 1)) (ZMod 2)) :
        Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ b) + b) := by
  rw [pairActN_pairVec, Matrix.mulVec_zero, pairVec_inv, pairVec_mul]
  simp

theorem commOn_V1n_Cv (hm : 2 ≤ m) :
    commOn (V1n (m + 1)) (Lg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0))) =
      V1n (m + 1) := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨a, ha, w, hw, rfl⟩
    have haL : a ∈ Lg (m + 1) := (Subgroup.mem_inf.mp ha).1
    have haw : a w ∈ V1n (m + 1) := ((Lg_le_stabSub_V1n haL) w).mpr hw
    exact (V1n (m + 1)).mul_mem haw ((V1n (m + 1)).inv_mem hw)
  · intro x hx
    obtain ⟨a, b, rfl⟩ := pairVec_surj x
    have hb : b = 0 := by
      have h2 : (pairVec a b).2 = 1 := mem_V1n.mp hx
      change Multiplicative.ofAdd b = 1 at h2
      simpa using h2
    subst hb
    obtain ⟨A, hA, x₀, hx₀⟩ := exists_mulVec_add_eq hm a
    apply Subgroup.subset_closure
    exact ⟨pairActN (m + 1) A, mem_Lg_inf_centSub_iff.mpr ⟨A, hA, rfl⟩, pairVec x₀ 0,
      pairVec_mem_V1n x₀, ((comm_gen_V1 A x₀).trans (by rw [hx₀])).symm⟩

theorem commOn_V2n_Cv (hm : 2 ≤ m) :
    commOn (V2n (m + 1)) (Lg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0))) =
      V2n (m + 1) ⊓ perpN (m + 1) (Subgroup.zpowers (pairVec (ez m) 0)) := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr ?_
    rintro _ ⟨a, ha, w, hw, rfl⟩
    obtain ⟨A, hA, rfl⟩ := mem_Lg_inf_centSub_iff.mp ha
    obtain ⟨a0, b, rfl⟩ := pairVec_surj w
    have ha0 : a0 = 0 := by
      have h2 : (pairVec a0 b).1 = 1 := mem_V2n.mp hw
      change Multiplicative.ofAdd a0 = 1 at h2
      simpa using h2
    subst ha0
    show (pairActN (m + 1) A) (pairVec 0 b) * (pairVec 0 b)⁻¹ ∈
      V2n (m + 1) ⊓ perpN (m + 1) (Subgroup.zpowers (pairVec (ez m) 0))
    rw [comm_gen_V2]
    refine (mem_V2n_perpN_iff _).mpr ⟨?_, ?_⟩
    · rfl
    · show ((((dualGLn (m + 1) A : GL (Fin (m + 1)) (ZMod 2)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) *ᵥ b) + b) 0 = 0
      rw [Pi.add_apply, dualGLn_stabGL_mulVec_zero hA]
      exact CharTwo.add_self_eq_zero _
  · intro x hx
    obtain ⟨hx1, hx2⟩ := (mem_V2n_perpN_iff x).mp hx
    obtain ⟨a, c, rfl⟩ := pairVec_surj x
    have ha : a = 0 := by
      change Multiplicative.ofAdd a = 1 at hx1
      simpa using hx1
    subst ha
    have hc0 : c 0 = 0 := hx2
    obtain ⟨A, hA, b, hb0, hbc⟩ := exists_dual_mulVec_add_eq hm c hc0
    apply Subgroup.subset_closure
    exact ⟨pairActN (m + 1) A, mem_Lg_inf_centSub_iff.mpr ⟨A, hA, rfl⟩, pairVec 0 b,
      pairVec_mem_V2n b, ((comm_gen_V2 A b).trans (by rw [hbc])).symm⟩

end CFSG.ASVolI.ChH.VectorStabilizer
