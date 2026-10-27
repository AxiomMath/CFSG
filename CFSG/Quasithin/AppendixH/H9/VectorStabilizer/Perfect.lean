module

public import CFSG.Quasithin.AppendixH.H9.VectorStabilizer.Model
public import CFSG.Quasithin.AppendixH.H9.GLBasics

public section

open scoped Matrix commutatorElement

namespace CFSG.ASVolI.ChH.VectorStabilizer

open CFSG.Quasithin CFSG.Open

variable {m : ℕ}

private theorem blockGL_eq_levi_mul_tr (r : Fin m → ZMod 2) (B : GL (Fin m) (ZMod 2)) :
    blockGL r B = leviHom m B * trHom m (Multiplicative.ofAdd r) := by
  rw [leviHom_apply, trHom_apply, blockGL_mul]
  simp

private theorem leviHom_mem_commutator (hm : 3 ≤ m) (B : GL (Fin m) (ZMod 2)) :
    leviHom m B ∈ ⁅stabGL m, stabGL m⁆ := by
  haveI := isPerfect_GL_two hm
  let T : Subgroup (GL (Fin m) (ZMod 2)) := ⊤
  have h1 : B ∈ ⁅T, T⁆ := by
    have h := (Group.isPerfect_def.mp inferInstance :
      commutator (GL (Fin m) (ZMod 2)) = (⊤ : Subgroup (GL (Fin m) (ZMod 2))))
    rw [commutator_def] at h
    rw [h]
    trivial
  have h2 : leviHom m B ∈ (⁅T, T⁆).map (leviHom m) :=
    Subgroup.mem_map_of_mem _ h1
  rw [Subgroup.map_commutator] at h2
  have hle : T.map (leviHom m) ≤ stabGL m := by
    rintro _ ⟨B, -, rfl⟩
    exact leviHom_mem B
  exact Subgroup.commutator_mono hle hle h2

private theorem exists_ne_zero_ne (hm : 2 ≤ m) (s : Fin m → ZMod 2) :
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

private theorem trHom_mem_commutator (hm : 2 ≤ m) (r : Multiplicative (Fin m → ZMod 2)) :
    trHom m r ∈ ⁅stabGL m, stabGL m⁆ := by
  obtain ⟨r₀, hr₀, hr₀s⟩ := exists_ne_zero_ne hm (Multiplicative.toAdd r)
  have hr₁ : r₀ + Multiplicative.toAdd r ≠ 0 := by
    intro h
    apply hr₀s
    have h2 : r₀ + Multiplicative.toAdd r + Multiplicative.toAdd r = Multiplicative.toAdd r := by
      rw [h, zero_add]
    rw [add_assoc, add_self_vec, add_zero] at h2
    exact h2
  obtain ⟨X, hX⟩ := exists_GL_mulVec_eq hr₀ hr₁
  have hdd : (((dualGLn m X)⁻¹ : GL (Fin m) (ZMod 2)) : Matrix (Fin m) (Fin m) (ZMod 2))ᵀ =
      (X : Matrix (Fin m) (Fin m) (ZMod 2)) := by
    have h := congrArg (fun Y : GL (Fin m) (ZMod 2) => (Y : Matrix (Fin m) (Fin m) (ZMod 2)))
      (dualGLn_dualGLn X)
    exact h
  have hcomm : ⁅leviHom m (dualGLn m X), trHom m (Multiplicative.ofAdd r₀)⁆ = trHom m r := by
    rw [commutatorElement_def, leviHom_mul_trHom_mul_inv, hdd]
    simp only [toAdd_ofAdd]
    rw [hX, ← map_inv, ← map_mul]
    congr 1
    apply Multiplicative.toAdd.injective
    simp only [toAdd_mul, toAdd_inv, toAdd_ofAdd]
    abel
  rw [← hcomm]
  exact Subgroup.commutator_mem_commutator (leviHom_mem _) (trHom_mem _)

theorem isPerfect_stabGL (hm : 3 ≤ m) : Group.IsPerfect (stabGL m) := by
  rw [Subgroup.isPerfect_iff]
  refine le_antisymm ?_ ?_
  · rw [Subgroup.commutator_le]
    intro g hg h hh
    exact (stabGL m).mul_mem ((stabGL m).mul_mem ((stabGL m).mul_mem hg hh)
      ((stabGL m).inv_mem hg)) ((stabGL m).inv_mem hh)
  · intro A hA
    have h := Subgroup.mul_mem _ (leviHom_mem_commutator hm (blockHom m ⟨A, hA⟩))
      (trHom_mem_commutator (m := m) (by omega)
        (Multiplicative.ofAdd (fun j => ((A : GL (Fin (m + 1)) (ZMod 2)) :
          Matrix (Fin (m + 1)) (Fin (m + 1)) (ZMod 2)) 0 j.succ)))
    rw [← blockGL_eq_levi_mul_tr, ← eq_blockGL_blockHom ⟨A, hA⟩] at h
    exact h

theorem isPerfect_Cv (hm : 3 ≤ m) :
    Group.IsPerfect ↥(Lg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0))) := by
  have key : ∀ K : Subgroup (MulAut (PairN (m + 1))), K = (stabGL m).map (pairActN (m + 1)) →
      Group.IsPerfect ↥K := by
    intro K hK
    subst hK
    haveI := isPerfect_stabGL hm
    exact Group.IsPerfect.ofSurjective (f := (pairActN (m + 1)).subgroupMap (stabGL m))
      ((pairActN (m + 1)).subgroupMap_surjective (stabGL m))
  exact key _ (Lg_inf_centSub_eq_map m)

theorem twoResidual_Cv (hm : 3 ≤ m) :
    twoResidual (Lg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0))) =
      Lg (m + 1) ⊓ centSub (Subgroup.zpowers (pairVec (ez m) 0)) :=
  twoResidual_eq_self_of_isPerfect (isPerfect_Cv hm)

end CFSG.ASVolI.ChH.VectorStabilizer
