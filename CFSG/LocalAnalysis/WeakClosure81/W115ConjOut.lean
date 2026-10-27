module

public import CFSG.LocalAnalysis.WeakClosure81.W115ConjIn
public import CFSG.LocalAnalysis.WeakClosure81.W115ConjOutAux2
public import CFSG.Quasithin.AppendixH.H14.MathieuOuterInvolutions

public section

namespace CFSG.LocalAnalysis.WeakClosure81.W115

open CFSG.Blueprint
open CFSG.ComponentClassification.OuterAutomorphisms

theorem w115_fourConj_outer
    (α : MulAut ↥NativeSporadic.M22) (hα2 : α * α = 1)
    (hα1 : α ∉ inner ↥NativeSporadic.M22) :
    ∃ h : Fin 4 → ↥NativeSporadic.M22,
      inner ↥NativeSporadic.M22 ≤
        Subgroup.closure
          (Set.range fun i => MulAut.conj (h i) * α * (MulAut.conj (h i))⁻¹) := by
  obtain ⟨α₁, α₂, hcover⟩ := CFSG.Quasithin.AppendixH.H14.exists_outer_involution_reps
  have hP := w115_P_of_outer_reps hcover
  obtain ⟨z, hz⟩ := hcover α hα2 hα1
  rcases hz with hz | hz
  · have hconj := w115_P_conj z hP.1
    rw [← hz] at hconj
    exact hconj
  · have hconj := w115_P_conj z hP.2
    rw [← hz] at hconj
    exact hconj

theorem w115_fourConj_aut
    (α : MulAut ↥NativeSporadic.M22) (hα2 : α * α = 1) (hα1 : α ≠ 1) :
    ∃ h : Fin 4 → ↥NativeSporadic.M22,
      CFSG.ComponentClassification.OuterAutomorphisms.inner ↥NativeSporadic.M22 ≤
        Subgroup.closure
          (Set.range fun i => MulAut.conj (h i) * α * (MulAut.conj (h i))⁻¹) := by
  by_cases hαin : α ∈ CFSG.ComponentClassification.OuterAutomorphisms.inner ↥NativeSporadic.M22
  · obtain ⟨j, hj⟩ := hαin
    have hj2 : j * j = 1 := by
      have h : MulAut.conj (j * j) = 1 := by rw [map_mul, hj]; exact hα2
      have hker : j * j ∈ Subgroup.center ↥NativeSporadic.M22 := by
        rw [Subgroup.mem_center_iff]
        intro x
        have hx := congrArg (fun φ : MulAut ↥NativeSporadic.M22 => φ x) h
        simp only [MulAut.conj_apply, MulAut.one_apply] at hx
        calc x * (j * j) = ((j * j) * x * (j * j)⁻¹) * (j * j) := by rw [hx]
          _ = (j * j) * x := by group
      rw [CFSG.Sporadic.Schreier.m22_center_eq_bot', Subgroup.mem_bot] at hker
      exact hker
    have hj1 : j ≠ 1 := by
      intro h
      apply hα1
      rw [← hj, h, map_one]
    obtain ⟨h, hh⟩ := w115_fourConj_inner hj2 hj1
    refine ⟨h, ?_⟩
    have hmap := MonoidHom.map_closure
      (MulAut.conj : ↥NativeSporadic.M22 →* MulAut ↥NativeSporadic.M22)
      (Set.range fun i => h i * j * (h i)⁻¹)
    rw [hh] at hmap
    have himg : MulAut.conj '' (Set.range fun i => h i * j * (h i)⁻¹) =
        Set.range fun i => MulAut.conj (h i) * MulAut.conj j *
          (MulAut.conj (h i))⁻¹ := by
      rw [← Set.range_comp]
      apply congrArg Set.range
      funext i
      simp only [Function.comp_apply, map_mul, map_inv]
    rw [himg] at hmap
    rw [hj] at hmap
    have hrange : ((⊤ : Subgroup ↥NativeSporadic.M22).map
        (MulAut.conj : ↥NativeSporadic.M22 →* MulAut ↥NativeSporadic.M22)) =
        CFSG.ComponentClassification.OuterAutomorphisms.inner ↥NativeSporadic.M22 :=
      Subgroup.map_top _
    rw [hrange] at hmap
    rw [hmap]
  · exact w115_fourConj_outer α hα2 hαin

end CFSG.LocalAnalysis.WeakClosure81.W115
