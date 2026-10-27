module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen3a

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (mem_normalizer_iff_map_conj)

variable {G : Type} [Group G] [Finite G]

theorem le_normalizer_inf_of_permutesPair {D : Data G} {L₁ L₂ : Subgroup G}
    (hperm : PermutesPair D.M L₁ L₂) {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    {P : Subgroup G} (hP : IsPGroup p P) (hPM : P ≤ D.M) :
    P ≤ normalizer (L₁ : Set G) ⊓ normalizer (L₂ : Set G) := by
  intro x hx
  have hxM : x ∈ D.M := hPM hx
  rw [Subgroup.mem_inf, mem_normalizer_iff_map_conj, mem_normalizer_iff_map_conj]
  rcases hperm x hxM with ⟨h1, h2⟩ | ⟨h1, h2⟩
  · exact ⟨h1, h2⟩
  · have hsq1 : x ^ 2 ∈ normalizer (L₁ : Set G) := by
      rw [pow_two, mem_normalizer_iff_map_conj]
      have hcomp : MulAut.conj (x * x) = MulAut.conj x * MulAut.conj x :=
        map_mul MulAut.conj x x
      have hto : (MulAut.conj x * MulAut.conj x).toMonoidHom =
          (MulAut.conj x).toMonoidHom.comp (MulAut.conj x).toMonoidHom := by
        ext y
        simp [MulAut.mul_apply]
      rw [hcomp, hto, ← Subgroup.map_map, h1, h2]
    have hsq2 : x ^ 2 ∈ normalizer (L₂ : Set G) := by
      rw [pow_two, mem_normalizer_iff_map_conj]
      have hcomp : MulAut.conj (x * x) = MulAut.conj x * MulAut.conj x :=
        map_mul MulAut.conj x x
      have hto : (MulAut.conj x * MulAut.conj x).toMonoidHom =
          (MulAut.conj x).toMonoidHom.comp (MulAut.conj x).toMonoidHom := by
        ext y
        simp [MulAut.mul_apply]
      rw [hcomp, hto, ← Subgroup.map_map, h2, h1]
    obtain ⟨k, hk⟩ := hP ⟨x, hx⟩
    have hk' : x ^ (p ^ k) = 1 := by simpa using hk
    have hodd : Odd (p ^ k) := (hp.odd_of_ne_two hp2).pow
    obtain ⟨j, hj⟩ := hodd
    have hx_eq : x = ((x ^ 2) ^ j)⁻¹ := by
      apply eq_inv_of_mul_eq_one_right
      have h := hk'
      rw [hj, pow_succ, pow_mul] at h
      exact h
    have hxN1 : x ∈ normalizer (L₁ : Set G) := by
      rw [hx_eq]
      exact (Subgroup.normalizer _).inv_mem ((Subgroup.normalizer _).pow_mem hsq1 j)
    have hxN2 : x ∈ normalizer (L₂ : Set G) := by
      rw [hx_eq]
      exact (Subgroup.normalizer _).inv_mem ((Subgroup.normalizer _).pow_mem hsq2 j)
    exact ⟨mem_normalizer_iff_map_conj.1 hxN1, mem_normalizer_iff_map_conj.1 hxN2⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
