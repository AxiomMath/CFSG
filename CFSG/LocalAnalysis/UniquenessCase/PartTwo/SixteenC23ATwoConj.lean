module

public import Mathlib.Data.Set.Card
public import Mathlib.Algebra.Group.Subgroup.Ker

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

variable {A : Type*} [Group A]

private theorem c23a_map_conj_one (L : Subgroup A) :
    L.map (MulAut.conj (1 : A)).toMonoidHom = L := by
  ext x
  simp [Subgroup.mem_map]

private theorem c23a_map_conj_mul (L : Subgroup A) (m ψ : A) :
    (L.map (MulAut.conj ψ).toMonoidHom).map (MulAut.conj m).toMonoidHom =
      L.map (MulAut.conj (m * ψ)).toMonoidHom := by
  rw [Subgroup.map_map]
  congr 1
  ext x
  simp [MulAut.conj_apply, mul_assoc]

theorem c23a_two_conj {Mb L : Subgroup A}
    (h : Set.ncard {X : Subgroup A | ∃ φ ∈ Mb, X = L.map (MulAut.conj φ).toMonoidHom} = 2) :
    (∃ ψ ∈ Mb, L.map (MulAut.conj ψ).toMonoidHom ≠ L) ∧
      ∀ ψ ∈ Mb, L.map (MulAut.conj ψ).toMonoidHom ≠ L →
        (∀ φ ∈ Mb, L.map (MulAut.conj φ).toMonoidHom = L ∨
          L.map (MulAut.conj φ).toMonoidHom = L.map (MulAut.conj ψ).toMonoidHom) ∧
        ∀ m ∈ Mb,
          (L.map (MulAut.conj m).toMonoidHom = L ∧
            (L.map (MulAut.conj ψ).toMonoidHom).map (MulAut.conj m).toMonoidHom =
              L.map (MulAut.conj ψ).toMonoidHom) ∨
          (L.map (MulAut.conj m).toMonoidHom = L.map (MulAut.conj ψ).toMonoidHom ∧
            (L.map (MulAut.conj ψ).toMonoidHom).map (MulAut.conj m).toMonoidHom = L) := by
  obtain ⟨X, Y, hXY, hS⟩ := Set.ncard_eq_two.1 h
  have hmem : ∀ φ ∈ Mb, L.map (MulAut.conj φ).toMonoidHom = X ∨
      L.map (MulAut.conj φ).toMonoidHom = Y := by
    intro φ hφ
    have : L.map (MulAut.conj φ).toMonoidHom ∈ ({X, Y} : Set (Subgroup A)) := by
      rw [← hS]
      exact ⟨φ, hφ, rfl⟩
    simpa using this
  have hL : L = X ∨ L = Y := by
    have h1 := hmem 1 Mb.one_mem
    rwa [c23a_map_conj_one] at h1
  have hex : ∃ ψ ∈ Mb, L.map (MulAut.conj ψ).toMonoidHom ≠ L := by
    by_contra hcon
    push Not at hcon
    rcases hL with rfl | rfl
    · have hY : Y ∈ ({L, Y} : Set (Subgroup A)) := by simp
      rw [← hS] at hY
      obtain ⟨φ, hφ, hφY⟩ := hY
      exact hXY (by rw [hφY]; exact (hcon φ hφ).symm)
    · have hX : X ∈ ({X, L} : Set (Subgroup A)) := by simp
      rw [← hS] at hX
      obtain ⟨φ, hφ, hφX⟩ := hX
      exact hXY (by rw [hφX]; exact hcon φ hφ)
  refine ⟨hex, fun ψ hψ hψL => ?_⟩
  have hcases : ∀ φ ∈ Mb, L.map (MulAut.conj φ).toMonoidHom = L ∨
      L.map (MulAut.conj φ).toMonoidHom = L.map (MulAut.conj ψ).toMonoidHom := by
    intro φ hφ
    have h1 := hmem φ hφ
    have h2 := hmem ψ hψ
    rcases hL with hL | hL <;> rcases h1 with h1 | h1 <;> rcases h2 with h2 | h2 <;>
      first
      | exact absurd (h2.trans hL.symm) hψL
      | exact Or.inl (h1.trans hL.symm)
      | exact Or.inr (h1.trans h2.symm)
  refine ⟨hcases, fun m hm => ?_⟩
  have hinj : Function.Injective
      (Subgroup.map (MulAut.conj m).toMonoidHom : Subgroup A → Subgroup A) :=
    Subgroup.map_injective (MulEquiv.injective _)
  have hne : L.map (MulAut.conj m).toMonoidHom ≠
      (L.map (MulAut.conj ψ).toMonoidHom).map (MulAut.conj m).toMonoidHom := fun he =>
    hψL (hinj he).symm
  rw [c23a_map_conj_mul] at hne ⊢
  rcases hcases m hm with h1 | h1
  · left
    refine ⟨h1, ?_⟩
    rcases hcases (m * ψ) (Mb.mul_mem hm hψ) with h2 | h2
    · exact absurd (h1.trans h2.symm) hne
    · exact h2
  · right
    refine ⟨h1, ?_⟩
    rcases hcases (m * ψ) (Mb.mul_mem hm hψ) with h2 | h2
    · exact h2
    · exact absurd (h1.trans h2.symm) hne

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
