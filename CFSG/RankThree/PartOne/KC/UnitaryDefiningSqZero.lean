module

public import CFSG.RankThree.PartOne.KC.UnitaryDefiningHermitian
public import CFSG.ClassicalGroups.UnitaryFlag.GramForm
public import CFSG.LinearAlgebra.LinearGroups.UnitaryBasics

public section

namespace CFSG.RankThree.PartOne.KCUnitaryHerm

open CFSG.LocalAnalysis.ComponentInitial CFSG.ClassicalGroups.UnitaryFlag CFSG.LinearGroups

variable {p f : ℕ} {K : Type} [Field K] {h : UnitaryFieldData p f K} {V : Type} [AddCommGroup V]
  [Module K V] [FiniteDimensional K V]

theorem exists_sq_zero_structure (hp3 : 3 < p) {B : V →ₛₗ[h.bar] V →ₗ[K] K} (hB : B.IsSymm)
    (hBl : B.SeparatingLeft) {N : V →ₗ[K] V} (hN : ∀ x y, B (N x) y = -B x (N y))
    (hN2 : ∀ x, N (N x) = 0) (hN0 : N ≠ 0) {η : K} (hη : h.bar η = -η) (hη0 : η ≠ 0) :
    ∃ e g : V, B e e = 0 ∧ B g g = 0 ∧ B e g = 1 ∧ N e = 0 ∧ N g = η • e ∧
      Module.finrank K ((Submodule.span K {e, g}).orthogonalBilin B) = Module.finrank K V - 2 ∧
      (B.domRestrict₁₂ ((Submodule.span K {e, g}).orthogonalBilin B)
        ((Submodule.span K {e, g}).orthogonalBilin B)).SeparatingLeft ∧
      ((∀ z ∈ (Submodule.span K {e, g}).orthogonalBilin B, N z = 0) ∨
        (2 ≤ Module.finrank K ((Submodule.span K {e, g}).orthogonalBilin B) ∧
          ∃ e' ∈ (Submodule.span K {e, g}).orthogonalBilin B,
            ∃ g' ∈ (Submodule.span K {e, g}).orthogonalBilin B,
              B e' e' = 0 ∧ B g' g' = 0 ∧ B e' g' = 1 ∧ N e' = 0 ∧ N g' = η • e')) := by
  obtain ⟨e, g, hee, hgg, heg, hNe, hNg⟩ :=
    exists_hyperbolic_pair_of_sq_zero hp3 hB hBl hN hN2 hN0 hη hη0
  have he0 : e ≠ 0 := by
    rintro rfl
    simp at heg
  obtain ⟨-, hsp⟩ := hermitian_hyperbolic_splitting h hB hBl he0 hee
  obtain ⟨-, -, -, hWsep, hWdim⟩ := hsp g heg hgg
  refine ⟨e, g, hee, hgg, heg, hNe, hNg, hWdim, hWsep, ?_⟩
  set W := (Submodule.span K {e, g}).orthogonalBilin B with hW
  have hWinv : ∀ z ∈ W, N z ∈ W := fun z hz => orthogonal_span_invariant hN hNe hNg hz
  by_cases hW0 : ∀ z ∈ W, N z = 0
  · exact Or.inl hW0
  right
  obtain ⟨z, hzW, hz0⟩ : ∃ z ∈ W, N z ≠ 0 := by
    by_contra hcon
    exact hW0 fun z hz => by
      by_contra hne
      exact hcon ⟨z, hz, hne⟩
  let N' : W →ₗ[K] W := N.restrict hWinv
  have hN' : ∀ x y : W, (B.domRestrict₁₂ W W) (N' x) y = -(B.domRestrict₁₂ W W) x (N' y) :=
    fun x y => hN x y
  have hN2' : ∀ x : W, N' (N' x) = 0 := fun x => Subtype.ext (hN2 x)
  have hN0' : N' ≠ 0 := fun h0 => hz0 (congrArg Subtype.val (LinearMap.congr_fun h0 ⟨z, hzW⟩))
  obtain ⟨e', g', hee', hgg', heg', hNe', hNg'⟩ := exists_hyperbolic_pair_of_sq_zero hp3
    (B := B.domRestrict₁₂ W W) (hB.domRestrict W) hWsep hN' hN2' hN0' hη hη0
  have h2 : 2 ≤ Module.finrank K W := by
    have he'0 : e' ≠ 0 := by
      rintro rfl
      simp at heg'
    obtain ⟨-, hsp'⟩ := hermitian_hyperbolic_splitting h (hB.domRestrict W) hWsep he'0 hee'
    obtain ⟨hfin, -⟩ := hsp' g' heg' hgg'
    rw [← hfin]
    exact Submodule.finrank_le _
  refine ⟨h2, e', e'.2, g', g'.2, ?_, ?_, ?_, ?_, ?_⟩
  · simpa [LinearMap.domRestrict₁₂_apply] using hee'
  · simpa [LinearMap.domRestrict₁₂_apply] using hgg'
  · simpa [LinearMap.domRestrict₁₂_apply] using heg'
  · have h1 : N (e' : V) = ((N' e' : W) : V) := rfl
    rw [h1, hNe']
    rfl
  · have h1 : N (g' : V) = ((N' g' : W) : V) := rfl
    rw [h1, hNg']
    rfl

end CFSG.RankThree.PartOne.KCUnitaryHerm
