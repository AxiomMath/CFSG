module

public import CFSG.LocalAnalysis.StandardType.GGL45NtClLin

public section

namespace CFSG.HardMathSupport.C14Cl

open CFSG CFSG.Open CFSG.Assembly CFSG.StandardType CFSG.LocalAnalysis.ComponentInitial
  CFSG.LocalAnalysis.ComponentInitial.LinearFlag Matrix

private theorem cLG1_mono {p : ℕ} {R : Type} [Group R] {I F F' : Set (MulAut R)}
    (hFF' : F ⊆ F') (h : GGL45NtCore p R I F') : GGL45NtCore p R I F := by
  intro hRsimple hRnonab Ebar f' hEab hcard hEbarI hf'p hconj hcomm hSat
  obtain ⟨f, hfF', u, huI, hford, hf'eq⟩ := hconj
  exact h hRsimple hRnonab Ebar f' hEab hcard hEbarI hf'p
    ⟨f, hFF' hfF', u, huI, hford, hf'eq⟩ hcomm hSat

theorem ntCore_lin {K : Type} [Field K] [Fintype K] [CharP K 2] {d p : ℕ} (hd : 3 ≤ d) (hp : p.Prime) (hp2 : p ≠ 2) (hpd : ¬ p ∣ d ∨ ¬ p ∣ Fintype.card K - 1) :
    GGL45NtCore p (LargeEvenProj (LargeEvenSLGroup (Fin d) K))
      (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)
      (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))) := by
  refine ntCore_of_mulEquiv (TypeA.recipeEquiv d K)
    (LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ)
    (LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K))) ?_
  have hI : (MulAut.congr (TypeA.recipeEquiv d K)) ''
      LargeEvenMatConjImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) Set.univ =
      Set.range (conjAut d K) := by
    rw [← RecipeFieldLinear.coe_recI]
    ext x
    constructor
    · rintro ⟨φ, hφ, rfl⟩
      exact Set.mem_range.mpr
        (LinearFlag.mem_linearAutGroup_iff.mp ((RecipeFieldLinear.mem_recI_iff).mp hφ))
    · intro hx
      obtain ⟨A, hA⟩ := Set.mem_range.mp hx
      refine ⟨(MulAut.congr (TypeA.recipeEquiv d K)).symm x, ?_, ?_⟩
      · rw [SetLike.mem_coe, RecipeFieldLinear.mem_recI_iff, MulEquiv.apply_symm_apply]
        exact LinearFlag.mem_linearAutGroup_iff.mpr ⟨A, hA⟩
      · exact (MulAut.congr (TypeA.recipeEquiv d K)).apply_symm_apply x
  have hF : (MulAut.congr (TypeA.recipeEquiv d K)) ''
      LargeEvenMatFieldImage (LargeEvenProjMk (LargeEvenSLGroup (Fin d) K)) ⊆
      Set.range (fieldAut d K) := by
    rintro φ ⟨ψ, hψ, rfl⟩
    obtain ⟨σ, hσ⟩ := RecipeFieldLinear.congr_field_eq hψ
    exact ⟨σ, hσ.symm⟩
  rw [hI]
  exact cLG1_mono hF (ntCore_lin_model hd hp hp2 hpd)

end CFSG.HardMathSupport.C14Cl
