module

public import CFSG.RankThree.Classical.SteinbergBJOrthogonalInnerPlane

public section

namespace CFSG.RankThree.PartOne.KCOrthogonal

open QuadraticMap CFSG.RankThree.Classical CFSG.RankThree.Classical2

section Stable

variable {K V : Type} [Field K] [AddCommGroup V] [Module K V] {Q : QuadraticForm K V}
  {Ã : Subgroup (orthDerived Q)}

theorem stable_lineSpace (hcomm : ∀ x y : Ã, x * y = y * x) (M : Subgroup Ã) (a : Ã)
    {v : V} (hv : v ∈ lineSpace M) : ((a : orthDerived Q) : V ≃ₗ[K] V) v ∈ lineSpace M := by
  obtain ⟨hv1, hv2⟩ := Submodule.mem_inf.mp hv
  refine Submodule.mem_inf.mpr ⟨?_, ?_⟩
  · rw [lineFixSpace_eq_fixSub, mem_fixSub] at hv1
    show orthRep Ã a v ∈ lineFixSpace M
    rw [lineFixSpace_eq_fixSub, mem_fixSub]
    intro m hm
    rw [← Module.End.mul_apply, ← map_mul, hcomm m a, map_mul, Module.End.mul_apply,
      hv1 m hm]
  · rw [LinearMap.BilinForm.mem_orthogonal_iff]
    intro u hu
    have hu1 := hu
    rw [planeFixSpace_eq_fixSub, mem_fixSub] at hu1
    have hu2 := LinearMap.BilinForm.mem_orthogonal_iff.mp hv2 u hu
    have h3 := polar_orthRep Ã a u v
    rw [hu1 a trivial] at h3
    show polarBilin Q u (orthRep Ã a v) = 0
    rw [h3]
    exact hu2

end Stable

end CFSG.RankThree.PartOne.KCOrthogonal
