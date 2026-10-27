module

public import CFSG.LocalAnalysis.StandardType.GGTorusGenE6TwoLang
import CFSG.LieType.Chevalley.KernelComponentRoots

public section

namespace CFSG.StandardType

open CFSG CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg.Adjoint
open TableBExc.E6Three

namespace E6TwoGen

private def reflE6 (β v : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ :=
  v - iform β v • β

private def wvE6 (v : Fin Tag.E6.rank → ℤ) : Fin Tag.E6.rank → ℤ :=
  reflE6 (bE6 0) (reflE6 (bE6 1) (reflE6 (bE6 2) (reflE6 (bE6 3) v)))

private theorem iform_bE6_self (i : Fin 4) : iform (bE6 i) (bE6 i) = 2 := by
  have h : ∀ i : Fin 4, iform (bE6 i) (bE6 i) = 2 := by decide +kernel
  exact h i

private theorem corootPair_bE6 (i : Fin 4) (v : Fin Tag.E6.rank → ℤ) :
    corootPair (bE6 i) v = iform (bE6 i) v := by
  rw [corootPair, iform_bE6_self i]
  omega

private theorem wE6Two_smul_eq_wvE6
    (v : Fin Tag.E6.rank → ℤ) :
    wE6Two • v = wvE6 v := by
  rw [wE6Two]
  simp only [mul_smul]
  rw [rootReflection_smul (isRoot_bE6 0), rootReflection_smul (isRoot_bE6 1),
    rootReflection_smul (isRoot_bE6 2), rootReflection_smul (isRoot_bE6 3)]
  simp only [corootPair_bE6, wvE6, reflE6]

private theorem wvE6_spec :
    ∀ v ∈ rootFinset .E6,
      wvE6 v = -v ∨ (iform v (wvE6 v) = 0 ∧ wvE6 (wvE6 v) = v) := by
  decide +kernel

theorem wE6Two_smul_root
    {α : Fin Tag.E6.rank → ℤ} (hα : IsRoot .E6 α) :
    wE6Two • α = -α ∨ (iform α (wE6Two • α) = 0 ∧ wE6Two • wE6Two • α = α) := by
  have hspec := wvE6_spec α (mem_rootFinset.2 hα)
  rw [wE6Two_smul_eq_wvE6, wE6Two_smul_eq_wvE6 (wvE6 α)]
  exact hspec

end E6TwoGen

end CFSG.StandardType
