module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.FifteenKNormSymModel
import CFSG.HardMathSupport.Solomon.Coordinator.I28_14SymN
import CFSG.HardMathSupport.Solomon.Coordinator.I28_14SymAut

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.HardMathSupport.Solomon.Coordinator

theorem s15k_norm_sym_range {W : Type} [CommGroup W] {J : Subgroup (MulAut W)}
    {R : Subgroup W} {m : ℕ} (hm : 5 ≤ m) (h : SymmetricNatural J R ⊥ m) (D : McRep J R)
    (A : LinearMap.GeneralLinearGroup (ZMod 2) D.V)
    (hA : ∀ y ∈ D.ρ.range, A * y * A⁻¹ ∈ D.ρ.range) : A ∈ D.ρ.range := by
  obtain ⟨M, hM⟩ := s15k_norm_symModel hm h D
  have hg : ∀ y ∈ M.ψ.range, A * y * A⁻¹ ∈ M.ψ.range := by
    rw [hM]
    exact hA
  have h1 := i28_14_symModel_N M hm (fun α hα => perm_aut_preserving_swaps_inner hm α hα) hg
  rwa [hM] at h1

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
