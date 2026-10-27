module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8CuUnique
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC8SpinHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open CFSG.Quasithin.SmithCurtis
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.SpCurtis

theorem exists_spinRep :
    ∃ (V₀ : Type) (_ : AddCommGroup V₀) (_ : Module (ZMod 2) V₀) (_ : Finite V₀)
      (ρ₀ : Representation (ZMod 2) G6 V₀), IsSimpleRep ρ₀ ∧
        Module.finrank (ZMod 2) V₀ = 8 := by
  obtain ⟨e⟩ := cu_nonempty_equiv_of_isSpn isSpn_spinH
  obtain ⟨V, instA, instM, instF, ρ, θ, hs, -⟩ :=
    cu_binModel spinW_exp_rk.1 spinH_irr e
  exact ⟨V, instA, instM, instF, ρ, hs,
    cu_finrank_eq spinW_exp_rk.1 spinW_exp_rk.2 θ⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
