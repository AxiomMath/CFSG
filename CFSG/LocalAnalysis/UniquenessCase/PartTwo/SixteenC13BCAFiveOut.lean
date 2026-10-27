module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC13BCAFiveEquiv
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenSeven2TwentyNineFrameOuter
public import CFSG.LocalAnalysis.ComponentClassification.CatalogueSchreierLinearTwoAllFields

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Open CFSG.ComponentClassification.AutL2Facts

theorem s16c13bcA_outer_solvable_om {F Y : Type} [Group F] [Group Y] (hY : IsOmegaPlus Y 4 2)
    (e : F ≃* Multiplicative (ZMod 3) × Y) :
    Group.IsSolvable (CFSG.ComponentClassification.OuterAutomorphisms.Outer F) := by
  obtain ⟨K, hKf, hKfin, hKc, hcard, ⟨eY⟩⟩ := s16c13bcA_omegaPlus_equiv hY
  letI := hKf
  letI := hKfin
  letI := hKc
  have h4 : 4 ≤ Nat.card K := hcard.ge
  have hcen : Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) = ⊥ :=
    s16c13bcA_center_sl2
  let ePSL : Matrix.ProjectiveSpecialLinearGroup (Fin 2) K ≃*
      Matrix.SpecialLinearGroup (Fin 2) K :=
    (QuotientGroup.quotientMulEquivOfEq hcen).trans QuotientGroup.quotientBot
  haveI : IsSimpleGroup (Matrix.ProjectiveSpecialLinearGroup (Fin 2) K) :=
    Matrix.ProjectiveSpecialLinearGroup.rank_two_simple h4
  haveI : IsSimpleGroup (Matrix.SpecialLinearGroup (Fin 2) K) := ePSL.symm.isSimpleGroup
  have hSC : SimpleCentreless (Matrix.SpecialLinearGroup (Fin 2) K) := by
    refine ⟨fun N hN => ?_, fun z hz => ?_, ?_⟩
    · haveI := hN
      exact IsSimpleGroup.eq_bot_or_eq_top_of_normal N
    · have hz' : z ∈ Subgroup.center (Matrix.SpecialLinearGroup (Fin 2) K) :=
        Subgroup.mem_center_iff.mpr fun g => (hz g).symm
      rw [hcen, Subgroup.mem_bot] at hz'
      exact hz'
    · obtain ⟨x, hx⟩ := exists_ne (1 : Matrix.SpecialLinearGroup (Fin 2) K)
      exact ⟨x, hx⟩
  have hperf : Group.IsPerfect (Matrix.SpecialLinearGroup (Fin 2) K) :=
    CFSG.ClassicalModels.specialLinear_isPerfect_two_of_four_le_card K h4
  have hout : Group.IsSolvable
      (CFSG.ComponentClassification.OuterAutomorphisms.Outer
        (Matrix.SpecialLinearGroup (Fin 2) K)) :=
    CFSG.ComponentClassification.CatalogueSchreierLinearTwo.outer_solvable_of_equiv K ePSL.symm
  exact s16c167_frame_outer_cyclic_square_solvable hSC hperf hout
    (e.trans (MulEquiv.prodCongr (MulEquiv.refl _) eY))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
