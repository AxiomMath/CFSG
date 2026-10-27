module

public import CFSG.LocalAnalysis.StandardType.GGRawAutRestSz
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestSmall
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestTri
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestTwE6
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestChev
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestUnitary
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestOmega
public import CFSG.LocalAnalysis.StandardType.GGRawAutRestReeF4
public import CFSG.LocalAnalysis.StandardType.GGNbrGraphField

public section

namespace CFSG.StandardType

open CFSG.Assembly


theorem ggRawPCyclicOn_rest5 :
    GGRawPCyclicOn fun p lab => GGNotD4Three p lab ∧ ¬ GGRawPCyclicDoneLabel lab ∧
      ¬ GGOmegaLabel lab := by
  intro p hp hp2 lab hlab hS
  obtain ⟨-, hnd, hno⟩ := hS
  obtain ⟨t, l, n⟩ := lab
  cases t with
  | twE6 => exact ggRawPCyclicOn_twE6 p hp hp2 _ hlab rfl
  | twB2 => exact ggRawPCyclicOn_twB2 p hp hp2 _ hlab rfl
  | G2der => exact ggRawPCyclicOn_g2der p hp hp2 _ hlab rfl
  | twF4der => exact ggRawPCyclicOn_twF4der p hp hp2 _ hlab rfl
  | D =>
    exfalso
    have hl : 3 ≤ l := hlab.2
    rcases Nat.lt_or_ge l 4 with h4 | h4
    · exact hnd (by simp [GGRawPCyclicDoneLabel, GGLinearRecipeLabel]; omega)
    · exact hno (Or.inl ⟨rfl, h4⟩)
  | twD =>
    exfalso
    have hl : 2 ≤ l := hlab.2
    rcases Nat.lt_or_ge l 4 with h4 | h4
    · exact hnd (by
        simp [GGRawPCyclicDoneLabel, GGLinearRecipeLabel, GGInndiagUnitaryLabel]; omega)
    · exact hno (Or.inr ⟨rfl, h4⟩)
  | _ =>
    exfalso
    exact hnd (by simp [GGRawPCyclicDoneLabel, GGLinearRecipeLabel, GGSymplecticRecipeLabel,
      GGB2derLabel, GGRecipeExcCyclicLabel, GGRecipeExcOutLabel, GGRecipeOutCyclicLabel,
      GGInndiagUnitaryLabel, GGRecipeE6Label])

theorem ggL46CyclicInput_of_D4 (hD4 : GGL46CyclicD4Input) : GGL46CyclicInput :=
  ggL46CyclicInput_of_rest_omega plusFourTrialityInput_holds ggRawPCyclicOn_rest5 hD4

theorem ggOddAutOn_rest5 : GGOddAutOn fun lab => ¬ GGNbrGraphDoneLabel lab := by
  intro p lab hp hp2 hlab hS hD
  obtain ⟨t, l, n⟩ := lab
  cases t with
  | twA => exact ggOddAutOn_unitary p _ hp hp2 hlab (Or.inl rfl) hD
  | D =>
    have hl : 3 ≤ l := hlab.2
    rcases Nat.lt_or_ge l 4 with h4 | h4
    · exact absurd (by simp [GGNbrGraphDoneLabel, GGLinearRecipeLabel]; omega) hS
    · exact ggOddAutOn_omegaPlus p _ hp hp2 hlab ⟨rfl, h4⟩ hD
  | twD =>
    have hl : 2 ≤ l := hlab.2
    rcases Nat.lt_or_ge l 3 with h3 | h3
    · exact absurd (by simp [GGNbrGraphDoneLabel, GGLinearRecipeLabel]; omega) hS
    · rcases Nat.lt_or_ge l 4 with h4 | h4
      · exact ggOddAutOn_unitary p _ hp hp2 hlab (Or.inr ⟨rfl, show l = 3 by omega⟩) hD
      · exact ggOddAutOn_omegaMinus p _ hp hp2 hlab ⟨rfl, h4⟩ hD
  | E6 => exact ggOddAutOn_E6 p _ hp hp2 hlab rfl hD
  | E7 => exact ggOddAutOn_E7E8 p _ hp hp2 hlab (Or.inl rfl) hD
  | E8 => exact ggOddAutOn_E7E8 p _ hp hp2 hlab (Or.inr rfl) hD
  | F4 => exact ggOddAutOn_F4 p _ hp hp2 hlab rfl hD
  | G2 => exact ggOddAutOn_G2 p _ hp hp2 hlab rfl hD
  | twE6 => exact ggOddAutOn_twE6 p _ hp hp2 hlab rfl hD
  | triD4 => exact ggOddAutOn_triD4 p _ hp hp2 hlab rfl hD
  | twB2 => exact ggOddAutOn_twB2 p _ hp hp2 hlab rfl hD
  | twF4 => exact ggOddAutOn_twF4 p _ hp hp2 hlab rfl hD
  | G2der => exact ggOddAutOn_g2der p _ hp hp2 hlab rfl hD
  | twF4der => exact ggOddAutOn_twF4der p _ hp hp2 hlab rfl hD
  | _ =>
    exfalso
    exact hS (by simp [GGNbrGraphDoneLabel, GGLinearRecipeLabel, GGSymplecticRecipeLabel])

theorem ggOddAutOn_all : GGOddAutOn fun _ => True :=
  ggOddAutOn_true_of ggOddAutOn_done ggOddAutOn_rest5

theorem ggNbrGraphInput_of_D4 (hD4 : GGNbrGraphD4Input) : GGNbrGraphInput :=
  ggNbrGraphInput_of_rest ggOddAutOn_rest5 hD4

theorem ggRawInnFieldOn_rest5_of_twF4 (h : GGRawInnFieldOn fun lab => lab.tag = .twF4) :
    GGRawInnFieldOn fun lab => ¬ GGRawInnFieldDoneLabel lab ∧ ¬ GGOmegaLabel lab := by
  intro p hp hp2 lab hlab hS
  obtain ⟨hnd, hno⟩ := hS
  obtain ⟨t, l, n⟩ := lab
  cases t with
  | twE6 => exact ggRawInnFieldOn_twE6 p hp hp2 _ hlab rfl
  | triD4 => exact ggRawInnFieldOn_triD4 p hp hp2 _ hlab rfl
  | twB2 => exact ggRawInnFieldOn_twB2 p hp hp2 _ hlab rfl
  | twF4 => exact h p hp hp2 _ hlab rfl
  | D =>
    exfalso
    have hl : 3 ≤ l := hlab.2
    rcases Nat.lt_or_ge l 4 with h4 | h4
    · exact hnd (by simp [GGRawInnFieldDoneLabel, GGLinearRecipeLabel]; omega)
    · exact hno (Or.inl ⟨rfl, h4⟩)
  | twD =>
    exfalso
    have hl : 2 ≤ l := hlab.2
    rcases Nat.lt_or_ge l 4 with h4 | h4
    · exact hnd (by
        simp [GGRawInnFieldDoneLabel, GGLinearRecipeLabel, GGInndiagUnitaryLabel]; omega)
    · exact hno (Or.inr ⟨rfl, h4⟩)
  | _ =>
    exfalso
    exact hnd (by simp [GGRawInnFieldDoneLabel, GGLinearRecipeLabel, GGSymplecticRecipeLabel,
      GGB2derLabel, GGRecipeSmallExcLabel, GGInndiagUnitaryLabel, GGRecipeExcInnLabel,
      GGRecipeE6Label])

theorem ggRawInnFieldOn_rest5_of_diag (hF4 : GGTwistedF4DiagInput) :
    GGRawInnFieldOn fun lab => ¬ GGRawInnFieldDoneLabel lab ∧ ¬ GGOmegaLabel lab :=
  ggRawInnFieldOn_rest5_of_twF4 (ggRawInnFieldOn_twF4_of_diag hF4)

theorem ggRawInnFieldInput_of_twF4Diag (hF4 : GGTwistedF4DiagInput) : GGRawInnFieldInput :=
  ggRawInnFieldInput_of_rest_omega (ggRawInnFieldOn_rest5_of_diag hF4)

end CFSG.StandardType

end
