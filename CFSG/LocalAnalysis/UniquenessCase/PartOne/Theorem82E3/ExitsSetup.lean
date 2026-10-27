module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.CaseOneLbar
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.SCExcluded3
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.LocalAnalysis.RankThreeUC (Setup Standing AGL81TheoremC)
open CFSG.LocalAnalysis.UniquenessCase.UC22 (IsSpor)
open CFSG.LocalAnalysis.UniquenessCase.UCK (ThreeCover)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82 (IsLie811)

@[expose] def ONanExcludedSetup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), CFSG.Open.rankThreeUC G →
    AGL81TheoremC G → ∀ S : Setup G, S.InMSigma →
      ∀ c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S),
        CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L →
        ThreeCover (fun Y _ => IsSpor Y .ONan) c.Lbar →
        (PartTwo.Three.dataOfSetup hS S).sig = {7} → False

@[expose] def L62ExcludedSetup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), CFSG.Open.rankThreeUC G →
    AGL81TheoremC G → ∀ S : Setup G, S.InMSigma →
      ∀ c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S),
        CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L →
        IsLie811 c.Lbar .l6 2 1 → (PartTwo.Three.dataOfSetup hS S).sig = {7} → False

@[expose] def SCExcludedSetup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), CFSG.Open.rankThreeUC G →
    AGL81TheoremC G → ∀ S : Setup G, S.InMSigma →
      ∀ c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S),
        ¬ CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L → c.SCExcluded3

@[expose] def Case812Setup : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (hS : Standing G), CFSG.Open.rankThreeUC G →
    AGL81TheoremC G → ∀ S : Setup G, S.InMSigma →
      ∀ c : Ctx82E3 (PartTwo.Three.dataOfSetup hS S),
        ¬ CFSG.Yardstones.Mf4cdcdf2e013.QuasisimpleModOTwo c.L → False

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
