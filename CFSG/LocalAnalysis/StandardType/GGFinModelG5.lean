module

public import CFSG.LocalAnalysis.StandardType.GGFinModelG5Frame
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5RF
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5F5
public import CFSG.LocalAnalysis.StandardType.GGFinModelG5W

public section

namespace CFSG.StandardType.GGFinModel.G5

open CFSG.StandardType CFSG.StandardType.GGFinModel CFSG.Open CFSG.Assembly CFSG.Blueprint
  CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.Assembly.LowTwoRank

section Glue

theorem ggG5_exists
    {t : StatedLieTag} {n f p : ℕ} [NeZero p] (ht : GGExcFive t) (hf : 1 ≤ f)
    (hp : p.Prime) (hp2 : p ≠ 2) (hreg : GGExcRegime p f) :
    ∃ M : GGDatumModel t f p ht,
      GGClauseRF t n f p (ggPsiU t n f) (M.torusData (n := n) hf hp hp2 hreg).ggBfull (piB t p f)
          (M.torusData (n := n) hf hp hp2 hreg).ggCoord ∧
        GGModelF5 t n f p (M.torusData (n := n) hf hp hp2 hreg).ggBfull (gram t f) (piB t p f)
          (M.torusData (n := n) hf hp hp2 hreg).ggCoord ∧
        GGClauseW t n f p (ggPsiU t n f) (M.torusData (n := n) hf hp hp2 hreg).ggBfull (piB t p f)
          (M.torusData (n := n) hf hp hp2 hreg).ggCoord := by
  obtain ⟨F⟩ := ggG5_frame_exists (p := p) ht hf hp hp2 hreg
  exact ⟨F.M, ggG5_rf hf hp hp2 hreg F, ggG5_f5 hf hp hp2 hreg F, ggG5_w hf hp hp2 hreg F⟩

end Glue

end CFSG.StandardType.GGFinModel.G5
