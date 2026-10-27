module

public import CFSG.LocalAnalysis.StandardType.GGSelectedModelOfChevalley
public import CFSG.LocalAnalysis.StandardType.F4ExplicitPos.Sp6Port419ReadyPart11
public import CFSG.LieType.Steinberg.Adjoint.Presentation

public noncomputable section

namespace CFSG.StandardType.SelectedRoot

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Steinberg
  CFSG.LieType.Steinberg.Adjoint CFSG.LieType.Universal CFSG.LieType.RootSystem
  CFSG.LieType.CurtisTits


theorem exists_model_f4 (K : Type) [Field K] [CharP K 2] (i : Fin Tag.F4.rank) :
    ∃ model : SelectedSL2Model (f4Datum K) K (Pi.single i 1),
      model.phi.range = rankOne (f4Datum K).rootGroup i := by
  obtain ⟨O⟩ := nonempty_commOrder_ofCartan (f4Datum K).isFiniteType
    (Dv := (f4Datum K).divisible) rfl
  obtain ⟨C, _hCabs, hC⟩ := f4_commutatorFormula K O
  have hE := f4_chevalleyExtras K O C hC
  have hM : GGRankOneModel (f4Datum K) K := by
    refine ⟨f4Par K, C, O, hE, ?_⟩
    intro h hh j
    obtain ⟨c, hc⟩ := F4ExplicitPos.RootScalar.f4_xPar_simple_scalar_of_mem_ggTorus K j h hh
    exact ⟨(c : K), hc⟩
  exact exists_model_of_rankOneModel hM i

end CFSG.StandardType.SelectedRoot
