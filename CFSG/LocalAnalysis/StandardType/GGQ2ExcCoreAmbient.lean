module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreAmbientCent

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley


theorem excCoreAmbient_of_rootSep {m : Fin 6} {τ : Tag}
    (hτ : τ = .F4 ∨ τ = .E6 ∨ τ = .E7 ∨ τ = .E8) (hsep : ExcRaw.RootSep m) :
    ExcCoreAmbient m τ := by
  intro L _ _ p S hS T₀ d
  exact le_antisymm (d.map_ggAutomizer_le hsep) (d.ambientNormalizer_le_map_ggAutomizer hS hτ)

theorem excCoreAmbient_F4 : ExcCoreAmbient 0 .F4 :=
  excCoreAmbient_of_rootSep (Or.inl rfl) ExcRaw.rootSep_zero

theorem excCoreAmbient_E7 : ExcCoreAmbient 4 .E7 :=
  excCoreAmbient_of_rootSep (Or.inr (Or.inr (Or.inl rfl))) ExcRaw.rootSep_four

theorem excCoreAmbient_E8 : ExcCoreAmbient 5 .E8 :=
  excCoreAmbient_of_rootSep (Or.inr (Or.inr (Or.inr rfl))) ExcRaw.rootSep_five

theorem excCoreAmbient_E6_two : ExcCoreAmbient 2 .E6 :=
  excCoreAmbient_of_rootSep (Or.inr (Or.inl rfl)) ExcRaw.rootSep_two

theorem excCoreAmbient_E6_three : ExcCoreAmbient 3 .E6 :=
  excCoreAmbient_of_rootSep (Or.inr (Or.inl rfl)) ExcRaw.rootSep_three

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
