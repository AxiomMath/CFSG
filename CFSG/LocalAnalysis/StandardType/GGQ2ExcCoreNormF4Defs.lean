module

public import CFSG.LocalAnalysis.StandardType.GGQ2ExcCoreDefs

public section

namespace CFSG.StandardType.GGQ2Frame.ExcPlacement

open CFSG CFSG.Assembly CFSG.StandardType CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley
  CFSG.LocalAnalysis.ComponentInitial.FourGroupChevalley
  CFSG.HardMathSupport.Timmesfeld.LangTorus CFSG.StandardType.QTwoCav

noncomputable section


@[expose] def ExcF4NormB2 : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .F4 L p), NegLangTwo S →
    ∀ {T₀ : Subgroup (ModGL .F4 L)} (d : ExcCoordDatum S T₀ 0) (c : Finset (ExcRaw.Root 0)),
      ExcRaw.admissible 0 c → c.card = 4 →
        (ggAutomizer (codeComponent S d.γ c) T₀).map (ggLin (p := 3) d.coord) =
          ExcRaw.weyl 0 c ⊓ (LinearEquiv.det : (ExcRaw.V 0 ≃ₗ[ZMod 3] ExcRaw.V 0) →* (ZMod 3)ˣ).ker

section RootWeyl


@[expose] def ExcF4NormRootWeyl : Prop :=
  ∀ {L : Type} [Field L] [IsAlgClosed L] {p : ℕ} (S : LangSetup .F4 L p), NegLangTwo S →
    ∀ {T₀ : Subgroup (ModGL .F4 L)} (d : ExcCoordDatum S T₀ 0) (c : Finset (ExcRaw.Root 0)),
      ExcRaw.admissible 0 c → c.card ≠ 4 →
        ∀ i ∈ c, rootSL2 .F4 L (d.γ i) WSL ∈ codeComponent S d.γ c

end RootWeyl

end

end CFSG.StandardType.GGQ2Frame.ExcPlacement

end
