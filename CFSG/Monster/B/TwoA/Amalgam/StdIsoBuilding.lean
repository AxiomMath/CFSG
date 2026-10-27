module

public import CFSG.Monster.B.TwoA.Amalgam.Deck
public import CFSG.Monster.B.TwoA.Amalgam.StdIsoNative
public import CFSG.Monster.B.TwoA.Amalgam.StdIsoStandard

public noncomputable section

attribute [-instance] instCommGroupOfIsSimpleGroupOfIsNilpotent
  instAddCommGroupOfIsSimpleAddGroupOfIsNilpotent

namespace CFSG.Monster.B.TwoA.Amalgam

open CFSG.Blueprint.Chevalley CFSG.LieType.Chevalley CFSG.LieType.Chevalley.C2E6Std
open CFSG.LieType.Chevalley.CosetBuilding CFSG.Monster.B.Geometry CFSG.Monster.B.E6.StdF4

theorem native_standard_F4_building_isomorphism :
    (∃ δ : Chamber → Chamber → WeylGroup .F4, IsWeylDistanceBuilding (coxeterSystem .F4) δ ∧
      ∀ (i : Fin Tag.F4.rank) (x y : Chamber),
        chamberCS.adj i x y ↔ δ x y = 1 ∨ δ x y = (coxeterSystem .F4).simple i) ∧
    ∀ δ : Chamber → Chamber → WeylGroup .F4, IsWeylDistanceBuilding (coxeterSystem .F4) δ →
      (∀ (i : Fin Tag.F4.rank) (x y : Chamber),
        chamberCS.adj i x y ↔ δ x y = 1 ∨ δ x y = (coxeterSystem .F4).simple i) →
      (∃ F : Chamber → C2E6Std.stdChamber,
        IsTypeIso (coxeterSystem .F4) δ stdDistanceF4 Set.univ Set.univ F ∧
          IsWeylIsometry δ stdDistanceF4 Set.univ Set.univ F) ∧
      ∀ (c d : Chamber) (c' d' : C2E6Std.stdChamber), δ c d = longest (coxeterSystem .F4) Set.univ →
        stdDistanceF4 c' d' = longest (coxeterSystem .F4) Set.univ →
        ∀ φ : Chamber → C2E6Std.stdChamber,
          IsWeylIsometry δ stdDistanceF4 (foundation (coxeterSystem .F4) δ 2 c ∪ {d})
            (foundation (coxeterSystem .F4) stdDistanceF4 2 c' ∪ {d'}) φ →
          φ c = c' → φ d = d' →
            ∃! F : Chamber → C2E6Std.stdChamber,
              (IsTypeIso (coxeterSystem .F4) δ stdDistanceF4 Set.univ Set.univ F ∧
                IsWeylIsometry δ stdDistanceF4 Set.univ Set.univ F) ∧
              Set.EqOn F φ (foundation (coxeterSystem .F4) δ 2 c ∪ {d}) := by
  obtain ⟨-, -, -, -, ⟨δ₀, hδ₀, hadj₀, -⟩, -⟩ := short_F4_deck_triviality_and_native_order
  exact ⟨⟨δ₀, hδ₀, hadj₀⟩, fun δ hδ hadj =>
    building_iso_of_hasClassicalEnds hδ isWeylDistanceBuilding_stdDistanceF4
      (hasClassicalEnds_native hδ hadj) hasClassicalEnds_std encard_panel_one_std⟩

end CFSG.Monster.B.TwoA.Amalgam
