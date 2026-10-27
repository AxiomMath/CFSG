module

public import CFSG.RankThree.PartOne.S12.Sec12FusChoice
public import CFSG.RankThree.PartOne.S12.Sec12FusMove
public import CFSG.RankThree.PartOne.S12.Sec12FusMax
public import CFSG.RankThree.PartOne.S12.Sec12FusTwo
public import CFSG.RankThree.PartOne.S12.Sec12FusField

public section

namespace CFSG.RankThree.PartOne.CTP

open CFSG.RankThree.PartOne

@[expose] def KF1212LayerRow12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → RowModel p L 12 →
      ∃ (b : G) (K I : Subgroup G), Layer1212 p A c L E b K I

@[expose] def KF1213TypeRow12 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → RowModel p L 12 →
      ∀ (b : G) (K I X P Q : Subgroup G), Layer1212 p A c L E b K I →
        Choice1212 p E b I X P Q → InducesFieldAut p c I → LayerModel p L I p

theorem KF1212Layer.row12 (h : KF1212Layer) : KF1212LayerRow12 :=
  fun G _ _ p A c L E ctx _ => h G p A c L E ctx

theorem KF1213Type.row12 (h : KF1213Type) : KF1213TypeRow12 :=
  fun G _ _ p A c L E ctx _ b K I X P Q hL hC hF => h G p A c L E ctx b K I X P Q hL hC hF

@[expose] def Kf1214U5Core : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (p : ℕ) (A : Subgroup G) (c : G) (L E : Subgroup G),
    Fus12Ctx G p A c L E → RowModel p L 12 →
      ∀ (b : G) (K I X P Q : Subgroup G), Layer1212 p A c L E b K I →
        Choice1212 p E b I X P Q → Field1213 p A c L b K I → False

theorem kf1214U5_of_core
    (hsel : SelectedPrimeElementsNormalizeThetaComponents) (h112 : InSec11Two)
    (hLS : FieldAutCoset) (h124 : Node124) (hLay : KF1212LayerRow12)
    (hTyp : KF1213TypeRow12) (hcore : Kf1214U5Core) : KF1214U5 := by
  intro G _ _ p A c L E ctx hrow
  obtain ⟨b, K, I, hL⟩ := hLay G p A c L E ctx hrow
  obtain ⟨X, P, Q, hC⟩ := node1212Choice_of_inputs hsel G p A c L E ctx b K I hL
  obtain ⟨hne, hcomm⟩ := node1213Move_of_inputs G p A c L E ctx b K I X P Q hL hC
  have hmax := node1213Max_of_inputs G p A c L E ctx b K I X P Q hL hC hne hcomm
  have htwo := node1213Two_of_inputs h124 G p A c L E ctx b K I X P Q hL hC hne hcomm hmax
  have hfield := node1213Field_of_inputs h112 hLS G p A c L E ctx b K I X P Q hL hC hne hcomm
    hmax htwo
  have hmodel := hTyp G p A c L E ctx hrow b K I X P Q hL hC hfield
  exact hcore G p A c L E ctx hrow b K I X P Q hL hC ⟨hne, hcomm, hmax, htwo, hfield, hmodel⟩

end CFSG.RankThree.PartOne.CTP
