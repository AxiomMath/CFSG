module

public import CFSG.Sporadic.Mathieu.M24
public import CFSG.Sporadic.HS
public import CFSG.Sporadic.He.Simple
public import CFSG.Sporadic.Ru
public import CFSG.Assembly.RankThreeEvenDefs
public import CFSG.Fischer.Classification.Recognition.PSU6
public import CFSG.LocalAnalysis.ComponentClassification.ClassicalModelStatedBridge
public import CFSG.LocalAnalysis.RankTwoShapes.UnitaryFour.Bridge
public import CFSG.Quasithin.Background.A3StructureDefs
public import CFSG.Sporadic.Schreier.M23Base

public section

namespace CFSG.Quasithin.H13.NF314ptA312

open CFSG.Quasithin

theorem card_isSporadic_M23 {X : Type} [Group X]
    (h : IsSporadic .M23 X) : Nat.card X = 10200960 := by
  obtain ⟨e⟩ := h
  have : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M23) = 10200960 :=
    CFSG.Sporadic.Schreier.m23_card
  rw [Nat.card_congr e.toEquiv, this]

theorem card_isSporadic_M24 {X : Type} [Group X]
    (h : IsSporadic .M24 X) : Nat.card X = 244823040 := by
  obtain ⟨e⟩ := h
  have : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .M24) = 244823040 :=
    CFSG.Sporadic.Mathieu.card_M24
  rw [Nat.card_congr e.toEquiv, this]

theorem card_isSporadic_HS {X : Type} [Group X]
    (h : IsSporadic .HS X) : Nat.card X = 44352000 := by
  obtain ⟨e⟩ := h
  have : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .HS) = 44352000 :=
    CFSG.Sporadic.HS.card_HS
  rw [Nat.card_congr e.toEquiv, this]

theorem card_isSporadic_He {X : Type} [Group X]
    (h : IsSporadic .He X) : Nat.card X = 4030387200 := by
  obtain ⟨e⟩ := h
  have : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .He) = 4030387200 :=
    CFSG.Sporadic.He.card_He
  rw [Nat.card_congr e.toEquiv, this]

theorem card_isSporadic_Ru {X : Type} [Group X]
    (h : IsSporadic .Ru X) : Nat.card X = 145926144000 := by
  obtain ⟨e⟩ := h
  have : Nat.card (CFSG.Blueprint.NativeSporadic.Carrier .Ru) = 145926144000 :=
    CFSG.Sporadic.Ru.card_Ru
  rw [Nat.card_congr e.toEquiv, this]

end CFSG.Quasithin.H13.NF314ptA312
