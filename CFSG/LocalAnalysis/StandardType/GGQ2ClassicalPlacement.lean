module

public import CFSG.LocalAnalysis.StandardType.GGQ2FrameSplit
public import CFSG.LocalAnalysis.StandardType.GGNbrMarkingLabel
public import CFSG.LocalAnalysis.StandardType.GGOneFiveNbr

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly

private theorem marking_or {X : Type} [Group X] {P P₁ P₂ : LargeEvenLabel → Prop}
    (hq : CFSG.Assembly.IsQuasisimple X) (hP : ∀ lab, P lab → P₁ lab ∨ P₂ lab)
    (hm : LargeEvenMarking X (fun lab _ _ _ _ _ => P lab)) :
    LargeEvenMarking X (fun lab _ _ _ _ _ => P₁ lab) ∨
      LargeEvenMarking X (fun lab _ _ _ _ _ => P₂ lab) := by
  obtain ⟨labm, hlab2, hhas, -, -, -, -, -, hPm⟩ := largeEvenMarking_exists_hasLabel hm
  have hmk := largeEvenMarking_of_hasLabel hq hlab2 hhas
  rcases hP labm hPm with hi | hi
  · exact Or.inl (largeEvenMarking_mono (fun lab' R _ I F θ h => by rw [h]; exact hi) hmk)
  · exact Or.inr (largeEvenMarking_mono (fun lab' R _ I F θ h => by rw [h]; exact hi) hmk)

theorem PlacementInputOn.of_or {P P₁ P₂ : LargeEvenLabel → Prop}
    {catalogue : FrameKind → RawFrameData} (hP : ∀ lab, P lab → P₁ lab ∨ P₂ lab)
    (h₁ : PlacementInputOn P₁ catalogue) (h₂ : PlacementInputOn P₂ catalogue) :
    PlacementInputOn P catalogue := by
  intro G _ _ p B Bs x L D J hS hp hm
  rcases marking_or (isQuasisimple_of_largeEvenMarking (K := ggG0 p B x L D J) hm) hP hm with
    hm' | hm'
  · exact h₁ hS hp hm'
  · exact h₂ hS hp hm'

theorem PlacementCoreInputOn.of_or {P P₁ P₂ : LargeEvenLabel → Prop}
    {catalogue : FrameKind → RawFrameData} (hP : ∀ lab, P lab → P₁ lab ∨ P₂ lab)
    (h₁ : PlacementCoreInputOn P₁ catalogue) (h₂ : PlacementCoreInputOn P₂ catalogue) :
    PlacementCoreInputOn P catalogue := by
  intro G _ _ p B Bs x L D J hS hp hm
  rcases marking_or (isQuasisimple_of_largeEvenMarking (K := ggG0 p B x L D J) hm) hP hm with
    hm' | hm'
  · exact h₁ hS hp hm'
  · exact h₂ hS hp hm'

theorem placementInputOn_classical_of_families {catalogue : FrameKind → RawFrameData}
    (hA : PlacementInputOn (fun lab => lab.tag = .A) catalogue)
    (htwA : PlacementInputOn (fun lab => lab.tag = .twA) catalogue)
    (hBC : PlacementInputOn (fun lab => lab.tag = .B ∨ lab.tag = .C) catalogue)
    (hDtwD : PlacementInputOn (fun lab => lab.tag = .D ∨ lab.tag = .twD) catalogue) :
    PlacementInputOn ClassicalLabel catalogue :=
  PlacementInputOn.of_or (P₁ := fun lab => lab.tag = .A)
    (P₂ := fun lab => lab.tag = .twA ∨ ((lab.tag = .B ∨ lab.tag = .C) ∨
      (lab.tag = .D ∨ lab.tag = .twD)))
    (fun lab h => by unfold ClassicalLabel at h; tauto) hA
    (PlacementInputOn.of_or (P₁ := fun lab => lab.tag = .twA)
      (P₂ := fun lab => (lab.tag = .B ∨ lab.tag = .C) ∨ (lab.tag = .D ∨ lab.tag = .twD))
      (fun lab h => h) htwA
      (PlacementInputOn.of_or (P₁ := fun lab => lab.tag = .B ∨ lab.tag = .C)
        (P₂ := fun lab => lab.tag = .D ∨ lab.tag = .twD) (fun lab h => h) hBC hDtwD))

theorem placementCoreInputOn_classical_of_families {catalogue : FrameKind → RawFrameData}
    (hA : PlacementCoreInputOn (fun lab => lab.tag = .A) catalogue)
    (htwA : PlacementCoreInputOn (fun lab => lab.tag = .twA) catalogue)
    (hBC : PlacementCoreInputOn (fun lab => lab.tag = .B ∨ lab.tag = .C) catalogue)
    (hDtwD : PlacementCoreInputOn (fun lab => lab.tag = .D ∨ lab.tag = .twD) catalogue) :
    PlacementCoreInputOn ClassicalLabel catalogue :=
  PlacementCoreInputOn.of_or (P₁ := fun lab => lab.tag = .A)
    (P₂ := fun lab => lab.tag = .twA ∨ ((lab.tag = .B ∨ lab.tag = .C) ∨
      (lab.tag = .D ∨ lab.tag = .twD)))
    (fun lab h => by unfold ClassicalLabel at h; tauto) hA
    (PlacementCoreInputOn.of_or (P₁ := fun lab => lab.tag = .twA)
      (P₂ := fun lab => (lab.tag = .B ∨ lab.tag = .C) ∨ (lab.tag = .D ∨ lab.tag = .twD))
      (fun lab h => h) htwA
      (PlacementCoreInputOn.of_or (P₁ := fun lab => lab.tag = .B ∨ lab.tag = .C)
        (P₂ := fun lab => lab.tag = .D ∨ lab.tag = .twD) (fun lab h => h) hBC hDtwD))

end CFSG.StandardType.GGQ2Frame

end
