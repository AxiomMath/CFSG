module

public import CFSG.LocalAnalysis.StandardType.GGQ2ActualFrame
public import CFSG.LocalAnalysis.StandardType.GGQ2AmbModelSplitAmb

public section

namespace CFSG.StandardType.GGQ2Frame

open CFSG CFSG.Assembly

@[expose] def ClassicalLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .A ∨ lab.tag = .twA ∨ lab.tag = .B ∨ lab.tag = .C ∨ lab.tag = .D ∨ lab.tag = .twD

@[expose] def ExceptionalLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .F4 ∨ lab.tag = .E6 ∨ lab.tag = .twE6 ∨ lab.tag = .E7 ∨ lab.tag = .E8

@[expose] def SmallLabel (lab : LargeEvenLabel) : Prop :=
  lab.tag = .G2 ∨ lab.tag = .triD4 ∨ lab.tag = .twB2 ∨ lab.tag = .twF4 ∨ lab.tag = .B2der ∨
    lab.tag = .G2der ∨ lab.tag = .twF4der

theorem label_cases (lab : LargeEvenLabel) :
    ClassicalLabel lab ∨ ExceptionalLabel lab ∨ SmallLabel lab := by
  unfold ClassicalLabel ExceptionalLabel SmallLabel
  cases lab.tag <;> simp

@[expose] def PlacementInputOn (P : LargeEvenLabel → Prop) (catalogue : FrameKind → RawFrameData) :
    Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 →
      LargeEvenMarking (ggG0 p B x L D J) (fun lab _ _ _ _ _ => P lab) →
        ∃ kind : FrameKind, ActualFrame (ggG0 p B x L D J) Bs (catalogue kind)

@[expose] def PlacementCoreInputOn (P : LargeEvenLabel → Prop)
    (catalogue : FrameKind → RawFrameData) : Prop :=
  ∀ {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G} {x : G} {L D J : Subgroup G},
    GGQTwoSetting p B Bs x L D J → p = 3 →
      LargeEvenMarking (ggG0 p B x L D J) (fun lab _ _ _ _ _ => P lab) →
        ∃ kind : FrameKind, ActualCoreFrame (ggG0 p B x L D J) Bs (catalogue kind)

theorem PlacementInputOn.toCore {P : LargeEvenLabel → Prop} {catalogue : FrameKind → RawFrameData}
    (h : PlacementInputOn P catalogue) : PlacementCoreInputOn P catalogue := by
  intro G _ _ p B Bs x L D J hS hp hm
  obtain ⟨kind, hframe⟩ := h hS hp hm
  exact ⟨kind, hframe.toCore⟩

theorem marking_ggG0_of_cover {ι : Type} (Ps : ι → LargeEvenLabel → Prop)
    (hcover : ∀ lab, ∃ i, Ps i lab) {G : Type} [Group G] [Finite G] {p : ℕ} {B Bs : Subgroup G}
    {x : G} {L D J : Subgroup G} (hS : GGQTwoSetting p B Bs x L D J) :
    ∃ i, LargeEvenMarking (ggG0 p B x L D J) (fun lab _ _ _ _ _ => Ps i lab) := by
  obtain ⟨lab, hm⟩ := ggQ2_marking_with_label hS.1.2.2.2.2
  obtain ⟨i, hi⟩ := hcover lab
  exact ⟨i, largeEvenMarking_mono (fun lab' R _ I F θ h => by rw [h]; exact hi) hm⟩

theorem placementInput_of_on {ι : Type} (Ps : ι → LargeEvenLabel → Prop)
    (catalogue : FrameKind → RawFrameData) (hOn : ∀ i, PlacementInputOn (Ps i) catalogue)
    (hcover : ∀ lab, ∃ i, Ps i lab) : PlacementInput catalogue := by
  intro G _ _ p B Bs x L D J hS hp
  obtain ⟨i, hm⟩ := marking_ggG0_of_cover Ps hcover hS
  exact hOn i hS hp hm

theorem placementCoreInput_of_on {ι : Type} (Ps : ι → LargeEvenLabel → Prop)
    (catalogue : FrameKind → RawFrameData) (hOn : ∀ i, PlacementCoreInputOn (Ps i) catalogue)
    (hcover : ∀ lab, ∃ i, Ps i lab) : PlacementCoreInput catalogue := by
  intro G _ _ p B Bs x L D J hS hp
  obtain ⟨i, hm⟩ := marking_ggG0_of_cover Ps hcover hS
  exact hOn i hS hp hm

theorem cover_three : ∀ lab : LargeEvenLabel,
    ∃ i : Fin 3, ![ClassicalLabel, ExceptionalLabel, SmallLabel] i lab := by
  intro lab
  rcases label_cases lab with h | h | h
  · exact ⟨0, h⟩
  · exact ⟨1, h⟩
  · exact ⟨2, h⟩

theorem placementInput_of_split (catalogue : FrameKind → RawFrameData)
    (hcl : PlacementInputOn ClassicalLabel catalogue)
    (hex : PlacementInputOn ExceptionalLabel catalogue)
    (hsm : PlacementInputOn SmallLabel catalogue) : PlacementInput catalogue := by
  refine placementInput_of_on ![ClassicalLabel, ExceptionalLabel, SmallLabel] catalogue ?_ cover_three
  intro i
  fin_cases i
  · exact hcl
  · exact hex
  · exact hsm

theorem placementCoreInput_of_split (catalogue : FrameKind → RawFrameData)
    (hcl : PlacementCoreInputOn ClassicalLabel catalogue)
    (hex : PlacementCoreInputOn ExceptionalLabel catalogue)
    (hsm : PlacementCoreInputOn SmallLabel catalogue) : PlacementCoreInput catalogue := by
  refine placementCoreInput_of_on ![ClassicalLabel, ExceptionalLabel, SmallLabel] catalogue ?_
    cover_three
  intro i
  fin_cases i
  · exact hcl
  · exact hex
  · exact hsm

@[expose] def catalogueOf (cl ex : FrameKind → RawFrameData) : FrameKind → RawFrameData :=
  fun k => if IsClassical k then cl k else ex k

theorem catalogueOf_classical (cl ex : FrameKind → RawFrameData) {k : FrameKind}
    (hk : IsClassical k) : catalogueOf cl ex k = cl k := by
  simp [catalogueOf, hk]

theorem catalogueOf_exceptional (cl ex : FrameKind → RawFrameData) {k : FrameKind}
    (hk : IsExceptional k) : catalogueOf cl ex k = ex k := by
  have : ¬ IsClassical k := hk
  simp [catalogueOf, this]

theorem actualCutThreeInput_catalogueOf (cl ex : FrameKind → RawFrameData)
    (hex : ∀ k, IsExceptional k → (ex k).kind = k)
    (hcl : ∀ k, IsClassical k → ActualCutThreeInput (cl k)) :
    ∀ k, ActualCutThreeInput (catalogueOf cl ex k) := by
  intro k
  by_cases hk : IsClassical k
  · rw [catalogueOf_classical cl ex hk]; exact hcl k hk
  · rw [catalogueOf_exceptional cl ex hk]
    intro hc
    have : IsExceptional (ex k).kind := by rw [hex k hk]; exact hk
    exfalso
    exact this hc

theorem actualCutFiveInput_catalogueOf (cl ex : FrameKind → RawFrameData)
    (hcl : ∀ k, IsClassical k → (cl k).kind = k)
    (hex : ∀ k, IsExceptional k → ActualCutFiveInput (ex k)) :
    ∀ k, ActualCutFiveInput (catalogueOf cl ex k) := by
  intro k
  by_cases hk : IsClassical k
  · rw [catalogueOf_classical cl ex hk]
    intro hc
    have : IsClassical (cl k).kind := by rw [hcl k hk]; exact hk
    exfalso
    exact hc this
  · rw [catalogueOf_exceptional cl ex hk]; exact hex k hk

end CFSG.StandardType.GGQ2Frame
