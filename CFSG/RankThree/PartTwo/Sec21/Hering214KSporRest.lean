module

public import CFSG.RankThree.PartTwo.Sec21.Hering214KM23
public import CFSG.RankThree.PartTwo.Sec21.Hering214KM24
public import CFSG.RankThree.PartTwo.Sec21.Hering214KHS
public import CFSG.RankThree.PartTwo.Sec21.Hering214KJ4
public import CFSG.RankThree.PartTwo.Sec21.Hering214KFour
public import CFSG.RankThree.PartTwo.Sec21.Hering214KCoverBar

public section

namespace CFSG.RankThree.PartTwo.Sec21

open CFSG CFSG.Blueprint
open Hering214

namespace Hering214

@[expose] def IsBarSporadicRest (X : Type) [Group X] : Prop :=
  Nonempty (X ≃* NativeSporadic.He) ∨ Nonempty (X ≃* NativeSporadic.J2) ∨
    Nonempty (X ≃* NativeSporadic.Ru) ∨ Nonempty (X ≃* NativeSporadic.J3) ∨
    Sec4.IsTripleCover X NativeSporadic.J3

@[expose] def Item214BarSporadicRest : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Group.IsPerfect X → IsBarSporadicRest X →
    ∀ Ē Ū : Subgroup (MulAut X), BarData X Ē Ū → EInvFour X Ē

@[expose] def FourDataRest : Prop :=
  FourData27 NativeSporadic.He ∧ FourData27 NativeSporadic.J2 ∧ FourData27 NativeSporadic.Ru

@[expose] def Item214BarJ3Simple : Prop :=
  ∀ (X : Type) [Group X] [Finite X], Nonempty (X ≃* NativeSporadic.J3) →
    ∀ Ē Ū : Subgroup (MulAut X), BarData X Ē Ū → EInvFour X Ē

theorem item214BarSporadicRest_of_split
    (h₁ : FourDataRest) (h₂ : Item214BarJ3Simple) :
    Item214BarSporadicRest := by
  intro X _ _ hperf hX Ē Ū hd
  obtain ⟨hHe', hJ2', hRu'⟩ := h₁
  have hHe : EInvNine NativeSporadic.He := eInvNine_he_of_data hHe'
  have hJ2 : EInvNine NativeSporadic.J2 := eInvNine_j2_of_data hJ2'
  have hRu : EInvNine NativeSporadic.Ru := eInvNine_ru_of_data hRu'
  rcases hX with h | h | h | h | h
  · obtain ⟨e⟩ := h
    exact (@EInvNine.of_mulEquiv X NativeSporadic.He _ Units.instGroup e hHe) Ē hd.elem3
      hd.card9
  · obtain ⟨e⟩ := h
    exact (@EInvNine.of_mulEquiv X NativeSporadic.J2 _ Units.instGroup e hJ2) Ē hd.elem3
      hd.card9
  · obtain ⟨e⟩ := h
    exact (@EInvNine.of_mulEquiv X NativeSporadic.Ru _ Units.instGroup e hRu) Ē hd.elem3
      hd.card9
  · exact h₂ X h Ē Ū hd
  · obtain ⟨hZ3, ⟨e⟩⟩ := h
    haveI : Group.IsPerfect X := hperf
    exact eInvFour_of_perfect_central_quotient (Y := X ⧸ Subgroup.center X) hZ3 (MulEquiv.refl _)
      (fun Ē' Ū' hd' => h₂ (X ⧸ Subgroup.center X) ⟨e⟩ Ē' Ū' hd') hd

end Hering214

theorem item214BarSporadic_of_rest
    (hrest : Item214BarSporadicRest) : Item214BarSporadic := by
  intro X _ _ hperf hX Ē Ū hd
  have key : (Sec4.IsTripleCover X NativeSporadic.M22 ∨ Nonempty (X ≃* NativeSporadic.M22) ∨
      Nonempty (X ≃* NativeSporadic.M23) ∨ Nonempty (X ≃* NativeSporadic.HS) ∨
      Nonempty (X ≃* NativeSporadic.M24) ∨ Nonempty (X ≃* NativeSporadic.J4)) →
      EInvFour X Ē := by
    intro h
    rcases h with h | h | h | h | h | h
    · exact eInvNine_of_isTripleCover_m22 h Ē hd.elem3 hd.card9
    · obtain ⟨e⟩ := h
      exact eInvNine_of_mulEquiv_m22 e Ē hd.elem3 hd.card9
    · obtain ⟨e⟩ := h
      exact eInvNine_of_mulEquiv_m23 e Ē hd.elem3 hd.card9
    · obtain ⟨e⟩ := h
      exact eInvNine_of_mulEquiv_hs e Ē hd.elem3 hd.card9
    · obtain ⟨e⟩ := h
      exact eInvNine_of_mulEquiv_m24 e Ē hd.elem3 hd.card9
    · obtain ⟨e⟩ := h
      exact (@EInvNine.of_mulEquiv X NativeSporadic.J4 _ Units.instGroup e eInvNine_j4) Ē
        hd.elem3 hd.card9
  rcases hX with h | h | h | h | h | h | h | h | h | h | h
  · exact key (Or.inl h)
  · exact key (Or.inr (Or.inl h))
  · exact key (Or.inr (Or.inr (Or.inl h)))
  · exact key (Or.inr (Or.inr (Or.inr (Or.inl h))))
  · exact key (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl h)))))
  · exact hrest X hperf (Or.inl h) Ē Ū hd
  · exact hrest X hperf (Or.inr (Or.inl h)) Ē Ū hd
  · exact hrest X hperf (Or.inr (Or.inr (Or.inl h))) Ē Ū hd
  · exact key (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr h)))))
  · exact hrest X hperf (Or.inr (Or.inr (Or.inr (Or.inl h)))) Ē Ū hd
  · exact hrest X hperf (Or.inr (Or.inr (Or.inr (Or.inr h)))) Ē Ū hd

end CFSG.RankThree.PartTwo.Sec21
