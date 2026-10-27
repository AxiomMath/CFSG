module

public import CFSG.Quasithin.Recognition.UniquenessSystemDefs

public section

namespace CFSG.Quasithin.Asc94

universe u v

section Mono

variable {V : Type u} {Γ : SimpleGraph V}

theorem rotRev_mono {C C' : Set (List V)} (h : C ⊆ C') : rotRev C ⊆ rotRev C' := by
  rintro d ⟨c, hc, hd⟩
  exact ⟨c, h hc, hd⟩

theorem ElemMove.mono {C C' : Set (List V)} (h : C ⊆ C') {p q : List V}
    (hm : ElemMove Γ C p q) : ElemMove Γ C' p q := by
  cases hm with
  | backDel l₁ l₂ w v hwv => exact ElemMove.backDel l₁ l₂ w v hwv
  | backIns l₁ l₂ w v hwv => exact ElemMove.backIns l₁ l₂ w v hwv
  | cycIns l₁ l₂ c w hc h₁ h₂ => exact ElemMove.cycIns l₁ l₂ c w (rotRev_mono h hc) h₁ h₂
  | cycDel l₁ l₂ c w hc h₁ h₂ => exact ElemMove.cycDel l₁ l₂ c w (rotRev_mono h hc) h₁ h₂

theorem moves_mono {C C' : Set (List V)} (h : C ⊆ C') {p q : List V}
    (hm : Moves Γ C p q) : Moves Γ C' p q := by
  induction hm with
  | refl => exact Relation.ReflTransGen.refl
  | tail _ hbc ih => exact ih.tail (hbc.mono h)

theorem InClosure.mono {C C' : Set (List V)} (h : C ⊆ C') {c : List V}
    (hc : InClosure Γ C c) : InClosure Γ C' c := by
  obtain ⟨w, hw⟩ := hc
  exact ⟨w, moves_mono h hw⟩

end Mono

section Base

variable {G : Type v} [Group G] {X : Type u} [MulAction G X]

theorem isBase_of_triangulable {Γ : SimpleGraph X} {ΓI : Γ.Subgraph} (htri : Triangulable Γ)
    (hplane : ∀ p : List X, IsNGon Γ 3 p →
      ∃ (c₀ : List X) (g : G), IsSubCycle ΓI c₀ ∧ p = c₀.map (g • ·)) :
    IsBase G Γ ΓI := by
  intro c hc
  refine (htri c hc).mono ?_
  intro p hp
  exact hplane p hp

end Base

end CFSG.Quasithin.Asc94
