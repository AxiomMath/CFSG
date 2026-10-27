module

public import CFSG.Quasithin.H13.AS91Sec5Defs
public import CFSG.Quasithin.H13.AS91Sec1Four

public section

namespace CFSG.Quasithin.H13.AS91

open CFSG.Quasithin.Asc94

@[expose] def Stmt7_9 : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
    Triangulable c.Delta

theorem stmt7_9_of_hypB
    (h : ∀ (G : Type) [Group G] [Finite G] (z : G) (_ : HypJ4 G z) (c : Loc49 G z),
      ∃ (N : ℕ) (R : ℕ → (G ⧸ c.G1) → (G ⧸ c.G1) → (G ⧸ c.G1) → Prop), HypB c.Delta N R) :
    Stmt7_9 := by
  intro G _ _ z hz c
  obtain ⟨N, R, hR⟩ := h G z hz c
  exact triangulable_of_hypB hR

end CFSG.Quasithin.H13.AS91
