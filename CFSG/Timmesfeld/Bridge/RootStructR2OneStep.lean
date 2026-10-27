module

public import CFSG.Timmesfeld.Bridge.RootStructR2OneQ
public import CFSG.Timmesfeld.Bridge.RootStructR2OneTwo

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

namespace RootOne

theorem thinGateOneStep_of
    (h1 : ∀ (G : Type) [Group G] (D : Set G) (q : ℕ), ThinGateCounter G D →
      ThinGateCount G D q 1 1 → False) : ThinGateOneStep := by
  intro G _ D q k C K hk
  rcases hk with rfl | rfl | rfl
  · exact h1 G D q C K
  · exact false_of_eq_two C K
  · exact false_of_eq_q C K

end RootOne

end CFSG.Timmesfeld.Bridge
