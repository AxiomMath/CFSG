module

public import CFSG.Timmesfeld.Bridge.RootStructR2KOneBender

public section

namespace CFSG.Timmesfeld.Bridge

open CFSG.Timmesfeld

theorem thinGateOne_kOne : ∀ (G : Type) [Group G] (D : Set G) (q : ℕ),
    ThinGateCounter G D → ThinGateCount G D q 1 1 → False := by
  intro G _ D q C K
  obtain ⟨a, x, y, h, T₁, T₂, K1⟩ := RootKOne.exists_kOneConf C K
  rcases K1.isBenderGroup with ⟨m, hm, e⟩ | ⟨m, hm, e⟩ | ⟨m, hm, e⟩
  · exact K1.false_of_psl2 rfl hm e
  · exact K1.false_of_suzuki rfl hm e
  · exact K1.false_of_psu3 rfl hm e

end CFSG.Timmesfeld.Bridge
