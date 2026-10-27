module

public import CFSG.LocalAnalysis.StandardType.GGCorFiveTwentyUDefs

public section

namespace CFSG.StandardType

open CFSG.Assembly

namespace KGA

theorem ggTorusSelfCent_restrict_image {p : ℕ} {X : Type} [Group X] (A : Subgroup (MulAut X))
    (J : Subgroup X) (res : A →* MulAut J)
    (hres : ∀ (a : A) (x : J), ((res a x : J) : X) = (a : MulAut X) (x : X))
    (hSC : GGTorusSelfCent p A) : GGTorusSelfCent p res.range := by
  intro n hn hnp
  have hfix : ∀ a ∈ A, (a : MulAut X) (n : X) = n := by
    intro a ha
    rw [← hres ⟨a, ha⟩ n]
    exact congrArg Subtype.val (hn _ ⟨⟨a, ha⟩, rfl⟩)
  have hnpX : (n : X) ^ p = 1 := by
    have := congrArg Subtype.val hnp
    simpa using this
  refine ⟨⟨MulAut.conj (n : X), hSC (n : X) hfix hnpX⟩, ?_⟩
  ext x
  rw [hres]
  simp [MulAut.conj_apply]

end KGA

end CFSG.StandardType

end
