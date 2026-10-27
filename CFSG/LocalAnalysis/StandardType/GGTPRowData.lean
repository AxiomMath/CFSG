module

public import CFSG.LocalAnalysis.StandardType.GGTPRowDataA
public import CFSG.LocalAnalysis.StandardType.GGTPRowDataTwA
public import CFSG.LocalAnalysis.StandardType.GGTPRowDataC
public import CFSG.LocalAnalysis.StandardType.GGTPRowDataD
public import CFSG.LocalAnalysis.StandardType.GGTPRowDataTwD

public section

namespace CFSG.StandardType

open CFSG CFSG.Assembly

theorem ggTPRowData {labK : LargeEvenLabel}
    (hrow : (labK.tag = .A ∧ (labK.rank = 6 ∨ labK.rank = 11 ∨ labK.rank = 12)) ∨
      (labK.tag = .twA ∧ labK.rank = 6) ∨ (labK.tag = .C ∧ labK.rank = 6) ∨
      (labK.tag = .D ∧ (labK.rank = 6 ∨ labK.rank = 7)) ∨ (labK.tag = .twD ∧ labK.rank = 7))
    (h3 : labK.tag = .A → labK.rank = 11 → 3 ∣ 2 ^ labK.n + 1)
    {Y : Type} [Group Y] (hY : GGHasLabel labK Y) : GGTPRowDatum Y := by
  rcases labK with ⟨t, r, n⟩
  rcases hrow with ⟨ht, hr⟩ | ⟨ht, hr⟩ | ⟨ht, hr⟩ | ⟨ht, hr⟩ | ⟨ht, hr⟩
  all_goals dsimp only at ht hr h3
  all_goals subst ht
  · exact ggTPRowData_A hr (h3 rfl) hY
  · subst hr; exact ggTPRowData_twA hY
  · subst hr; exact ggTPRowData_C hY
  · exact ggTPRowData_D hr hY
  · subst hr; exact ggTPRowData_twD hY

end CFSG.StandardType

end
