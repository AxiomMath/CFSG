module

public import CFSG.LocalAnalysis.StandardType.GGNbrTableForms

public section

namespace CFSG.StandardType

open CFSG.Assembly

theorem labelIso_dvd_markDeg {lab lab' : LargeEvenLabel} (hl : LargeEvenInLambda2 lab)
    (h : GGLabelIso lab lab') : lab.n ∣ markDeg lab' := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨t', r', n'⟩ := lab'
  unfold GGLabelIso at h
  simp only [LargeEvenLabel.mk.injEq] at h
  rcases h with h | ⟨-, hB', -, rfl⟩ | ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩ |
    ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩ | ⟨-, rfl, rfl, rfl⟩ | ⟨⟨rfl, rfl, -⟩, rfl, rfl, rfl⟩
  · obtain ⟨rfl, rfl, rfl⟩ := h
    cases t
    case twD => simp only [markDeg]; split_ifs <;> simp
    case B2der =>
      obtain rfl : n = 1 := hl.2.2
      simp [markDeg]
    case G2der =>
      obtain rfl : n = 1 := hl.2.2
      simp [markDeg]
    all_goals simp [markDeg]
  · rcases hB' with rfl | rfl <;> simp [markDeg]
  all_goals simp [markDeg]

namespace TableCRes

theorem markDeg_eq_of_ggLabelIso {lab lab' : LargeEvenLabel} (h : GGLabelIso lab lab') :
    markDeg lab = markDeg lab' := by
  obtain ⟨t, r, n⟩ := lab
  obtain ⟨t', r', n'⟩ := lab'
  rcases h with h | ⟨h1, h2, h3, h4⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ | ⟨h1, h2⟩ |
    ⟨h1, h2⟩
  · simp only [LargeEvenLabel.mk.injEq] at h
    obtain ⟨rfl, rfl, rfl⟩ := h
    rfl
  · simp only at h1 h2 h3 h4
    rcases h1 with rfl | rfl <;> rcases h2 with rfl | rfl <;> simp [markDeg, h4]
  all_goals simp_all [markDeg]

end TableCRes

end CFSG.StandardType
