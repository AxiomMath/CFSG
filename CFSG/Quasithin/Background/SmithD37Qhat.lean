module

public import CFSG.Quasithin.Background.D2Params

public section

namespace CFSG.Quasithin.SmithD37

variable {V : Type*} [CommGroup V] [Finite V]

theorem exists_mem_qhatStar {X : Subgroup (MulAut V)}
    (h : qhatOf X ≤ ((2 : ℚ) : WithTop ℚ)) : ∃ A, A ∈ QhatStar X := by
  have : Finite (MulAut V) := MulEquiv.finite_left
  obtain ⟨r, hr⟩ : ∃ r : ℚ, qhatOf X = (r : WithTop ℚ) := by
    rcases hq : qhatOf X with _ | r
    · rw [hq] at h
      exact absurd h (not_le.mpr (WithTop.coe_lt_top _))
    · exact ⟨r, rfl⟩
  have hr2 : r ≤ 2 := by
    rw [hr] at h
    exact WithTop.coe_le_coe.mp h
  obtain ⟨⟨A, hA, hAk, hAr⟩, -⟩ := kq_eq_coe_iff.mp (show kq X 3 = (r : WithTop ℚ) from hr)
  obtain ⟨B, hB⟩ := exists_minimal_le_of_wellFoundedLT (fun B => B ∈ kRle X 3 r) A
    ⟨⟨hA, hAr.le⟩, hAk⟩
  exact ⟨B, r, hr, hr2, hB.2.1, fun C hC hCB => le_antisymm hCB (hB.2.2 hC hCB)⟩

end CFSG.Quasithin.SmithD37
