module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5P55Shift
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec5StmtA

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem fan55h1 (F : FanTree Γ G) (h54 : Fan54 F) : Fan55h1 F := by
  intro h40 ℓ z z' a b tL tR a' b' tL' tR' hz hz' hd hd' hpos
  have h1 := P55.cfix_a_lt hd
  have h2 := P55.cfix_tL_le hd
  have h3 := P55.cfix_le_tR hd
  have h4 := P55.cfix_a_lt hd'
  have h5 := P55.cfix_tL_le hd'
  have h6 := P55.cfix_le_tR hd'
  have hnc : z * z' ≠ z' * z := by
    have key := h54 h40 ℓ z' a' b' hz' hd'.core
    have hzfix : z • ℓ.vert tR = ℓ.vert tR := (hd.fix tR).2 ⟨by omega, le_rfl⟩
    have hzmov : z • ℓ.vert (tR + 1) ≠ ℓ.vert (tR + 1) := fun h => by
      have := (hd.fix (tR + 1)).1 h
      omega
    rcases hpos with h | h
    · refine key a' (a' + 1) (Or.inr (Or.inr (Or.inl ⟨rfl, rfl⟩))) z ?_ ?_
      · rw [MulAction.mem_stabilizer_iff, h]; exact hzfix
      · rw [MulAction.mem_stabilizer_iff, h]; exact hzmov
    · refine key (a' - 1) a' (Or.inr (Or.inr (Or.inr ⟨rfl, rfl⟩))) z ?_ ?_
      · rw [MulAction.mem_stabilizer_iff, show a' - 1 = tR by omega]; exact hzfix
      · rw [MulAction.mem_stabilizer_iff, h]; exact hzmov
  by_contra hlt
  have hedge : z' ∈ ℓ.edgeCirc (G := G) (b - 1) := by
    refine P55.mem_edgeCirc_of_fix hz'.1 ((hd'.fix (b - 1)).2 ⟨by omega, by omega⟩) ?_
    rw [sub_add_cancel]
    exact (hd'.fix b).2 ⟨by omega, by omega⟩
  have hcen := (P55.cfix_cen hd (i := b - 1) (by omega) (by omega)).2 z' hedge
  exact hnc hcen.symm

theorem fan55h2 (F : FanTree Γ G) (h54 : Fan54 F) : Fan55h2 F := by
  intro h40 ℓ z z' a b tL tR a' b' tL' tR' hz hz' hd hd' hpos
  have h1 := P55.cfix_a_lt hd
  have h2 := P55.cfix_tL_le hd
  have h3 := P55.cfix_le_tR hd
  have h4 := P55.cfix_a_lt hd'
  have h5 := P55.cfix_tL_le hd'
  have h6 := P55.cfix_le_tR hd'
  have hnc : z' * z ≠ z * z' := by
    have key := h54 h40 ℓ z a b hz hd.core
    have hzfix : z' • ℓ.vert tL' = ℓ.vert tL' := (hd'.fix tL').2 ⟨le_rfl, by omega⟩
    rcases hpos with h | h
    · refine key tL' (b - 1) (Or.inl ⟨h, rfl⟩) z' ?_ ?_
      · rw [MulAction.mem_stabilizer_iff]; exact hzfix
      · rw [MulAction.mem_stabilizer_iff]
        intro hx
        have := (hd'.fix (b - 1)).1 hx
        omega
    · refine key tL' b (Or.inr (Or.inl ⟨h, rfl⟩)) z' ?_ ?_
      · rw [MulAction.mem_stabilizer_iff]; exact hzfix
      · rw [MulAction.mem_stabilizer_iff]
        intro hx
        have := (hd'.fix b).1 hx
        omega
  by_contra hlt
  have hedge : z ∈ ℓ.edgeCirc (G := G) a' := by
    refine P55.mem_edgeCirc_of_fix hz.1 ((hd.fix a').2 ⟨by omega, by omega⟩) ?_
    exact (hd.fix (a' + 1)).2 ⟨by omega, by omega⟩
  have hcen := (P55.cfix_cen hd' (i := a') le_rfl (by omega)).2 z hedge
  exact hnc hcen.symm

end CFSG.Quasithin.Fan86
