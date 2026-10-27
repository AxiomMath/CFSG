module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec3SevenRefl

public section

namespace CFSG.Quasithin.Fan86

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

namespace Sec3Seven

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem false_of_ls4_rs4 (F : FanTree Γ G) (h40 : Fan40 F) (h36 : Fan36 F) (T : Track Γ G)
    {b : ℤ} (hl : LS4 Γ G T.line b) (hr : RS4 Γ G T.line b) : False := by
  by_cases hv : valence Γ (T.line.vert b) = 3
  · have hv1 : valence Γ (T.line.vert (b + 1)) ≠ 3 := fun h =>
      F.alternating _ _ (T.line.adj b) (hv.trans h.symm)
    have hP1 : (T.line.arc b 6).vert 1 = T.line.vert (b + 1) := by simp [arc_vert]
    have hL : LeftSingular Γ G (T.line.arc b 6).vert 2 6 :=
      (leftSingular_arc_iff F T.line b (n := 6) (i := 2) (by norm_num)).2
        (ls4_of_add_two_mul F T 1 (by push_cast; ring) hl)
    have hR : RightSingular Γ G (T.line.arc b 6).vert 0 4 :=
      (rightSingular_arc_iff F T.line b (n := 6) (i := 0) (by norm_num)).2
        (rs4_of_add_two_mul F T 0 (by push_cast; ring) hr)
    exact (h36 h40 (T.line.arc b 6) (by rw [hP1]; exact hv1)).2.2 ⟨hL, hR⟩
  · have hP1 : (T.line.arc (b - 1) 6).vert 1 = T.line.vert b := by simp [arc_vert]
    have hL : LeftSingular Γ G (T.line.arc (b - 1) 6).vert 1 5 :=
      (leftSingular_arc_iff F T.line (b - 1) (n := 6) (i := 1) (by norm_num)).2
        (ls4_of_add_two_mul F T 0 (by push_cast; ring) hl)
    have hR : RightSingular Γ G (T.line.arc (b - 1) 6).vert 1 5 :=
      (rightSingular_arc_iff F T.line (b - 1) (n := 6) (i := 1) (by norm_num)).2
        (rs4_of_add_two_mul F T 0 (by push_cast; ring) hr)
    exact (h36 h40 (T.line.arc (b - 1) 6) (by rw [hP1]; exact hv)).2.1 ⟨hL, hR⟩

theorem not_lineSingLe_four (F : FanTree Γ G) (h40 : Fan40 F) (h36 : Fan36 F) (T : Track Γ G)
    (hT : HasLenTwoReflection Γ G T) : ¬ LineSingLe Γ G T.line 4 := by
  rintro ⟨k, a, hk1, hk4, hsing⟩
  have key : LS4 Γ G T.line a ∨ RS4 Γ G T.line a → False := fun ha => by
    obtain ⟨b, hl, hr⟩ := exists_ls4_and_rs4 F T hT ha
    exact false_of_ls4_rs4 F h40 h36 T hl hr
  rcases Nat.lt_or_ge k 4 with hlt | hge
  · rcases hsing with hR | hL
    · exact h40 k hk1 hlt ⟨T.line.arc a k, hR⟩
    · exact h40 k hk1 hlt ⟨(T.line.arc a k).rev, rightSingular_rev_of_leftSingular hk1 _ hL⟩
  · obtain rfl : k = 4 := by omega
    rcases hsing with hR | hL
    · refine key (Or.inr ?_)
      have := (rightSingular_arc_iff F T.line a (n := 4) (i := 0) le_rfl).1 hR
      exact rs4_of_add_two_mul F T 0 (by simp) this
    · refine key (Or.inl ?_)
      have := (leftSingular_arc_iff F T.line a (n := 4) (i := 0) le_rfl).1 hL
      exact ls4_of_add_two_mul F T 0 (by simp) this

end Sec3Seven

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

end CFSG.Quasithin.Fan86
