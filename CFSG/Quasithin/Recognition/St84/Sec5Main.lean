module

public import CFSG.Quasithin.Recognition.St84.Sec5CaseA
public import CFSG.Quasithin.Recognition.St84.Sec5CaseB
public import CFSG.Quasithin.Recognition.St84.Sec5CaseC
public import CFSG.Quasithin.Recognition.St84.HigmanQuadProof

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86

variable {V G : Type} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s n₀ : ℕ}

namespace Setup

theorem sec5_trichotomy (Y : Setup Γ G) (H : Y.Sec5Hyp s n₀) :
    (n₀ = 2 ∧ s = 5 ∧ Y.swap.TreeU42Data) ∨ (s = 7 ∧ Y.TreeD4Data n₀) ∨
      (n₀ = 2 ∧ s = 5 ∧ Y.swap.TreeJ2Data ∧ Y.J2Arc) := by
  obtain ⟨r, -, -, hr⟩ := exists_isMaxRegLen Y H
  by_cases hZ : Y.Zt 0 = ⊥
  · obtain ⟨-, -, -, hcase⟩ := s52_step11 Y H hZ hr
    rcases hcase with ⟨h7, -⟩ | ⟨h5, -⟩
    · exact Or.inr (Or.inl ⟨h7, treeD4_of_caseB Y H hZ h7⟩)
    · obtain ⟨hn, -⟩ := caseC_n Y H hZ h5
      exact Or.inr (Or.inr ⟨hn, h5, treeJ2_of_caseC Y H hZ h5, j2Arc_of_five Y H hZ h5⟩)
  · exact Or.inl (treeU42_of_caseA Y H hZ (higmanQuad n₀))

theorem sec5_false_of_four_le (Y : Setup Γ G)
    (H : Y.Sec5Hyp s n₀) (h4 : 4 ≤ n₀) :
    False := by
  rcases sec5_trichotomy Y H with ⟨h2, -, -⟩ | ⟨-, hD⟩ | ⟨h2, -, -⟩
  · omega
  · have h3 := hD.n_eq_three H.two_le
    omega
  · omega

theorem sec5_two (Y : Setup Γ G) (H : Y.Sec5Hyp s 2) :
    s = 5 ∧ (Y.swap.TreeU42Data ∨ (Y.swap.TreeJ2Data ∧ Y.J2Arc)) := by
  rcases sec5_trichotomy Y H with ⟨-, h5, hU⟩ | ⟨-, hD⟩ | ⟨-, h5, hJ, hJArc⟩
  · exact ⟨h5, Or.inl hU⟩
  · exact hD.false_of_two.elim
  · exact ⟨h5, Or.inr ⟨hJ, hJArc⟩⟩

end Setup

theorem sec5_S3A5_univ_odd (hc : CharTwoStab (V := V) (G := G))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (Y : Setup Γ G) (hY0 : Y.n 0 = 1) (hY1 : Y.n 1 = 2)
    (hGT : Odd (Nat.card Y.GT)) :
    s = 5 ∧ (Y.TreeU42Data ∨ Y.TreeJ2Data) := by
  have H : Y.swap.Sec5Hyp s 2 :=
    ⟨hc, le_rfl, by rw [Setup.swap_n]; simpa using hY1,
      by rw [Setup.swap_n]; simpa using hY0, hs, hodd, h5, by rw [Setup.swap_GT]; exact hGT⟩
  obtain ⟨h5', hU | ⟨hJ, -⟩⟩ := Setup.sec5_two Y.swap H
  · exact ⟨h5', Or.inl (Setup.TreeU42Data.congr (X := Y.swap.swap) (Y := Y)
      (by simp) (by simp) hU)⟩
  · exact ⟨h5', Or.inr (Setup.TreeJ2Data.congr (X := Y.swap.swap) (Y := Y)
      (by simp) (by simp) hJ)⟩

theorem sec5_S3A5 (hc : CharTwoStab (V := V) (G := G))
    (X : Setup Γ G)
    (hn0 : X.n 0 = 1 ∨ X.n 0 = 2) (hn1 : X.n 1 = 1 ∨ X.n 1 = 2) (hne : X.n 0 ≠ X.n 1)
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s)
    (hGT : Odd (Nat.card X.GT)) :
    s = 5 ∧ ((X.n 0 = 1 ∧ (X.TreeU42Data ∨ X.TreeJ2Data)) ∨
      (X.n 1 = 1 ∧ X.swap.TreeU42Data)) := by
  have hor : (X.n 0 = 1 ∧ X.n 1 = 2) ∨ (X.n 0 = 2 ∧ X.n 1 = 1) := by
    rcases hn0 with h0 | h0 <;> rcases hn1 with h1 | h1
    · exact absurd (h0.trans h1.symm) hne
    · exact Or.inl ⟨h0, h1⟩
    · exact Or.inr ⟨h0, h1⟩
    · exact absurd (h0.trans h1.symm) hne
  rcases hor with ⟨h0, h1⟩ | ⟨h0, h1⟩
  · obtain ⟨h5', hU | hJ⟩ := sec5_S3A5_univ_odd hc hs hodd h5 X h0 h1 hGT
    · exact ⟨h5', Or.inl ⟨h0, Or.inl hU⟩⟩
    · exact ⟨h5', Or.inl ⟨h0, Or.inr hJ⟩⟩
  · have H : X.Sec5Hyp s 2 := ⟨hc, le_rfl, h0, h1, hs, hodd, h5, hGT⟩
    obtain ⟨h5', hU | ⟨hJ, hJArc⟩⟩ := Setup.sec5_two X H
    · exact ⟨h5', Or.inr ⟨h1, hU⟩⟩
    · exfalso
      obtain ⟨⟨hL, hR⟩, -⟩ := hJArc
      have hreg : Regular Γ G (X.line.arc 1 6) :=
        ⟨(X.leftTransitive_arc_iff 1 6).mpr (by simpa using hL),
          (X.rightTransitive_arc_iff 1 (by norm_num)).mpr (by simpa using hR)⟩
      have hpar := (odd_orbit_of_rightSingular X.hyp.isTree X.hyp.adj_smul
        (fun v x y hx hy => X.hyp.locTrans hx hy) X.hyp.edgeTrans X.hyp.preservesParts
        hs hX).2 6 (by omega) (X.line.arc 1 6) hreg
      have h01 : Even (Γ.dist (X.vert 0) (X.vert 1)) := by
        simpa [Line.arc] using hpar.1
      have hdist : Γ.dist (X.vert 0) (X.vert 1) = 1 := by
        have h := Line.dist_eq X.hyp.isTree X.line (i := (0 : ℤ)) (j := 1) (by norm_num)
        simpa using h
      rw [hdist] at h01
      obtain ⟨m, hm⟩ := h01
      omega

theorem sec5_S3A5_univ (hc : CharTwoStab (V := V) (G := G))
    (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (h6 : ∀ X : Setup Γ G, ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s →
      Even (Nat.card X.GT) → False)
    (Y : Setup Γ G) (hY0 : Y.n 0 = 1) (hY1 : Y.n 1 = 2) :
    s = 5 ∧ (Y.TreeU42Data ∨ Y.TreeJ2Data) := by
  rcases Nat.even_or_odd (Nat.card Y.GT) with hEven | hOdd
  · exfalso
    obtain ⟨o, ho, -⟩ := exists_odd_orbit Y.hyp.isTree Y.hyp.adj_smul
      (fun v x y hx hy => Y.hyp.locTrans hx hy) Y.hyp.edgeTrans Y.hyp.preservesParts hs hodd
    rcases Nat.even_or_odd (Γ.dist o (Y.vert 0)) with hd0 | hd0
    · have hend : Odd (Γ.dist o (Y.vert (s : ℤ))) := Y.odd_dist_vert_of_even o hodd hd0
      have hX : ¬ RightTransitive Γ G (Y.line.arc 0 s).vert 0 s :=
        (ho s le_rfl (Y.line.arc 0 s)).1 (by simpa [Line.arc] using hend)
      exact h6 Y hX hEven
    · have hend : Odd (Γ.dist o (Y.vert ((s : ℤ) + 1))) :=
        Y.odd_dist_vert_succ_of_odd o hodd hd0
      have hX : ¬ RightTransitive Γ G ((Y.shift 1).line.arc 0 s).vert 0 s :=
        (ho s le_rfl ((Y.shift 1).line.arc 0 s)).1
          (by simpa [Line.arc] using hend)
      exact h6 (Y.shift 1) hX (by simpa [Setup.shift_GT] using hEven)
  · exact sec5_S3A5_univ_odd hc hs hodd h5 Y hY0 hY1 hOdd

end CFSG.Quasithin.St84
