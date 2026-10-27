module

public import CFSG.Quasithin.Recognition.St84.Sec4Setup

public section

namespace CFSG.Quasithin.St84

open SimpleGraph CFSG.Open CFSG.QuasithinUnique CFSG.Quasithin.Fan86

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V} {s : ℕ}

theorem Setup.exists_sec4Hyp (hc : CharTwoStab (V := V) (G := G)) (X : Setup Γ G)
    (hn : ∀ v, 2 ≤ nOf Γ v) (hs : IsSingularity Γ G s) (hodd : Odd s) (h5 : 5 ≤ s)
    (hX : ¬ RightTransitive Γ G (X.line.arc 0 s).vert 0 s) (hGT : Odd (Nat.card X.GT)) :
    ∃ m, X.Sec4Hyp s (2 * m) := by
  obtain ⟨m, hle, hlong⟩ := X.exists_isLongReg hs hodd hX
  obtain ⟨ho, -⟩ := odd_orbit_of_rightSingular X.hyp.isTree X.hyp.adj_smul
    (fun v a b ha hb => X.hyp.locTrans ha hb) X.hyp.edgeTrans X.hyp.preservesParts hs hX
  have hends : ∀ (a : ℤ) (k : ℕ), s ≤ k →
      (X.RightTransAt a (a + k) → Even (a + k)) ∧
        (X.LeftTransAt a (a + k) → Even a) := by
    intro a k hk
    have hk1 : 1 ≤ k := by omega
    constructor
    · intro hR
      have hR' : RightTransitive Γ G (X.line.arc a k).vert 0 k :=
        (X.rightTransitive_arc_iff a hk1).mpr hR
      have hdist : Even (Γ.dist (X.vert 0) (X.vert (a + (k : ℤ)))) := by
        rcases Nat.even_or_odd (Γ.dist (X.vert 0) (X.vert (a + (k : ℤ)))) with hev | hodd_d
        · exact hev
        · exact absurd hR' ((ho k hk (X.line.arc a k)).1 (by simpa [Line.arc] using hodd_d))
      exact X.even_of_even_dist (a + (k : ℤ)) hdist
    · intro hL
      have hL' : LeftTransitive Γ G (X.line.arc a k).vert 0 k :=
        (X.leftTransitive_arc_iff a k).mpr hL
      have hdist : Even (Γ.dist (X.vert 0) (X.vert a)) := by
        rcases Nat.even_or_odd (Γ.dist (X.vert 0) (X.vert a)) with hev | hodd_d
        · exact hev
        · exact absurd hL' ((ho k hk (X.line.arc a k)).2 (by simpa [Line.arc] using hodd_d))
      exact X.even_of_even_dist a hdist
  exact ⟨m,
    { char := hc
      two_le_n := fun i => hn (X.vert i)
      sing := hs
      odd_s := hodd
      five_le := h5
      odd_GT := hGT
      longReg := hlong
      even_r := ⟨m, by omega⟩
      le_r := hle
      ends_even := hends }⟩

end CFSG.Quasithin.St84
