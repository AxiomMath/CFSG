module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Contradiction
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.ProofsEightPrelim
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.Ctx2311Exists

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem s23_11_of_exists (D : Data G) (Ch : Choice2011 G) (hE : UC22P20gExcFacts)
    (h207 : S20_7 D) (h52 : S23_5_2 D Ch) (h53 : S23_5_3 D Ch) (h10 : S23_10 D Ch)
    (h211 : S23_21_1 D Ch) (h212 : S23_21_2 D Ch)
    (hX : H1930 D → ∀ c : Ctx23L D Ch,
      CFSG.LocalAnalysis.UniquenessCase.PartTwo.IsSLn (Bar2 c.L) 3 (CFSG.Open.pRank 2 D.Z) →
        ∃ X : Subgroup G, IsMaximalParabolicOf c.L X ∧ D.T ⊓ c.L ≤ X ∧ ¬ X ≤ D.M) :
    S23_11 D Ch := by
  intro h1930 c hSL3
  obtain ⟨X, hXpar, hTX, hXM⟩ := hX h1930 c hSL3
  let c2 : Ctx2311 D Ch :=
    { toCtx23L := c, hSL3 := hSL3, X := X, hX := hXpar, hTX := hTX, hXM := hXM }
  have h43 : S23_43 D Ch := by
    intro h _
    exact ⟨h211 h c2, fun p hp hdvd =>
      (Set.eq_empty_iff_forall_notMem.mp (h212 h c2)) p
        ⟨hp, (D.sig_prime p hp).1, hdvd⟩⟩
  have hn3 : 3 ≤ c.n := uc22p20g_hn3_of hE D Ch h207 h1930 c.toCtx23.toCtx21
  have hn : 2 ≤ CFSG.Open.pRank 2 D.Z := by
    rcases h52 h1930 c with h | ⟨-, -, h⟩
    · rw [h] at hn3
      omega
    · rw [h] at hn3
      omega
  exact false_of_s23_43 D Ch h1930 c.withB0 rfl h52 h53 h10 h43 hn

theorem s23_11_of (D : Data G) (Ch : Choice2011 G) (hE : UC22P20gExcFacts)
    (h207 : S20_7 D) (h52 : S23_5_2 D Ch) (h53 : S23_5_3 D Ch) (h10 : S23_10 D Ch)
    (h211 : S23_21_1 D Ch) (h212 : S23_21_2 D Ch) : S23_11 D Ch :=
  s23_11_of_exists D Ch hE h207 h52 h53 h10 h211 h212 fun h c hSL3 =>
    c.exists_maxParabolic_of_isSLn h hSL3

end CFSG.LocalAnalysis.UniquenessCase.UC22
