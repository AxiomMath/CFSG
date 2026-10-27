module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamArith
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamPSLRank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamPSLCent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamPSLField
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamPSLTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamPSURank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamPSUCent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamPSUField
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamPSUTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamPSp4Rank
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamPSp4Cent
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamPSp4Field
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg.FamPSp4Torus

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg

open CFSG.Open Subgroup
open CFSG.Blueprint (LieModel)

theorem center_eq_bot_of_sit {J : Type} [Group J] [Finite J] (hs : Sit J) :
    Subgroup.center J = ⊥ := by
  obtain ⟨hsimple, ⟨a, b, hab⟩, -⟩ := hs
  haveI := hsimple
  rcases IsSimpleGroup.eq_bot_or_eq_top_of_normal (Subgroup.center J) with h | h
  · exact h
  · exfalso
    have : a ∈ Subgroup.center J := by rw [h]; trivial
    exact hab ((Subgroup.mem_center_iff.mp this b).symm)

private theorem k330c_two_le_pow {p f : ℕ} (hp : p.Prime) (hf : 1 ≤ f) : 2 ≤ p ^ f :=
  le_trans hp.two_le (Nat.le_self_pow (by omega) p)

private theorem k330c_two_le_of_pow {p f k : ℕ} (hp : p.Prime) (hf : 1 ≤ f) (hk : k ^ 7 = p ^ f) :
    2 ≤ k := by
  have h2 := k330c_two_le_pow hp hf
  by_contra hlt
  have : k ≤ 1 := by omega
  have : k ^ 7 ≤ 1 := by simpa using Nat.pow_le_pow_left this 7
  omega

theorem excl_PSL (n : ℕ) (hn : n = 4 ∨ n = 5) {J : Type} [Group J]
    [Finite J] {p f : ℕ} (hs : Sit J) (e : LieModel J .PSL n p f) (hq : p ^ f % 3 = 2) :
    Excl J := by
  obtain ⟨hp, hf, -⟩ := e.admissible
  refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
  · by_cases hcase : p = 7 ∨ 7 ∣ (p ^ f) ^ 2 - 1
    · exact sevenRankFree_of_two_le_pRank (rank_PSL n hn e hcase)
    · obtain ⟨hp7, h7⟩ := not_or.mp hcase
      exact sevenRankFree_of_noSevenCent (cent_PSL n hn e hq hp7 h7)
  · refine sevenStep_of_hasField (center_eq_bot_of_sit hs)
      (hasField_of_rp_torus (hasFieldRP_PSL n hn e) (torusBig_PSL n hn e hq) ?_)
    intro k hk
    have := sltBound_lt_torusLow n hn k (k330c_two_le_of_pow hp hf hk)
    rwa [hk] at this

theorem excl_PSU (n : ℕ) (hn : n = 4 ∨ n = 5) {J : Type} [Group J]
    [Finite J] {p f : ℕ} (hs : Sit J) (e : LieModel J .PSU n p f) (hq : p ^ f % 3 = 1) :
    Excl J := by
  obtain ⟨hp, hf, -⟩ := e.admissible
  refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
  · by_cases hcase : p = 7 ∨ 7 ∣ (p ^ f) ^ 2 - 1
    · exact sevenRankFree_of_two_le_pRank (rank_PSU n hn e hcase)
    · obtain ⟨hp7, h7⟩ := not_or.mp hcase
      exact sevenRankFree_of_noSevenCent (cent_PSU n hn e hq hp7 h7)
  · refine sevenStep_of_hasField (center_eq_bot_of_sit hs)
      (hasField_of_rp_torus (hasFieldRP_PSU n hn e) (torusBig_PSU n hn e hq) ?_)
    intro k hk
    have := sltBound_lt_torusLow n hn k (k330c_two_le_of_pow hp hf hk)
    rwa [hk] at this

theorem excl_PSp4 {J : Type} [Group J] [Finite J] {p f : ℕ}
    (hs : Sit J) (e : LieModel J .PSp 2 p f) : Excl J := by
  obtain ⟨hp, hf, -⟩ := e.admissible
  refine Or.inr (Or.inr (Or.inr ⟨?_, ?_⟩))
  · by_cases hcase : p = 7 ∨ 7 ∣ (p ^ f) ^ 2 - 1
    · exact sevenRankFree_of_two_le_pRank (rank_PSp4 e hcase)
    · obtain ⟨hp7, h7⟩ := not_or.mp hcase
      exact sevenRankFree_of_noSevenCent (cent_PSp4 e hp7 h7)
  · refine sevenStep_of_hasField (center_eq_bot_of_sit hs)
      (hasField_of_rp_torus (hasFieldRP_PSp4 e) (torusBig_PSp4 e) ?_)
    intro k hk
    have := spBound_lt_spTorusLow k (k330c_two_le_of_pow hp hf hk)
    rwa [hk] at this

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.K330Cfg
