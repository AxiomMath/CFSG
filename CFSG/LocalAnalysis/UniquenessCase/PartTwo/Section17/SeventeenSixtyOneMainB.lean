module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenSixtyOneNonMainB

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.RankThree.PartOne (pElementSubgroup)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]


theorem p_ne_thirteen_of_main
    (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) (hThin : ThinList13) (hSg : SigmaStd D)
    {K : Subgroup G} (hK : K ∈ calC (Lp D p))
    (hdvd : p ∣ Nat.card (barImage D.M K))
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3)
    (hunique : ∀ K' ∈ calC (Lp D p), K' ≠ L →
      p ∣ Nat.card (barImage D.M K') → K' = K)
    (h56 : R17_56At D V₀ V) (h57 : R17_57At D V₀ V) :
    p ≠ 13 := by
  intro hp13
  have hpmem : p ∈ D.sig := ctx.hyp54.1
  have hpp : p.Prime := (D.sig_prime p hpmem).1
  have hns : s13_NormalSimple (Bar2 D.M) := normalSimple_of_hyp1754 D hThin ctx.hyp54
  have h3le : 3 ≤ CFSG.Open.pRank p D.M := hSg.three_le p hpmem
  have hSp1 : CFSG.Open.pRank p (Sp D p) ≤ 1 := h57 p ctx.hyp54
  have hLp1 : CFSG.Open.pRank p (Lp D p) ≤ 1 :=
    pRank_Lp_le_one_of_p13 D ctx hThin hK hdvd hshape hunique hp13
  have hp3 : p ≠ 3 := by rw [hp13]; norm_num
  have hMrank := pRank_M_eq_pRank_Lp_add_pRank_Sp D ctx hns h56 hp3
  omega

theorem p_eq_three_or_five_of_main
    (D : Data G) {V₀ V L : Subgroup G} {p : ℕ}
    (ctx : Ctx17_58 D V₀ V L p) {K : Subgroup G} (hK : K ∈ calC (Lp D p))
    (hdvd : p ∣ Nat.card (barImage D.M K))
    (hshape : IsL2 (Bar2 K) 3 ∨ IsSz (Bar2 K) 3)
    (hp7 : p ≠ 7) (hp13 : p ≠ 13) :
    p = 3 ∨ p = 5 := by
  have hpmem : p ∈ D.sig := ctx.hyp54.1
  have hpp : p.Prime := (D.sig_prime p hpmem).1
  have hp2 : p ≠ 2 := (D.sig_prime p hpmem).2
  have hKcalM : K ∈ calC D.M := calC_of_calC_Lp D hK
  rcases hshape with hL2 | hSz
  · exact Or.inl (p_eq_three_of_isL2_three hKcalM hpp hp2 hp7 hL2 hdvd)
  · rcases p_eq_five_or_thirteen_of_isSz_three hKcalM hpp hp2 hp7 hSz hdvd with h | h
    · exact Or.inr h
    · exact absurd h hp13


end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

