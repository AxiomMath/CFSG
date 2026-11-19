module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenNineTransfer
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenGlueB
public import CFSG.Quasithin.EmptyFaithful.R3cBase
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF3ThreeRankHolds
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.GF3PermutabilityHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.Quasithin CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open CFSG.Blueprint (LieModel)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem eq_three_of_prime_pow_le_three {r q f : ℕ} (hr : r.Prime) (hr2 : r ≠ 2)
    (hf : 1 ≤ f) (hq : q = r ^ f) (hle : q ≤ 3) : q = 3 := by
  have hr3 : 3 ≤ r := by
    have h2 : 2 ≤ r := hr.two_le
    omega
  have hqge : r ≤ q := by
    rw [hq]
    calc r = r ^ 1 := (pow_one r).symm
      _ ≤ r ^ f := Nat.pow_le_pow_right (by omega) hf
  have hrle : r ≤ 3 := hqge.trans hle
  have hreq : r = 3 := le_antisymm hrle hr3
  subst hreq
  have hf1 : f ≤ 1 := by
    have h := hle
    rw [hq] at h
    exact (Nat.pow_le_pow_iff_right (by norm_num : 1 < 3)).1 (by simpa using h)
  have hf1' : f = 1 := le_antisymm hf1 hf
  rw [hq, hf1']
  norm_num

theorem two_lt_pRank_three_of_qs (hK : Inputs1719.K_GF3_three_rank_qs)
    {D : Data G} {V₀ V L : Subgroup G} {r q : ℕ} (hC : Ctx17_6 D V₀ V L r q)
    (h8 : R17_8At D V₀ V L r q hC) (hq3 : q = 3) :
    2 < CFSG.Open.pRank 3 L := by
  by_contra hle
  push Not at hle
  obtain ⟨t, n, hadm, hlie⟩ := lie_three_of_q hC hq3
  obtain ⟨e⟩ := uc22p21k_barInf_equiv_of_calC hC.memL
  have hlie' : LieModel (Bar2 L ⧸ Subgroup.center (Bar2 L)) t n 3 1 :=
    LieModel.of_mulEquiv e hlie
  have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup (Bar2 L)) ≤ 2 := by
    rw [← R3c.pRank_three_eq_pCore_quotient]
    exact hle
  rcases hK (Bar2 L) t n hadm hC.memL.2.2 hlie' hrank with h | h
  · exact h8.1 h
  · exact h8.2 h

theorem seventeen_nine (D : Data G) (V₀ V L : Subgroup G) (r q : ℕ) (hC : Ctx17_6 D V₀ V L r q)
    (h17_1 : R17_1At D V₀ V hC.hyp125) (h17_8 : R17_8At D V₀ V L r q hC)
    (h82 : F08.R82 D)
    (hFC3 : Inputs1719.K_FunCommuteThree) :
    R17_9At D V₀ V L r q hC := by
  by_contra hlt
  have hq3 : q = 3 := by
    obtain ⟨hr, hr2, t, n, f, hadm, hq, -⟩ := hC.lie
    obtain ⟨-, hf, -⟩ := hadm
    exact eq_three_of_prime_pow_le_three hr hr2 hf hq (le_of_not_gt hlt)
  have hm3 : 2 < Open.pRank 3 L :=
    two_lt_pRank_three_of_qs Inputs1719.k_GF3_three_rank_qs_holds hC h17_8 hq3
  have hstr : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    h82 L ⟨hC.memL.1, hC.memL.2.1, hm3, Or.inl (s15_Three_qs_of_open hC.memL.2.2)⟩
  have hk : D.k = 1 :=
    CFSG.LocalAnalysis.UniquenessCase.PartTwo.Data.k_eq_one_of_isStronglyPEmbedded D hstr
  have hKp : Inputs1719.K_GF3_permutability :=
    Inputs1719.k_GF3_permutability_of_funCommuteThree hFC3
  obtain ⟨X, hXM, hXne, hXp, hXexp, hXnc, hperm⟩ :=
    exists_permutes_three_subgroup hKp hC h17_8 hq3
  have hin : F11.InP11 D X :=
    inP11_of_strongly Nat.prime_three (by norm_num) hstr hXM hXp hXexp hXnc hperm
  have hk2 := (h17_1.2 ⟨X, hin⟩).2.1
  omega

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
