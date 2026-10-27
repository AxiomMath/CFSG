module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.ComponentTorus
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.InP11OfStrongly
public import CFSG.LocalAnalysis.UniquenessCase.UC22P22za
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataKParam
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.StatementsA

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem false_of_permuting_elemAbelian_rank_four {D : Data G} {V₀ V L : Subgroup G}
    {hV : Hyp125 D V₀ V}
    (hL : L ∈ calC D.M) (h1 : R17_1At D V₀ V hV) (hSg : UC6S846.SigmaStd D) {r : ℕ}
    (hr : r.Prime) (hr2 : r ≠ 2) {E : Subgroup G} (hEM : E ≤ D.M)
    (hEel : CFSG.Open.IsElemAbelian r E) (hperm : Permutes E D.T)
    (hrank : 4 ≤ CFSG.Open.pRank r E) : False := by
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hL
  have h4 : 4 ≤ CFSG.Open.pRank r D.M :=
    hrank.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono r hr hEM)
  have hrsig : r ∈ D.sig := hSg.four_mem r hr hr2 h4
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M := UC6S846.sp_of_mem_sig hSg hns hrsig
  have hEp : IsPGroup r ↥E := hEel.isPGroup
  have hEnc : ¬ IsCyclic ↥E := by
    intro hcyc
    have := CFSG.SectionRank.pRank_le_one_of_isCyclic hr hcyc
    omega
  have hin : F11.InP11 D E := inP11_of_strongly hr hr2 hsp hEM hEp hEel.2 hEnc hperm
  have hcard : Nat.card E = r ^ CFSG.Open.pRank r E :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hr hEel
  have hlt : r ^ 2 < Nat.card E := by
    rw [hcard]
    exact Nat.pow_lt_pow_right hr.one_lt (by omega)
  exact h1.1 E ⟨hin, fun _ => ⟨r, hr, hEp, Or.inl hlt⟩⟩

theorem false_of_permuting_elemAbelian_rank_three {D : Data G} {V₀ V L : Subgroup G}
    {hV : Hyp125 D V₀ V}
    (hL : L ∈ calC D.M) (h1 : R17_1At D V₀ V hV) (hSg : UC6S846.SigmaStd D)
    (h13 : SigmaRankThree13 D)
    {r : ℕ} (hr : r.Prime) (hr5 : 5 < r) (hE : evenRank G = 3) {E : Subgroup G} (hEM : E ≤ D.M)
    (hEel : CFSG.Open.IsElemAbelian r E) (hperm : Permutes E D.T)
    (hrank : 3 ≤ CFSG.Open.pRank r E) : False := by
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hL
  obtain ⟨p, hpσ⟩ := hSg.nonempty
  have hp3 : 3 ≤ CFSG.Open.pRank p D.M := hSg.three_le p hpσ
  have hp3' : CFSG.Open.pRank p D.M ≤ 3 := by
    have h := UC22.uc22p22za_pRank_le_evenRank (G := G) (p := p) (D.sig_prime p hpσ).1
      (D.sig_prime p hpσ).2 (H := D.M) D.maxLocal.1
    omega
  have h3 : 3 ≤ CFSG.Open.pRank r D.M :=
    hrank.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono r hr hEM)
  have hr7 : 7 ≤ r := by
    have h6 : r ≠ 6 := by rintro rfl; exact absurd hr (by norm_num)
    omega
  have hrsig : r ∈ D.sig := h13 ⟨p, hpσ, le_antisymm hp3' hp3⟩ r hr hr7 h3
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded r D.M := UC6S846.sp_of_mem_sig hSg hns hrsig
  have hEp : IsPGroup r ↥E := hEel.isPGroup
  have hEnc : ¬ IsCyclic ↥E := by
    intro hcyc
    have := CFSG.SectionRank.pRank_le_one_of_isCyclic hr hcyc
    omega
  have hin : F11.InP11 D E := inP11_of_strongly hr (by omega) hsp hEM hEp hEel.2 hEnc hperm
  have hcard : Nat.card E = r ^ CFSG.Open.pRank r E :=
    CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hr hEel
  have hlt : r ^ 2 < Nat.card E := by
    rw [hcard]
    exact Nat.pow_lt_pow_right hr.one_lt (by omega)
  exact h1.1 E ⟨hin, fun _ => ⟨r, hr, hEp, Or.inl hlt⟩⟩

theorem false_of_permuting_elemAbelian_rank_two_of_k_one {D : Data G} {V₀ V : Subgroup G}
    {hV : Hyp125 D V₀ V}
    (h1 : R17_1At D V₀ V hV) (hk : D.k = 1)
    {E : Subgroup G} (hEM : E ≤ D.M) (hEel : CFSG.Open.IsElemAbelian 3 E)
    (hperm : Permutes E D.T) (hrank : 2 ≤ CFSG.Open.pRank 3 E) : False := by
  classical
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M := by
    by_contra h
    have hk2 : D.k = 2 := (Data.k_eq_two_iff D).2 h
    omega
  have hEnc : ¬ IsCyclic ↥E := by
    intro hcyc
    have := CFSG.SectionRank.pRank_le_one_of_isCyclic Nat.prime_three hcyc
    omega
  have hin : F11.InP11 D E :=
    inP11_of_strongly Nat.prime_three (by norm_num) hsp hEM hEel.isPGroup hEel.2 hEnc hperm
  have hk2 : D.k = 2 := (h1.2 ⟨E, hin⟩).2.1
  omega

section CartanQuotient

variable {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}

theorem mem_calC_of_mem_conjSetOf (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    {K : Subgroup G} (hK : K ∈ UC22.conjSetOf D.M L) : K ∈ calC X :=
  mem_calC_of_mem_conjSetOf_of_calC (D := D) (L := L) (X := X) ctx.mem_calC ctx.X_eq hK

end CartanQuotient

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
