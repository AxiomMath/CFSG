module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.SeventeenFortyFour
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.BorelTorusAbelianHolds

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.QuasithinUnique (IsSylowTwoOf)
open scoped Pointwise commutatorElement

variable {G : Type} [Group G] [Finite G]

theorem exists_permuting_elemAbelian_of_ctx_of_borel {D : Data G} {V₀ V L X : Subgroup G}
    {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    {f : ℕ} (hB : Inputs1719.BorelChevOver (BarInf L) f)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ∃ E : Subgroup G, E ≤ D.M ∧ CFSG.Open.IsElemAbelian r E ∧ Permutes E D.T ∧
      CFSG.Open.pRank r Dc ≤ CFSG.Open.pRank r E := by
  classical
  have hXM : X ≤ D.M := by
    rw [ctx.X_eq]
    exact uc22p22v_conjClosure_le (Subgroup.le_normalizer (H := D.M)) ctx.mem_calC.1.le
  have hGamma : Gamma ⊆ D.M ⊓ normalizer ((D.T ⊓ X : Subgroup G) : Set G) :=
    ctx.reps.1
  have hDcB : Dc ≤ X ⊓ normalizer ((D.T ⊓ X : Subgroup G) : Set G) := by
    rw [ctx.Dc_eq]
    exact iSup_conj_cartan_le_borel (D := D) (L := L) (X := X) (C := C)
      ctx.mem_calC ctx.X_eq ctx.cartan hGamma
  obtain ⟨E, hEB, hEel, hperm, hrankB⟩ :=
    exists_permuting_elemAbelian_of_calC_of_borel (D := D) (L := L) (X := X) (n := f)
      ctx.mem_calC ctx.X_eq hB hr hr2
  exact ⟨E, hEB.trans (inf_le_left.trans hXM), hEel, hperm,
    (CFSG.SectionRank.pRank_mono hr.one_lt hDcB).trans hrankB⟩

theorem exists_permuting_elemAbelian_of_ctx {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hK3 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_BorelTorusAbelian)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) :
    ∃ E : Subgroup G, E ≤ D.M ∧ CFSG.Open.IsElemAbelian r E ∧ Permutes E D.T ∧
      CFSG.Open.pRank r Dc ≤ CFSG.Open.pRank r E :=
  exists_permuting_elemAbelian_of_ctx_of_borel ctx
    (Inputs1719.BorelChevOver.of_chev hK3 ctx.chev) hr hr2

theorem pRank_Dc_le_three_of_borel {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    {f : ℕ} (hB : Inputs1719.BorelChevOver (BarInf L) f)
    (h1 : R17_1At D V₀ V ctx.hyp125) (hSg : UC6S846.SigmaStd D)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) : CFSG.Open.pRank r Dc ≤ 3 := by
  classical
  obtain ⟨E, hEM, hEel, hperm, hrank⟩ :=
    exists_permuting_elemAbelian_of_ctx_of_borel ctx hB hr hr2
  by_contra hcon
  push Not at hcon
  exact false_of_permuting_elemAbelian_rank_four ctx.mem_calC h1 hSg hr hr2 hEM hEel hperm
    (by omega)

theorem seventeen_fortyfour_one_of_borel {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (h1 : R17_1At D V₀ V hV) (hSg : UC6S846.SigmaStd D) :
    R17_44_1AtB D V₀ V :=
  fun L X p n l C Dc Gamma ctx f hB r hr hr2 =>
    pRank_Dc_le_three_of_borel ctx hB h1 hSg hr hr2

theorem seventeen_fortyfour_one {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h1 : R17_1At D V₀ V hV) (hSg : UC6S846.SigmaStd D)
    (hK3 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_BorelTorusAbelian) :
    R17_44_1At D V₀ V :=
  (seventeen_fortyfour_one_of_borel hV h1 hSg).toAt hK3

theorem seventeen_fortyfour_two_of_borel {D : Data G} {V₀ V : Subgroup G}
    (hV : Hyp125 D V₀ V) (h1 : R17_1At D V₀ V hV) (hSg : UC6S846.SigmaStd D)
    (h13 : SigmaRankThree13 D) : R17_44_2AtB D V₀ V := by
  classical
  intro L X p n l C Dc Gamma ctx f hB r hr hr5 hcase
  obtain ⟨E, hEM, hEel, hperm, hrank⟩ :=
    exists_permuting_elemAbelian_of_ctx_of_borel ctx hB hr (by omega)
  by_contra hcon
  push Not at hcon
  rcases hcase with h3 | hstrong
  · exact false_of_permuting_elemAbelian_rank_three ctx.mem_calC h1 hSg h13 hr hr5 h3 hEM hEel
      hperm (by omega)
  · have hEp : IsPGroup r ↥E := hEel.isPGroup
    have hEnc : ¬ IsCyclic ↥E := by
      intro hcyc
      have := CFSG.SectionRank.pRank_le_one_of_isCyclic hr hcyc
      omega
    have hin : F11.InP11 D E :=
      inP11_of_strongly hr (by omega) hstrong hEM hEp hEel.2 hEnc hperm
    have hcard : Nat.card E = r ^ CFSG.Open.pRank r E :=
      CFSG.GroupTheory.card_eq_pow_pRank_of_isElemAbelian hr hEel
    have hlt : r ^ 2 < Nat.card E := by
      rw [hcard]
      exact Nat.pow_lt_pow_right hr.one_lt (by omega)
    exact h1.1 E ⟨hin, fun _ => ⟨r, hr, hEp, Or.inl hlt⟩⟩

theorem seventeen_fortyfour_two {D : Data G} {V₀ V : Subgroup G} (hV : Hyp125 D V₀ V)
    (h1 : R17_1At D V₀ V hV) (hSg : UC6S846.SigmaStd D) (h13 : SigmaRankThree13 D) :
    R17_44_2At D V₀ V := by
  have hK3 : Inputs1719.K_BorelTorusAbelian := Inputs1719.k_BorelTorusAbelian_holds
  exact (seventeen_fortyfour_two_of_borel hV h1 hSg h13).toAt hK3

theorem pRank_three_Dc_le_one_of_k_one_of_borel {D : Data G} {V₀ V L X : Subgroup G}
    {p n l : ℕ} {C Dc : Subgroup G} {Gamma : Set G}
    (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    {f : ℕ} (hB : Inputs1719.BorelChevOver (BarInf L) f)
    (h1 : R17_1At D V₀ V ctx.hyp125) (hk : D.k = 1) :
    CFSG.Open.pRank 3 Dc ≤ 1 := by
  classical
  obtain ⟨E, hEM, hEel, hperm, hrank⟩ :=
    exists_permuting_elemAbelian_of_ctx_of_borel ctx hB Nat.prime_three (by norm_num)
  by_contra hcon
  push Not at hcon
  exact false_of_permuting_elemAbelian_rank_two_of_k_one h1 hk hEM hEel hperm (by omega)

theorem pRank_three_Dc_le_one_of_k_one {D : Data G} {V₀ V L X : Subgroup G} {p n l : ℕ}
    {C Dc : Subgroup G} {Gamma : Set G} (ctx : Ctx17_42 D V₀ V L X p n l C Dc Gamma)
    (hK3 : CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.K_BorelTorusAbelian)
    (h1 : R17_1At D V₀ V ctx.hyp125) (hk : D.k = 1) :
    CFSG.Open.pRank 3 Dc ≤ 1 :=
  pRank_three_Dc_le_one_of_k_one_of_borel ctx
    (Inputs1719.BorelChevOver.of_chev hK3 ctx.chev) h1 hk

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
