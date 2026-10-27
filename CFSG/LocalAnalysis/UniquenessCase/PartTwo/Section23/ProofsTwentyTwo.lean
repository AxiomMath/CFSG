module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section23.OmegaPlusTorus
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2121For

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartTwo
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def S23_22Fitting (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, 2 ≤ CFSG.Open.pRank 2 D.Z → ∀ (r : ℕ) (a b t : G),
    Ctx23L.OmegaPlusTorus c r a b t → S23_6 D Ch →
    (∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) → S23_7_1 D Ch →
    D.sig.Nonempty → UC6.R6_7 D → IsCyclic ↥(CFSG.fittingSubgroup (Bar2 D.M))

@[expose] def S23_22Hyp2120 (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx23L D Ch, 2 ≤ CFSG.Open.pRank 2 D.Z → ∀ (r : ℕ) (a b t : G),
    Ctx23L.OmegaPlusTorus c r a b t → S23_6 D Ch →
    (∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M) → S23_8 D Ch →
    S21_23 D Ch → IsCyclic ↥(CFSG.fittingSubgroup (Bar2 D.M)) →
    Hyp2120For D (Subgroup.zpowers a)

namespace Ctx23L

variable {D : Data G} {Ch : Choice2011 G}

theorem mem_M_of_torus (c : Ctx23L D Ch) (h1930 : H1930 D) (h4 : S23_4 D Ch)
    {r : ℕ} {a b t : G} (hT : OmegaPlusTorus c r a b t) : a ∈ D.M := by
  have hNZ : Subgroup.normalizer (D.Z : Set G) = D.M := by
    rw [← (h4 h1930 c).1]
    exact D.normalizer_U_eq
  rw [← hNZ]
  exact Subgroup.centralizer_le_normalizer (D.Z : Set G) hT.a_centralizes

private theorem zpowers_ne_bot_of_torus (c : Ctx23L D Ch) {r : ℕ} {a b t : G}
    (hT : OmegaPlusTorus c r a b t) : Subgroup.zpowers a ≠ ⊥ := by
  intro hbot
  have h1 := hT.a_order
  rw [Subgroup.zpowers_eq_bot.mp hbot, orderOf_one] at h1
  exact hT.r_prime.ne_one h1.symm

private theorem mem_calB1_zpowers_of_torus (c : Ctx23L D Ch) {r : ℕ} {a b t : G}
    (hT : OmegaPlusTorus c r a b t) : Subgroup.zpowers a ∈ calB1 D.T D.M c.L := by
  have hinv : ∀ x ∈ Subgroup.zpowers a, t * x * t⁻¹ = x⁻¹ := by
    intro x hx
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.mp hx
    have h1 : t * a ^ n * t⁻¹ = MulAut.conj t (a ^ n) := (MulAut.conj_apply t (a ^ n)).symm
    rw [h1, map_zpow,
      show MulAut.conj t a = a⁻¹ from by rw [MulAut.conj_apply]; exact hT.t_inv_a, inv_zpow]
  have hB : Subgroup.zpowers a ∈ calB D.T D.M c.L := by
    refine ⟨Subgroup.zpowers_le.mpr hT.a_mem, Subgroup.isCyclic_zpowers a, ?_, ?_,
      hT.permutes, ⟨t, hT.t_mem, hT.t_not_mem_M, hT.t_order, hinv⟩⟩
    · rw [Nat.card_zpowers, hT.a_order]
      exact hT.r_prime.squarefree
    · rw [Nat.card_zpowers, hT.a_order]
      exact hT.r_prime.odd_of_ne_two hT.r_ne_two
  exact mem_calB1_of_mem_calB hB

end Ctx23L

theorem s23_22N_of (D : Data G) (Ch : Choice2011 G) (hE : UC22P20gExcFacts) (h207 : S20_7 D)
    (h52 : S23_5_2 D Ch) (h4 : S23_4 D Ch) (h6 : S23_6 D Ch) (h71 : S23_7_1 D Ch)
    (h8 : S23_8 D Ch) (h2121F : S21_21For D Ch) (h2123 : S21_23 D Ch) (h67 : UC6.R6_7 D)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (hsig : D.sig.Nonempty) (hK : KOrdNatural) (hS : KSchurL2) (hA : KTab23a) (hKP : KOmPlus)
    (hFit : S23_22Fitting D Ch) (hHyp : S23_22Hyp2120 D Ch) :
    H1930 D → ∀ c : Ctx23L D Ch, IsOmegaPlus (Bar2 c.L) 4 (CFSG.Open.pRank 2 D.Z) →
      (hV : IsElemAbelian 2 c.V) →
        IsOmegaPlus ↥(barSub ⊥ c.V hV c.L) 4 (CFSG.Open.pRank 2 D.Z) →
        NatOmegaPlus (barSub ⊥ c.V hV c.L) ⊤ ⊥ 4 (CFSG.Open.pRank 2 D.Z) → False := by
  intro h1930 c hP hV hPH hNat
  have hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z := (c.n_eq_of_isOmegaPlus hE h207 h52 h1930 hP).2
  have hn2 : 2 ≤ CFSG.Open.pRank 2 D.Z := le_trans (by norm_num) hn3
  obtain ⟨r, a, b, t, hT⟩ := c.exists_omegaPlusTorus hV h4 h1930 hA hK hS hKP hn2 hPH hNat
  have hcyc : IsCyclic ↥(CFSG.fittingSubgroup (Bar2 D.M)) :=
    hFit h1930 c hn2 r a b t hT h6 hsp h71 hsig h67
  have hHyp' : Hyp2120For D (Subgroup.zpowers a) :=
    hHyp h1930 c hn2 r a b t hT h6 hsp h8 h2123 hcyc
  have hX : Subgroup.zpowers a ∈ calB1 D.T D.M c.L :=
    Ctx23L.mem_calB1_zpowers_of_torus c hT
  have hXle : Subgroup.zpowers a ≤ D.M :=
    Subgroup.zpowers_le.mpr (Ctx23L.mem_M_of_torus c h1930 h4 hT)
  have hXne : Subgroup.zpowers a ≠ ⊥ := Ctx23L.zpowers_ne_bot_of_torus c hT
  obtain ⟨p, hp⟩ := hsig
  obtain ⟨hHinfEq, -, hex⟩ :=
    h2121F h1930 c.toCtx21 c.L c.hL.1 (Subgroup.zpowers a) hX hXle hXne hHyp' p hp
  obtain ⟨n, hcases, hn, -, -⟩ := hex
  rcases hcases with
    ⟨⟨A, B, hA', hB', ⟨eAB⟩, hLA, hLB⟩, -⟩ | ⟨⟨A, B, hA', hB', ⟨eAB⟩, hUA, hLB⟩, -⟩
  · exact false_of_s23_8_of_hinf_prod D Ch h8 h1930 c hn (hHinfEq.symm ▸ eAB) (Or.inl hLA) hLB
  · exact false_of_s23_8_of_hinf_prod D Ch h8 h1930 c hn (hHinfEq.symm ▸ eAB) (Or.inr hUA) hLB

theorem s23_22_of (D : Data G) (Ch : Choice2011 G) (hE : UC22P20gExcFacts) (h207 : S20_7 D)
    (h52 : S23_5_2 D Ch) (h4 : S23_4 D Ch) (h6 : S23_6 D Ch) (h71 : S23_7_1 D Ch)
    (h8 : S23_8 D Ch) (h2121F : S21_21For D Ch) (h2123 : S21_23 D Ch) (h67 : UC6.R6_7 D)
    (hsp : ∀ p ∈ D.sig1, CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M)
    (hsig : D.sig.Nonempty) (hK : KOrdNatural) (hS : KSchurL2) (hA : KTab23a) (hKP : KOmPlus)
    (h2 : S23_2_natural D Ch) (h3 : S23_3 D Ch) (hS3 : KSchurSL3)
    (hN1 : S23_9_NotSp4SU4O6m D Ch) (hN2 : S23_9_NotO6p D Ch) (hN3 : S23_9_NotLarge D Ch)
    (hFit : S23_22Fitting D Ch) (hHyp : S23_22Hyp2120 D Ch) : S23_22 D Ch := by
  intro h1930 c hP
  have hn3 : 3 ≤ CFSG.Open.pRank 2 D.Z := (c.n_eq_of_isOmegaPlus hE h207 h52 h1930 hP).2
  obtain ⟨hV, hPH, hNat⟩ :=
    c.exists_natOmegaPlus h2 h3 h4 hK hS hS3 hN1 hN2 hN3 h1930 hn3 hP
  exact s23_22N_of D Ch hE h207 h52 h4 h6 h71 h8 h2121F h2123 h67 hsp hsig hK hS hA hKP
    hFit hHyp h1930 c hP hV hPH hNat

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
