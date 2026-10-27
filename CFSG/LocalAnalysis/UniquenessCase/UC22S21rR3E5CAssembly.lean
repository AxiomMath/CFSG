module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CCore
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5CaseB
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3HF
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5R2
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3HB
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3HD

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22r3e5c_false_of_isSz
    {D : Data G} {Ch : Choice2011 G} (h5 : S21_5 D Ch) (h15 : S21_15C D Ch)
    (hSg : UC6S846.SigmaStd D) (h72 : F07.R72 D) (hK72 : KStrongEmbedded72) (hU2 : R8100U2 D)
    (h211 : S21_1 D Ch) (h869 : F08.R869NS5 D) (h1930 : H1930 D) (c : Ctx21 D Ch)
    {H₁ H₂ : Subgroup G} (hH₁ : H₁ ∈ hSet D.T D.M) (hH₂ : H₂ ∈ hSet D.T D.M)
    (hL0 : c.L0 ≤ H₁ ⊓ H₂)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    (he : CFSG.Open.evenRank G = 3) (hn3 : 3 ≤ c.n) (hpow : IsPowTwo c.n)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ}
    (hn : 2 < n) (hSz : IsSz (Bar2 L) n) : False := by
  have h3 : 3 ∣ n :=
    uc22r3h_three_dvd_of_isSz hSg h869 h15 h1930 c hn3 hpow hL hc2 hn hSz
  obtain ⟨b, hb, hbo⟩ :=
    uc22p22i_exists_elt_of_mem_piSet (uc22r3h_three_mem_piSet c hn3 hpow)
  by_cases hY : ∃ Y ∈ conjSetOf D.M L,
      ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ CFSG.Open.pCoreOf 2 D.M
  · obtain ⟨Y, hYm, hbY⟩ := hY
    exact uc22r3e_false_of_trivial_on_one hSg h869 h15 hU2 h1930 c he hL hc2 hn hSz hb hbo
      hYm hbY
  · exact uc22r3e5c_false_of_sz_core h5 h15 hSg h72 hK72 hU2 h211 h1930 c hH₁ hH₂ hL0 hfX
      he hn3 hpow hL hc2 hn hSz h3 hb hbo (fun Y hYm hbY => hY ⟨Y, hYm, hbY⟩)

theorem uc22r3e5c_s21_22R3E5R2_of_inputs
    {D : Data G} {Ch : Choice2011 G} (st : Standing22 D)
    (hSg : UC6S846.SigmaStd D) (h13 : PartTwo.SigmaRankThree13 D) (h5 : S21_5 D Ch)
    (h15 : S21_15C D Ch) (h72 : F07.R72 D) (hK72 : KStrongEmbedded72) (hU2 : R8100U2 D)
    (h211 : S21_1 D Ch) (h869 : F08.R869NS5 D) (h82 : F08.R82 D) (h8107 : F08.R8107 D)
    (h847T : R847E3Thin D) (h16 : S21_16 D Ch) (h17 : S21_17 D Ch)
    (hn3 : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) : S21_22R3E5R2 D Ch := by
  intro h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX _ hcent _ he hpow L hL hc2 n hn hS
  have hSzAll : ∀ Y ∈ calC D.M, (conjSetOf D.M Y).ncard = 2 → ∀ m : ℕ, 2 < m →
      IsSz (Bar2 Y) m → False := fun Y hY hcY m hm hSzY =>
    uc22r3e5c_false_of_isSz h5 h15 hSg h72 hK72 hU2 h211 h869 h1930 c hH₁ hH₂ hL0 hfX he
      (hn3 h1930 c) hpow hY hcY hm hSzY
  rcases hS with ⟨hSz, -, -⟩ | ⟨hL2, -, -⟩
  · exact hSzAll L hL hc2 n hn hSz
  · exact uc22r3e5_false_of_caseB st hSg h13 h211 h82 h8107 h847T h16 h17 h1930 c hH₁ hH₂ hfX
      hcent he (hn3 h1930 c) hpow hSzAll hL hc2 hL2

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
