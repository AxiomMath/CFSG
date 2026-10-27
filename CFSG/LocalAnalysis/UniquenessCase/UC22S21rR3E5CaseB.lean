module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5Third
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21rR3E5Tail

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

theorem uc22r3e5_false_of_caseB {D : Data G}
    {Ch : Choice2011 G} (st : Standing22 D) (hSg : UC6S846.SigmaStd D)
    (h13 : PartTwo.SigmaRankThree13 D) (h211 : S21_1 D Ch) (h82 : F08.R82 D)
    (h8107 : F08.R8107 D) (h847T : R847E3Thin D) (h16 : S21_16 D Ch) (h17 : S21_17 D Ch)
    (h1930 : H1930 D) (c : Ctx21 D Ch) {H₁ H₂ : Subgroup G} (hH₁ : H₁ ∈ hSet D.T D.M)
    (hH₂ : H₂ ∈ hSet D.T D.M)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X →
      (F12.InF 1 (⊤ : Subgroup (Bar2 X)) ∨ Group.IsSolvable ↥X) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    (hcent : ∀ p ∈ D.sig, CFSG.Open.pRank p (barPreimage D.M (centE D.M)) = 0)
    (he : CFSG.Open.evenRank G = 3) (hn3 : 3 ≤ c.n) (hpow : IsPowTwo c.n)
    (hSzP : ∀ Y ∈ calC D.M, (conjSetOf D.M Y).ncard = 2 → ∀ m : ℕ, 2 < m →
      IsSz (Bar2 Y) m → False)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hc2 : (conjSetOf D.M L).ncard = 2) {n : ℕ}
    (hL2 : IsL2 (Bar2 L) n) : False := by
  obtain ⟨K, hKL, hset, hK⟩ := uc22s21ru4e_exists_second_member hc2 hL
  obtain ⟨p, hp⟩ := hSg.nonempty
  have hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded p D.M :=
    UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hp
  obtain ⟨L', hL', h₁, h₂⟩ :=
    uc22r3h_exists_other_member_of_sig st h211 h1930 c hH₁ hH₂
      (fun X hX hT hInf => hfX X hX hT (Or.inl hInf)) he hL hK hKL hset
      (Or.inl hL2) hp hsp (hcent p hp)
  exact uc22r3h_false_of_third_member hSg h13 h211 h82 h8107 h847T h16 h17 h1930 c he hcent
    hn3 hpow hSzP hL hK hKL hset hL2 hL' h₁ h₂

end CFSG.LocalAnalysis.UniquenessCase.UC22
