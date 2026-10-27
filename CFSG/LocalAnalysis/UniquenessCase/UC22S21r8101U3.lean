module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S21r8100Res3
import CFSG.LocalAnalysis.UniquenessCase.UC22S21rU4PC
import CFSG.LocalAnalysis.UniquenessCase.UC22P22rs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Conclusion76)
open scoped Pointwise

variable {G : Type} [Group G] [Finite G]

@[expose] def R8101U3 (D : Data G) : Prop :=
  3 < evenRank G → ∀ (L : Subgroup G) (n s r p k : ℕ), L ∈ calC D.M →
    (conjSetOf D.M L).ncard = 2 → IsL2 (Bar2 L) n → Odd s → s ∣ n → r.Prime →
    r ∣ 2 ^ s - 1 → p ∈ D.sig → 0 < k → n = 2 ^ k * p →
    (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)] →
    ∀ A : Subgroup G, A ≤ L → Nat.card A = r → A ∈ uniqueSet D.M

theorem r8101U3_of_r8100Res3 {D : Data G} (h : R8100Res3 D) : R8101U3 D := by
  intro he L n s r p k hL hc2 hL2 hs hsn hr hrs hp hk hn hcong A hAL hAr
  have hsp := h he L n s r p k hL hc2 hL2 hs hsn hr hrs hp hk hn hcong
  haveI : Fact r.Prime := ⟨hr⟩
  refine uc22p22r_mem_uniqueSet_of_sp D hr hsp (hAL.trans hL.1.le)
    (IsPGroup.of_card (n := 1) (by rw [hAr, pow_one])) ?_
  rintro rfl
  rw [Subgroup.card_bot] at hAr
  exact hr.one_lt.ne hAr

theorem u4p_false {D : Data G} {Ch : Choice2011 G}
    (h211 : S21_1 D Ch) (hSg : UC6S846.SigmaStd D)
    (hfour : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M) (h614 : UC6.R6_14 D)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    (h869 : F08.R869NS5 D) (h1930 : H1930 D) (c : Ctx21 D Ch) (hn3 : 3 ≤ c.n)
    {H₁ H₂ : Subgroup G} (hH₁ : H₁ ∈ hSet D.T D.M) (hH₂ : H₂ ∈ hSet D.T D.M)
    (hL0 : c.L0 ≤ H₁ ⊓ H₂)
    (hfX : ∀ X : Subgroup G, X ≤ D.M → D.T ≤ X → F12.InF 1 (⊤ : Subgroup (Bar2 X)) →
      (X : Set G) = ((H₁ ⊓ X : Subgroup G) : Set G) * ((H₂ ⊓ X : Subgroup G) : Set G))
    (he : 3 < evenRank G) (hU : R8101U3 D) {L : Subgroup G} (hL : L ∈ calC D.M)
    (hc2 : (conjSetOf D.M L).ncard = 2) {n p k : ℕ} (hL2 : IsL2 (Bar2 L) n)
    (hp : p ∈ D.sig) (hk : 0 < k) (hn : n = 2 ^ k * p)
    (hcong : (2 : ℤ) ^ n ≡ -1 [ZMOD (p : ℤ)]) : False := by
  obtain ⟨K, hKne, hset, hKC⟩ := uc22s21ru4e_exists_second_member hc2 hL
  have hKL : K ∈ conjSetOf D.M L := by rw [hset]; simp
  have hc2K : (conjSetOf D.M K).ncard = 2 := by rw [uc22p2214_conjSetOf_eq hKL]; exact hc2
  obtain ⟨e⟩ := u4x_bar2_equiv hKL
  obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
  have hpo : Odd p := hpp.odd_of_ne_two hp2
  have hpn : p ∣ n := by rw [hn]; exact dvd_mul_left p _
  exact U4P.false_of_uniqueSet ⟨hL, hKC, hKne, hset, hc2, hL2, hp, ⟨k, hk, hn⟩, hcong⟩ h211 hSg
    hfour h614 h76 h869 h1930 c hn3 hH₁ hH₂ hL0 hfX
    (fun r hr hrp => hU he L n p r p k hL hc2 hL2 hpo hpn hr hrp hp hk hn hcong)
    (fun r hr hrp => hU he K n p r p k hKC hc2K (CFSG.Blueprint.LieModel.of_mulEquiv e hL2) hpo
      hpn hr hrp hp hk hn hcong)

theorem s21_22U4BC_of_r8101U3
    {D : Data G} {Ch : Choice2011 G} (h211 : S21_1 D Ch) (hSg : UC6S846.SigmaStd D)
    (hfour : 3 < evenRank G → ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    (h614 : UC6.R6_14 D) (h847 : F08.R847 D) (h869 : F08.R869NS5 D) (hGL : GL3Excl.GL3Excl)
    (hn3H : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (hU : R8101U3 D) : S21_22U4BC D Ch := by
  intro h1930 c H₁ hH₁ H₂ hH₂ hL0 hfX hS1 hU3 he
  have hres : R8100Res3 D := fun _ L n _ _ p k hL hc2 hL2 _ _ _ _ hp hk hn hcong =>
    (u4p_false h211 hSg (hfour he) h614 h76 h869 h1930 c (hn3H h1930 c) hH₁ hH₂ hL0
      (fun X h1 h2 hF => hfX X h1 h2 (Or.inl hF)) he hU hL hc2 hL2 hp hk hn hcong).elim
  exact s21_22U4BC_of_r8100Res3 h211 hSg hfour h76 h614 h847 h869 hGL hn3H hres h1930 c H₁ hH₁
    H₂ hH₂ hL0 hfX hS1 hU3 he

theorem s21_22U4_of_r8101U3
    (D : Data G) (Ch : Choice2011 G) (hc : Nonempty (Ctx22b D Ch)) (h117 : R117W D)
    (h869P : F08.R869NPair D) (hV : S22_V D Ch) (hn3 : ∀ c : Ctx22b D Ch, 3 ≤ c.n)
    (h211 : S21_1 D Ch) (h8100E : R8100E D) (hSg : UC6S846.SigmaStd D)
    (hfour : 3 < evenRank G → ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (h76 : ∀ p ∈ D.sig, IsStronglyPEmbedded p D.M → Conclusion76 D.M p)
    (h614 : UC6.R6_14 D) (h847 : F08.R847 D) (h869 : F08.R869NS5 D) (hGL : GL3Excl.GL3Excl)
    (hn3H : H1930 D → ∀ c : Ctx21 D Ch, 3 ≤ c.n) (hU : R8101U3 D) : S21_22U4 D Ch :=
  s21_22U4_of_U4BC D Ch hc h117 h869P h8100E hV hn3
    (s21_22U4BC_of_r8101U3 h211 hSg hfour h76 h614 h847 h869 hGL hn3H hU)

end CFSG.LocalAnalysis.UniquenessCase.UC22
