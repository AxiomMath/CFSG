module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3LDefs
public import CFSG.LocalAnalysis.RankThreeTheoremC.GenericLayerReductionDefs
import CFSG.LocalAnalysis.UniquenessCase.UC6R869MConj
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114R3LRank
import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem uc22s2114r3l_false_of_small_sigma_rank
    {G : Type} [Group G] [Finite G] {D : Data G}
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    {L : Subgroup G} (hL : L ∈ calC D.M) (hML : D.M ≤ normalizer (L : Set G))
    {p : ℕ} (hp : p ∈ D.sig) (hpL : CFSG.Open.pRank p L ≤ 1)
    (hpM : 4 ≤ CFSG.Open.pRank p D.M)
    {r : ℕ} (hr : r.Prime) (hr2 : r ≠ 2) (hrank : 2 ≤ CFSG.Open.pRank r L)
    (hcent : ∀ E : Subgroup G, E ≤ L → IsElemAbelian r E → Nat.card E = r ^ 2 →
      CFSG.Open.pRank p (D.M ⊓ centralizer (E : Set G)) ≤ 1) : False := by
  have hpp := (D.sig_prime p hp).1
  have hp2 := (D.sig_prime p hp).2
  obtain ⟨E, hEL, hEel, hEc⟩ :=
    UC6S846.exists_elemAbelian_card_of_le_pRank (M := L) hr (k := 2) hrank
  obtain ⟨B, hBM, hBel, hBc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank
    hpp hpM
  have hLtop : L ≠ ⊤ := ne_top_of_le_ne_top (uc22p20a_M_ne_top D) hL.1.le
  have hK : CFSG.Open.IsKGroup ↥L := D.standing.kProper.isKGroup L hLtop
  have hAut := UC6.R869S.pRank_mulAut_bar2_le_two hOut hK hL.2.2 hpp hp2 hpL
  have hF := UC6.R869S.two_le_pRank_centralizer_of_pRank_mulAut hL.1.le hpp hp2 hAut
    hBM (hBM.trans hML) hBel hBc hr hr2 hEL hEel.isPGroup
  have h1 := hcent E hEL hEel hEc
  omega

@[expose] def S21_14R3LTFullSigma (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, IsChev (BarInf L) 2 →
    (∀ n : ℕ, LieRankTwoEven (BarInf L) n → IsPowTwo n) →
    ∀ f : ℕ, (LieModel (BarInf L) .PSL 4 2 f ∨ LieModel (BarInf L) .PSp 3 2 f ∨
      IsOmega8m (BarInf L) f) →
    D.k = 1 → Odd c.n → 3 ≤ c.n → c.B0 ≤ normalizer (D.T : Set G) →
    c.B0 ≤ normalizer (L : Set G) → (∀ b ∈ c.B0, CentralizesBar b L → b = 1) →
    D.M ≤ normalizer (L : Set G) →
    (∀ p ∈ D.sig, 2 ≤ CFSG.Open.pRank p L) →
    ∀ r : ℕ, r.Prime → 7 ≤ r → r ∣ 2 ^ c.n - 1 → r ∣ 2 ^ f - 1 → ¬ r ∣ f → r ∉ D.sig →
    (∀ p ∈ D.sig, ∀ E : Subgroup G, E ≤ L → IsElemAbelian r E → Nat.card E = r ^ 2 →
      CFSG.Open.pRank p (D.M ⊓ centralizer (E : Set G)) ≤ 1) →
      LieRankOneEven (BarInf L) ∨ (∃ n : ℕ, Odd n ∧ IsSp4 (Bar2 L) n) ∨ IsL3 (Bar2 L) 1


theorem s21_14R3LT_of_full_sigma
    {G : Type} [Group G] [Finite G] {D : Data G} {Ch : Choice2011 G}
    (hGA : GriessAllModelsStatement)
    (hOut : CFSG.LocalAnalysis.RankThreeTheoremC.KFactOutCyclic)
    (h4 : ∀ p ∈ D.sig, 4 ≤ CFSG.Open.pRank p D.M)
    (hFull : S21_14R3LTFullSigma D Ch) : S21_14R3LT D Ch := by
  intro hH c L hL hX hpow f hf hk hodd hn3 hBT hBL hfaith hML r hr hr7 hrn hrf hrf' hrσ hcent
  by_cases hfull : ∀ p ∈ D.sig, 2 ≤ CFSG.Open.pRank p L
  · exact hFull hH c L hL hX hpow f hf hk hodd hn3 hBT hBL hfaith hML hfull r hr hr7 hrn hrf hrf'
      hrσ hcent
  · push Not at hfull
    obtain ⟨p, hp, hpL⟩ := hfull
    exact (uc22s2114r3l_false_of_small_sigma_rank hOut hL hML hp (by omega) (h4 p hp) hr (by omega)
      (by have := uc22s2114r3l_three_le_pRank hGA hL hf hr (by omega) hrf; omega)
      (hcent p hp)).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22
