module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aUDefs
public import CFSG.LocalAnalysis.UniquenessCase.UC22S215KF7Use
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22S2112aR2Beta
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846c

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

@[expose] def S21_12aFR2g (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ p : ℕ, (p = 3 ∨ p = 5) → p ∈ D.sig →
    ∀ f : ℕ, f.Prime → f ≠ 2 → LieModel (BarInf L) .PSL 2 p f →
    (∀ b ∈ c.B0, CentralizesBar b L → b = 1) →
    (∃ b ∈ c.B0, ∃ hb : b ∈ normalizer (L : Set G), orderOf b = f ∧
      inducedBarInfAutHom L ⟨b, hb⟩ ∉ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) →
    F08.Thin8 L

@[expose] def S21_12aFR2d (D : Data G) (Ch : Choice2011 G) : Prop :=
  H1930 D → ∀ c : Ctx21 D Ch, ∀ L ∈ calC D.M, ∀ p : ℕ, p.Prime → p ≠ 2 → p ∉ D.sig →
    LieModel (BarInf L) .PSL 2 p 3 → (∀ b ∈ c.B0, CentralizesBar b L → b = 1) →
    (∃ b ∈ c.B0, ∃ hb : b ∈ normalizer (L : Set G), orderOf b = 3 ∧
      inducedBarInfAutHom L ⟨b, hb⟩ ∉ (MulAut.conj : BarInf L →* MulAut (BarInf L)).range) →
    F08.Thin8 L

theorem s21_12aFR2_of_rest (hGA : GriessAllModelsStatement) {D : Data G} {Ch : Choice2011 G}
    (hσ : UC6S846.SigmaStd D) (hKF7 : KF7Use D) (hg : S21_12aFR2g D Ch)
    (hd : S21_12aFR2d D Ch) : S21_12aFR2 D Ch := by
  intro hH c L hL p hp hp2 f hX hfaith ⟨b₀, hb₀B, hb₀, hθ₀⟩
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨b, hbB, hb, hbr, hbr2, hθ⟩ := uc22s2112r2_exists_prime c.hB0 hb₀B hb₀ hθ₀
  obtain ⟨hrf, hfL, -, -⟩ := uc22s2112r2_setup hGA hL hp2 hX hb hbr hbr2 rfl hθ
  by_cases hfr : 2 ≤ f / orderOf b
  · exact (uc22s2112r2_alpha hGA hσ hKF7 hH c hL hp2 hX hbB hb hbr hbr2 rfl hθ hfr).elim
  have hf1 : 1 ≤ f := hX.admissible.2.1
  have hfr1 : f / orderOf b = 1 := by
    have := Nat.div_pos (Nat.le_of_dvd hf1 hrf) hbr.pos
    omega
  have hfeq : f = orderOf b := by
    have h := Nat.div_mul_cancel hrf
    rw [hfr1, one_mul] at h
    exact h.symm
  by_cases hpσ : p ∈ D.sig
  · by_cases hp7 : 7 ≤ p
    · exact (uc22s2112r2_beta hGA hσ hKF7 hH c hL hp7 hpσ hX hbB hb hbr hbr2 rfl hθ hfr1).elim
    have hp35 : p = 3 ∨ p = 5 := by
      have h2 := hp.two_le
      rcases (by omega : p = 3 ∨ p = 4 ∨ p = 5 ∨ p = 6) with h | h | h | h
      · exact Or.inl h
      · subst h
        norm_num at hp
      · exact Or.inr h
      · subst h
        norm_num at hp
    exact hg hH c L hL p hp35 hpσ f (hfeq ▸ hbr) (hfeq ▸ hbr2) hX hfaith
      ⟨b, hbB, hb, hfeq.symm, hθ⟩
  ·
    have hfM : f ≤ Open.pRank p D.M := by
      obtain ⟨E, hEL, hEel, hEc⟩ := UC6S846.exists_elemAbelian_card_of_le_pRank hp hfL
      exact UC6S846.le_pRank' hp (hEL.trans hL.1.le) hEel hEc
    have hM3 : Open.pRank p D.M < 4 := by
      by_contra h4
      exact hpσ (hσ.four_mem p hp hp2 (by omega))
    have hr3 : 3 ≤ orderOf b := by
      have := hbr.two_le
      omega
    have hf3 : f = 3 := by omega
    subst hf3
    exact hd hH c L hL p hp hp2 hpσ hX hfaith ⟨b, hbB, hb, by omega, hθ⟩

end CFSG.LocalAnalysis.UniquenessCase.UC22
