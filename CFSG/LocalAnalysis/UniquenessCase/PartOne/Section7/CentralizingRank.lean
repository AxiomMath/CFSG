module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Defs
public import CFSG.RankThree.PartOne.S12.InputsSec15
import CFSG.GroupTheory.PGroup.ElemAbelianSq
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.LocalAnalysis.StronglyEmbedded.Normalizer
public import CFSG.LocalAnalysis.SectionRank.PRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7

open Subgroup

variable {G : Type} [Group G] [Finite G]

theorem normalizer_le_of_two_le_pRank_inf_centralizer {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    {M B : Subgroup G} (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M)
    (h76 : Conclusion76 M p)
    (hBM : B ≤ M) (hB : IsPGroup r B) (hBr : 2 ≤ CFSG.Open.pRank r B)
    (hF : 2 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (B : Set G))) :
    ∀ Y : Subgroup G, Y ≤ B → Y ≠ ⊥ → Subgroup.normalizer (Y : Set G) ≤ M := by
  classical
  have hp := (Fact.out : p.Prime)
  have hr := (Fact.out : r.Prime)
  have hN : ∀ X : Subgroup G, X ≤ B → Nat.card X = r → Subgroup.normalizer (X : Set G) ≤ M := by
    intro X hXB hXcard
    obtain ⟨E, hXE, hEB, hEea, hEcard⟩ :=
      CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_le_of_card_prime hB hBr hXB hXcard
    have hEM : E ≤ M := hEB.trans hBM
    have hFE : 0 < CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (E : Set G)) := by
      have hle : M ⊓ Subgroup.centralizer (B : Set G) ≤
          M ⊓ Subgroup.centralizer (E : Set G) :=
        inf_le_inf_left _ (Subgroup.centralizer_le hEB)
      have := CFSG.SectionRank.pRank_mono hp.one_lt hle
      omega
    have hX' : ∀ X' : Subgroup G, X' ≤ E → Nat.card X' = r →
        1 < CFSG.Open.pRank p (M ⊓ Subgroup.normalizer (X' : Set G)) := by
      intro X' hX'E _
      have hle : M ⊓ Subgroup.centralizer (B : Set G) ≤
          M ⊓ Subgroup.normalizer (X' : Set G) :=
        inf_le_inf_left _ ((Subgroup.centralizer_le hEB).trans
          ((Subgroup.centralizer_le hX'E).trans (Subgroup.centralizer_le_normalizer (X' : Set G))))
      have := CFSG.SectionRank.pRank_mono hp.one_lt hle
      omega
    have hΓ : CFSG.Open.rankThreeGamma 1 r E ≤ M :=
      h76 r hr E hEM hEea hEcard hFE hX'
    have hXea : CFSG.Open.IsElemAbelian r X := CFSG.GroupTheory.isElemAbelian_of_card_prime hXcard
    have hXrank : 1 ≤ CFSG.Open.pRank r X :=
      CFSG.SectionRank.le_pRank hr.one_lt le_rfl hXea (by rw [hXcard, pow_one])
    exact (CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore (p := r) (k := 1)
      hXE hXrank).trans hΓ
  intro Y hYB hYne
  have hYr : IsPGroup r Y := hB.to_le hYB
  have hYcard : r ∣ Nat.card Y := by
    rcases hYr.card_eq_or_dvd with h1 | h1
    · exact absurd (Subgroup.eq_bot_of_card_eq Y h1) hYne
    · exact h1
  obtain ⟨x, hxord⟩ := exists_prime_orderOf_dvd_card' (G := ↥Y) r hYcard
  let X : Subgroup G := Subgroup.zpowers (x : G)
  have hXY : X ≤ Y := Subgroup.zpowers_le.mpr x.2
  have hXB : X ≤ B := hXY.trans hYB
  have hXcard : Nat.card X = r := by
    show Nat.card (Subgroup.zpowers (x : G)) = r
    rw [Nat.card_zpowers, Subgroup.orderOf_coe, hxord]
  have hNX : Subgroup.normalizer (X : Set G) ≤ M := hN X hXB hXcard
  have hC : Subgroup.centralizer (Y : Set G) ≤ M := by
    have h1 : Subgroup.centralizer (Y : Set G) ≤ Subgroup.centralizer (X : Set G) :=
      Subgroup.centralizer_le hXY
    exact h1.trans ((Subgroup.centralizer_le_normalizer (X : Set G)).trans hNX)
  have hdvd : p ∣ Nat.card (Subgroup.centralizer (Y : Set G)) := by
    have hle : M ⊓ Subgroup.centralizer (B : Set G) ≤ Subgroup.centralizer (Y : Set G) :=
      (inf_le_right : M ⊓ Subgroup.centralizer (B : Set G) ≤
        Subgroup.centralizer (B : Set G)).trans (Subgroup.centralizer_le hYB)
    have hpcard : p ∣ Nat.card (M ⊓ Subgroup.centralizer (B : Set G) : Subgroup G) :=
      CFSG.GroupTheory.dvd_card_of_one_le_pRank (Fact.out : p.Prime)
        (H := M ⊓ Subgroup.centralizer (B : Set G)) (by omega)
    exact hpcard.trans (Subgroup.card_dvd_of_le hle)
  exact hM.normalizer_le_of_centralizer_le hC hdvd

theorem rankThreeGamma_le_of_two_le_pRank_inf_centralizer {p r : ℕ} [Fact p.Prime] [Fact r.Prime]
    {M B : Subgroup G} (hM : CFSG.RankThree.PartOne.IsStronglyPEmbedded p M)
    (h76 : Conclusion76 M p)
    (hBM : B ≤ M) (hB : IsPGroup r B) (hBr : 2 ≤ CFSG.Open.pRank r B)
    (hF : 2 ≤ CFSG.Open.pRank p (M ⊓ Subgroup.centralizer (B : Set G))) :
    CFSG.Open.rankThreeGamma 1 r B ≤ M := by
  have hr := (Fact.out : r.Prime)
  refine CFSG.HardMathSupport.Solomon.Proving.GLBCore_le_of_forall (p := r) (k := 1)
    (P := B) (M := M) ?_
  intro Q hQB hQrank
  have hQne : Q ≠ ⊥ := by
    intro hQbot
    obtain ⟨E, hEQ, _, hEcard⟩ := CFSG.SectionRank.exists_pRank hr.one_lt Q
    have hEbot : E = ⊥ := le_bot_iff.mp (hQbot ▸ hEQ)
    have h1 : Nat.card E = 1 := by rw [hEbot, Subgroup.card_bot]
    rw [hEcard] at h1
    have h2 : r ≤ r ^ CFSG.Open.pRank r Q := by
      calc r = r ^ 1 := (pow_one r).symm
        _ ≤ r ^ CFSG.Open.pRank r Q := Nat.pow_le_pow_right hr.pos hQrank
    have hr2 : 2 ≤ r := hr.two_le
    omega
  exact normalizer_le_of_two_le_pRank_inf_centralizer hM h76 hBM hB hBr hF Q hQB hQne

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
