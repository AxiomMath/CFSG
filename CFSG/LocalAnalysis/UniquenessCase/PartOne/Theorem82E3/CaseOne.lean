module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.Context
import CFSG.LocalAnalysis.StronglyEmbedded.GammaOne
import CFSG.HardMathSupport.Solomon.Proving.GLBCoreNormalizer
import CFSG.GroupTheory.PGroup.ElemAbelianSq

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

open CFSG.Open
open CFSG.LocalAnalysis.UniquenessCase.UC22 (Data)
open scoped commutatorElement Pointwise

variable {G : Type} [Group G] [Finite G] {D : Data G}

structure Case811Sylow (c : Ctx82E3 D) where
  P : Subgroup G
  A : Subgroup G
  sylow : CFSG.ABGLocalTools.IsSylowOf 3 P D.M
  P_le_L : P ≤ c.L
  A_le : A ≤ P
  elemAbelian : CFSG.Open.IsElemAbelian 3 A
  card_A : Nat.card A = 27
  unique : ∀ B : Subgroup G, B ≤ P → CFSG.Open.IsElemAbelian 3 B → Nat.card B = 27 → B = A
  cover : ∀ x ∈ D.M, orderOf x = 3 → ∃ m ∈ D.M, m * x * m⁻¹ ∈ A

namespace Case811Sylow

theorem not_rankThreeGamma_le {c : Ctx82E3 D} (h : Case811Sylow c) :
    ¬ CFSG.Open.rankThreeGamma 1 3 h.A ≤ D.M := by
  intro hΓ
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hA1 : h.A ≠ ⊥ := by
    intro hbot
    have hcard := h.card_A
    rw [hbot, Subgroup.card_bot] at hcard
    norm_num at hcard
  refine c.not_strong
    (CFSG.RankThree.PartOne.isStronglyPEmbedded_of_rankThreeGamma_le
      (q := 3) (M := D.M) (P := h.P) (A := h.A) c.M_ne_top h.sylow h.A_le
      h.elemAbelian hA1 ?_ h.cover hΓ)
  intro B hBP hBab hBcard
  exact h.unique B hBP hBab (by rw [hBcard, h.card_A])

theorem false_of_rank_conditions {c : Ctx82E3 D} (h : Case811Sylow c) {p : ℕ}
    (hp : p ∈ D.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 D.M p)
    (hcent : ∀ E : Subgroup G, E ≤ h.A → CFSG.Open.IsElemAbelian 3 E → Nat.card E = 9 →
      0 < CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (E : Set G)))
    (hN : ∀ E X : Subgroup G, X ≤ E → E ≤ h.A → CFSG.Open.IsElemAbelian 3 E →
      Nat.card E = 9 → Nat.card X = 3 →
      1 < CFSG.Open.pRank p (D.M ⊓ Subgroup.normalizer (X : Set G)))
    (hdvd : ∀ X : Subgroup G, X ≤ h.A → Nat.card X = 3 →
      p ∣ Nat.card (Subgroup.normalizer (X : Set G))) : False := by
  classical
  haveI : Fact (Nat.Prime 3) := ⟨by norm_num⟩
  have hp_prime : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hp_prime⟩
  have hA_gamma : CFSG.Open.rankThreeGamma 1 3 h.A ≤ D.M := by
    refine CFSG.RankThree.PartOne.IsStronglyPEmbedded.rankThreeGamma_one_le
      (p := p) (q := 3) (M := D.M) (A := h.A)
      (c.isStronglyPEmbedded_of_mem_sigma hp) h.elemAbelian.isPGroup ?_
    intro X hXA hXcard
    obtain ⟨E, hXE, hEA, hEab, hEcard⟩ :=
      CFSG.GroupTheory.exists_isElemAbelian_card_sq_of_le_of_card_prime h.elemAbelian.isPGroup
        ((show 2 ≤ 3 by norm_num).trans (CFSG.SectionRank.le_pRank (by norm_num) le_rfl
          h.elemAbelian (by rw [h.card_A]; norm_num))) hXA hXcard
    have hEcard9 : Nat.card E = 9 := by rw [hEcard]; norm_num
    have hEM : E ≤ D.M := hEA.trans (h.A_le.trans (h.P_le_L.trans c.hyp81.1))
    have hΓE : CFSG.Open.rankThreeGamma 1 3 E ≤ D.M :=
      h76 3 (by norm_num) E hEM hEab (by rw [hEcard9]; norm_num)
        (hcent E hEA hEab hEcard9)
        (fun Y hYE hYcard => hN E Y hYE hEA hEab hEcard9 hYcard)
    have hNX_le_ΓE : Subgroup.normalizer (X : Set G) ≤ CFSG.Open.rankThreeGamma 1 3 E := by
      have hXab : CFSG.Open.IsElemAbelian 3 X := h.elemAbelian.mono hXA
      have h1 : 1 ≤ CFSG.Open.pRank 3 X :=
        CFSG.SectionRank.le_pRank (p := 3) (by norm_num) (le_refl X) hXab
          (by rw [hXcard]; norm_num)
      have hcore := CFSG.HardMathSupport.Solomon.Proving.normalizer_le_glbCore
        (p := 3) (k := 1) (P := E) (Q := X) hXE h1
      simpa [CFSG.Open.rankThreeGamma] using hcore
    exact ⟨hNX_le_ΓE.trans hΓE, hdvd X hXA hXcard⟩
  exact h.not_rankThreeGamma_le hA_gamma

theorem false_of_le_centralizer_A {c : Ctx82E3 D} (h : Case811Sylow c) {p : ℕ}
    (hp : p ∈ D.sig)
    (h76 : CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76 D.M p)
    {R : Subgroup G} (hRM : R ≤ D.M) (hRA : R ≤ Subgroup.centralizer (h.A : Set G))
    (hR : CFSG.Open.IsElemAbelian p R) (hRcard : Nat.card R = p ^ 2) : False := by
  have hp_prime : p.Prime := (D.sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hp_prime⟩
  refine false_of_rank_conditions h hp h76 ?_ ?_ ?_
  · intro E hEA hEab hEcard
    have hle : R ≤ D.M ⊓ Subgroup.centralizer (E : Set G) :=
      le_inf hRM (hRA.trans (Subgroup.centralizer_le (fun x hx => hEA hx)))
    have h2 : 2 ≤ CFSG.Open.pRank p (D.M ⊓ Subgroup.centralizer (E : Set G)) :=
      CFSG.SectionRank.le_pRank hp_prime.one_lt hle hR hRcard
    omega
  · intro E X hXE hEA hEab hEcard hXcard
    have hcentE : Subgroup.centralizer (h.A : Set G) ≤ Subgroup.normalizer (X : Set G) :=
      (Subgroup.centralizer_le (fun x hx => hEA (hXE hx))).trans
        (Subgroup.centralizer_le_normalizer (X : Set G))
    have hle : R ≤ D.M ⊓ Subgroup.normalizer (X : Set G) :=
      le_inf hRM (hRA.trans hcentE)
    have h2 : 2 ≤ CFSG.Open.pRank p (D.M ⊓ Subgroup.normalizer (X : Set G)) :=
      CFSG.SectionRank.le_pRank hp_prime.one_lt hle hR hRcard
    omega
  · intro X hXA hXcard
    have hle : R ≤ Subgroup.normalizer (X : Set G) :=
      hRA.trans ((Subgroup.centralizer_le (fun x hx => hXA hx)).trans
        (Subgroup.centralizer_le_normalizer (X : Set G)))
    have hdvd : p ∣ Nat.card R := by
      rw [hRcard]
      exact dvd_pow_self p (by norm_num)
    exact hdvd.trans (Subgroup.card_dvd_of_le hle)
end Case811Sylow

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
