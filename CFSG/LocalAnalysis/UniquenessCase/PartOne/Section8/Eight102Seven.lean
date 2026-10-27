module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Types
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102UniqueU
import CFSG.LocalAnalysis.RankThreeUC.ProofSupport.Y2ConjugationInvariance.Y2ConjugationInvariance
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Sylow

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet normalizer_le_of_mem_uniqueSet mem_uniqueSet_of_le)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd rhoL)
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (not_solvable_of_mem_calC sig_subset_sig1)
open CFSG.LocalAnalysis.RankThreeUC.ProofSupport.Y2ConjugationInvariance (mem_uniqueSet_map_iff)

variable {G : Type} [Group G] [Finite G]

private theorem exists_sylow_of_mem_uniqueSet_notationB {D : Data G} (hK7 : KU45TorusFix)
    {L P B : Subgroup G} {p n : ℕ} (hH : F08.Hyp8102 D L P p n) (hX : IsU45 (Bar2 L) n)
    (hN : D.M ≤ normalizer (L : Set G))
    (h3 : ∀ q : ℕ, q.Prime → q ∣ 2 ^ n + 1 → IsStronglyPEmbedded q D.M)
    (hB : F08.NotationB8103 L P n B) (hBC : centralizer (B : Set G) ≤ D.M) :
    ∃ S : Subgroup G, IsSylowOf 3 S D.M ∧ P ≤ S ∧ B ∈ uniqueSet D.M := by
  classical
  have hLM : L ≤ D.M := hH.1.1.le
  have hPM : P ≤ D.M := hH.2.2.2.2.le.trans hLM
  have hP3M : IsPGroup 3 (P.subgroupOf D.M) := hH.2.2.2.2.isPGroup.comap_subtype
  obtain ⟨S₀, hPS₀⟩ := hP3M.exists_le_sylow
  let S : Subgroup G := (S₀ : Subgroup ↥D.M).map D.M.subtype
  have hS : IsSylowOf 3 S D.M := ⟨S₀, rfl⟩
  have hPS : P ≤ S := by
    intro x hx
    exact Subgroup.mem_map.mpr
      ⟨⟨x, hPM hx⟩, hPS₀ (Subgroup.mem_subgroupOf.mpr hx), rfl⟩
  have hSN : S ≤ normalizer (L : Set G) := hS.le.trans hN
  obtain ⟨q, hq, hqn, y, hyL, hyord, hyS⟩ :=
    exists_mem_centralizer_of_torusFix (hK7 := hK7) hX hH.2.2.2.2 hS.isPGroup hSN hPS
  refine ⟨S, hS, hPS, mem_uniqueSet_of_centralizer_le (r := 3) (q := q) Nat.prime_three hS hq
    (h3 q hq hqn) (hLM hyL) hyS hyord (hB.2.1.trans hPS) hBC⟩

private theorem exists_e9_unique_of_sylow {D : Data G} (hSg : SigmaStd D) (hK2 : KU45Syl3)
    (hK5 : KU45Types) (hK7 : KU45TorusFix) {L P B S : Subgroup G} {p n : ℕ}
    (hH : F08.Hyp8102 D L P p n) (hX : IsU45 (Bar2 L) n) (hN : D.M ≤ normalizer (L : Set G))
    (hpn : p ∣ 2 ^ n + 1)
    (h3 : ∀ q : ℕ, q.Prime → q ∣ 2 ^ n + 1 → IsStronglyPEmbedded q D.M)
    (h6 : ∀ A : Subgroup G, F08.NotationA8103 L P p n A → centralizer (A : Set G) ≤ D.M)
    (hB : F08.NotationB8103 L P n B)
    (hS : IsSylowOf 3 S D.M) (hPS : P ≤ S) (hBuniq : B ∈ uniqueSet D.M) :
    ∃ E : Subgroup G, E ≤ P ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      E ≤ S ⊓ centralizer (S : Set G) ∧ E ∈ uniqueSet D.M ∧
      ∀ X : Subgroup G, X ≤ E → Nat.card X = 3 → X ∈ uniqueSet D.M := by
  classical
  have hLM : L ≤ D.M := hH.1.1.le
  have hSN : S ≤ normalizer (L : Set G) := hS.le.trans hN
  obtain ⟨q, hq, hqn, y, hyL, hyord, hyS⟩ :=
    exists_mem_centralizer_of_torusFix (hK7 := hK7) hX hH.2.2.2.2 hS.isPGroup hSN hPS
  have hmem : ∀ X : Subgroup G, X ≤ S → centralizer (X : Set G) ≤ D.M → X ∈ uniqueSet D.M :=
    fun X hXS hXC =>
      mem_uniqueSet_of_centralizer_le (r := 3) (q := q) Nat.prime_three hS hq (h3 q hq hqn)
        (hLM hyL) hyS hyord hXS hXC
  obtain ⟨E, hEP, hEel, hEcard, hEmem⟩ := exists_elemAbelian_nine hK2 hX hH.2.2.2.2
  have hES : E ≤ S := hEP.trans hPS
  have hEC : E ≤ centralizer (S : Set G) := fun x hx =>
    mem_centralizer_of_isSylowOf hK2 hX hH.2.2.2.2 hS.isPGroup hSN hPS (hEP hx) (hEel.2 x hx)
  have hBE : B ≤ E := by
    intro x hx
    refine hEmem x (hB.2.1 hx) ?_
    have h := congrArg Subtype.val (pow_card_eq_one' (G := ↥B) (x := ⟨x, hx⟩))
    simpa [hB.1] using h
  have hEuniq : E ∈ uniqueSet D.M := mem_uniqueSet_of_le hBuniq hBE (hES.trans hS.le)
  have hp : p.Prime := (prime_of_hyp8102 hSg hH).1
  have hp2 : p ≠ 2 := (prime_of_hyp8102 hSg hH).2.1
  have hXuniq : ∀ X : Subgroup G, X ≤ E → Nat.card X = 3 → X ∈ uniqueSet D.M := by
    intro X hXE hXcard
    have hXP : X ≤ P := hXE.trans hEP
    rcases notationA8103_or_notationB8103 hK5 hX hH.2.2.2.2 hp hp2 hpn hXP hXcard with hA | hB'
    · exact hmem X (hXE.trans hES) (h6 X hA)
    · obtain ⟨l, hlL, hl⟩ := exists_conj_of_notationB8103 hK5 hX hH.2.2.2.2 hp hpn hB hB'
      rw [hl]
      exact (mem_uniqueSet_map_iff (hLM hlL) B).mpr hBuniq
  exact ⟨E, hEP, hEel, hEcard, le_inf hES hEC, hEuniq, hXuniq⟩

private theorem rankThreeGamma_le_of_uniqueSet_nine {M E : Subgroup G}
    (hM : rankThreeIsMaxTwoLocal M) (hEcard : Nat.card E = 9)
    (hEuniq : E ∈ uniqueSet M)
    (hsub : ∀ X : Subgroup G, X ≤ E → Nat.card X = 3 → X ∈ uniqueSet M) :
    rankThreeGamma 1 3 E ≤ M := by
  refine (CFSG.RankThreeCoreUniqueness.Helpers.gamma_le_iff 1 3 E M).mpr ?_
  intro Q hQE hQrank
  have hQne : Q ≠ ⊥ := by
    rintro rfl
    have h0 : CFSG.Open.pRank 3 (⊥ : Subgroup G) ≤ 0 := by
      refine CFSG.SectionRank.pRank_le (p := 3) (H := ⊥) (k := 0) (by norm_num) ?_
      intro E' hE' _
      rw [le_bot_iff] at hE'
      rw [hE', Subgroup.card_bot]
      simp
    omega
  have hQdvd : Nat.card Q ∣ 9 := by
    rw [← hEcard]
    exact Subgroup.card_dvd_of_le hQE
  obtain ⟨k, hk, hQk⟩ :=
    (Nat.dvd_prime_pow (p := 3) Nat.prime_three (m := 2) (i := Nat.card Q)).1
      (by rw [show (3 : ℕ) ^ 2 = 9 by norm_num]; exact hQdvd)
  have hQcard : Nat.card Q = 3 ∨ Nat.card Q = 9 := by
    have hk0 : k ≠ 0 := by
      rintro rfl
      rw [pow_zero] at hQk
      exact hQne ((Subgroup.card_eq_one).1 hQk)
    have hk12 : k = 1 ∨ k = 2 := by omega
    rcases hk12 with hk1 | hk2
    · left; rw [hQk, hk1]; norm_num
    · right; rw [hQk, hk2]; norm_num
  rcases hQcard with hQ3 | hQ9
  · exact normalizer_le_of_mem_uniqueSet hM (hsub Q hQE hQ3)
  · rw [Subgroup.eq_of_le_of_card_ge hQE (by rw [hEcard, hQ9])]
    exact normalizer_le_of_mem_uniqueSet hM hEuniq

theorem not_centralizer_le_of_notationB8103 {D : Data G} (hSg : SigmaStd D)
    (h614 : UC6.R6_14 D) (hK2 : KU45Syl3) (hK5 : KU45Types) (hK7 : KU45TorusFix)
    {L P B : Subgroup G} {p n : ℕ} (hH : F08.Hyp8102 D L P p n) (hX : IsU45 (Bar2 L) n)
    (hN : D.M ≤ normalizer (L : Set G)) (hpn : p ∣ 2 ^ n + 1)
    (h3 : ∀ q : ℕ, q.Prime → q ∣ 2 ^ n + 1 → IsStronglyPEmbedded q D.M)
    (h6 : ∀ A : Subgroup G, F08.NotationA8103 L P p n A → centralizer (A : Set G) ≤ D.M)
    (hB : F08.NotationB8103 L P n B) : ¬ centralizer (B : Set G) ≤ D.M := by
  classical
  intro hBC
  obtain ⟨S, hS, hPS, hBuniq⟩ :=
    exists_sylow_of_mem_uniqueSet_notationB hK7 hH hX hN h3 hB hBC
  obtain ⟨E, hEP, hEel, hEcard, hEinf, hEuniq, hXuniq⟩ :=
    exists_e9_unique_of_sylow hSg hK2 hK5 hK7 hH hX hN hpn h3 h6 hB hS hPS hBuniq
  have hΓ : rankThreeGamma 1 3 E ≤ D.M :=
    rankThreeGamma_le_of_uniqueSet_nine D.maxLocal hEcard hEuniq hXuniq
  have hEcard' : Nat.card E = 3 ^ 2 := by rw [hEcard]; norm_num
  have hns : ¬ Group.IsSolvable ↥D.M := not_solvable_of_mem_calC hH.1
  exact hH.2.2.1 (h614 (sig_subset_sig1 hSg hns) 3 Nat.prime_three (by norm_num)
    (three_not_mem_sig_of_hyp8102 hSg hH) S hS E hEinf hEel hEcard' hΓ)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
