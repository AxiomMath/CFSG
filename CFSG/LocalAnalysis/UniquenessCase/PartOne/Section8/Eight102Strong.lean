module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Transport

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd rhoL)

variable {G : Type} [Group G] [Finite G]

private theorem exists_rhoL_pow_eq_one {L Q : Subgroup G} {q : ℕ}
    (hQ : IsPGroup q Q) (hQN : Q ≤ normalizer (L : Set G)) {s : G} (hs : s ∈ Q) :
    ∃ k : ℕ, (rhoL L ⟨s, hQN hs⟩) ^ (q ^ k) = 1 := by
  obtain ⟨k, hk⟩ := hQ ⟨s, hs⟩
  refine ⟨k, ?_⟩
  have hpow : s ^ (q ^ k) = 1 := by simpa using congrArg Subtype.val hk
  have hm : (⟨s, hQN hs⟩ : ↥(normalizer (L : Set G))) ^ (q ^ k) = 1 := Subtype.ext hpow
  rw [← map_pow, hm, map_one]

private theorem rhoL_mem_barImage_inf {L Q : Subgroup G} {s : G}
    (hQN : Q ≤ normalizer (L : Set G)) (hs : s ∈ Q) :
    ∀ t ∈ barImage L (Q ⊓ L), rhoL L ⟨s, hQN hs⟩ t ∈ barImage L (Q ⊓ L) := by
  intro t ht
  obtain ⟨y, hy, rfl⟩ := (uc22p21c_mem_barImage (M := L) (P := Q ⊓ L)).1 ht
  have hyQ : (y : G) ∈ Q := hy.1
  have hmem : ((Subgroup.normalizerMonoidHom L ⟨s, hQN hs⟩ y : ↥L) : G) ∈ Q ⊓ L := by
    refine ⟨?_, (Subgroup.normalizerMonoidHom L ⟨s, hQN hs⟩ y).2⟩
    rw [UC6S846.rhoL_mk_coe]
    exact Q.mul_mem (Q.mul_mem hs hyQ) (Q.inv_mem hs)
  have h := (uc22p21c_mem_barImage (M := L) (P := Q ⊓ L)).2
    ⟨Subgroup.normalizerMonoidHom L ⟨s, hQN hs⟩ y, hmem, rfl⟩
  simpa [uc22p21cPi, QuotientGroup.mk'_apply, UC6S846.rhoL_mk] using h

private theorem exists_lift_elemAbelian {L Q : Subgroup G} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hQLsyl : IsSylowOf q (Q ⊓ L) L)
    {S : Subgroup (Bar2 L)} (hS : S ≤ barImage L (Q ⊓ L))
    (hSel : IsElemAbelian q S) (hScard : Nat.card S = q ^ 2) :
    ∃ E : Subgroup G, E ≤ Q ⊓ L ∧ barImage L E = S ∧ IsElemAbelian q E ∧
      Nat.card E = q ^ 2 := by
  obtain ⟨E, hE, hbarE⟩ := exists_barImage_eq hQLsyl.le hq hq2 hQLsyl.isPGroup hS
  have hEpg : IsPGroup q E := hQLsyl.isPGroup.to_le hE
  exact ⟨E, hE, hbarE,
    (isElemAbelian_barImage_iff (hE.trans inf_le_right) hq hq2 hEpg).1
      (hbarE.symm ▸ hSel),
    by rw [← card_barImage_of_isPGroup (hE.trans inf_le_right) hq hq2 hEpg, hbarE,
        hScard]⟩

private theorem le_centralizer_of_barImage_le {L Q E : Subgroup G} {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hQ : IsPGroup q Q)
    (hQN : Q ≤ normalizer (L : Set G))
    (hfix : ∀ α : MulAut (Bar2 L), (∃ k : ℕ, α ^ (q ^ k) = 1) →
      (∀ s ∈ barImage L (Q ⊓ L), α s ∈ barImage L (Q ⊓ L)) →
      ∀ s ∈ barImage L (Q ⊓ L), s ^ q = 1 → α s = s)
    (hE : E ≤ Q ⊓ L) (hEel : IsElemAbelian q E)
    (hES : barImage L E ≤ barImage L (Q ⊓ L)) :
    E ≤ centralizer (Q : Set G) := by
  intro e he
  have heQ : e ∈ Q := (hE he).1
  have heL : e ∈ L := (hE he).2
  refine mem_centralizer_of_rhoL_fix hq hq2 hQ hQN heQ heL ?_
  intro s hs
  have hēE : (QuotientGroup.mk ⟨e, heL⟩ : Bar2 L) ∈ barImage L E := by
    have h := (uc22p21c_mem_barImage (M := L) (P := E)).2
      ⟨⟨e, heL⟩, he, rfl⟩
    simpa [uc22p21cPi, QuotientGroup.mk'_apply] using h
  have hēS : (QuotientGroup.mk ⟨e, heL⟩ : Bar2 L) ∈ barImage L (Q ⊓ L) := hES hēE
  have hēq : (QuotientGroup.mk ⟨e, heL⟩ : Bar2 L) ^ q = 1 := by
    have heq : (⟨e, heL⟩ : ↥L) ^ q = 1 := Subtype.ext (by simpa using hEel.2 e he)
    rw [← QuotientGroup.mk_pow, heq, QuotientGroup.mk_one]
  exact hfix (rhoL L ⟨s, hQN hs⟩) (exists_rhoL_pow_eq_one hQ hQN hs)
    (rhoL_mem_barImage_inf hQN hs) _ hēS hēq

private theorem stronglyEmbedded_of_isU4 {D : Data G} (hSg : SigmaStd D)
    (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D) (hK4 : KU4SylOdd) {L P : Subgroup G} {p n : ℕ}
    (hH : F08.Hyp8102 D L P p n) (hU4 : IsU4 (Bar2 L) n) (hne : Even n)
    (hN : D.M ≤ normalizer (L : Set G)) (hpn : p ∣ 2 ^ n + 1) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqn : q ∣ 2 ^ n + 1) (hqs : q ∉ D.sig) :
    IsStronglyPEmbedded q D.M := by
  classical
  haveI : Fact q.Prime := ⟨hq⟩
  have hL : L ∈ calC D.M := hH.1
  have hLM : L ≤ D.M := hL.1.le
  have hpσ : p ∈ D.sig := hH.2.2.2.1
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hL
  obtain ⟨Q, hQsyl⟩ := CFSG.ABGLocalTools.exists_isSylowOf q D.M
  have hQLsyl : IsSylowOf q (Q ⊓ L) L := hQsyl.inf_of_le_normalizer hLM hN
  obtain ⟨hSq, hSidx⟩ := isPGroup_barImage_of_isSylowOf hq hQLsyl
  obtain ⟨⟨S, hSS, hSel, hScard, hSrank⟩, hfix⟩ :=
    hK4 (Bar2 L) n hU4 hne q p hq hp hqn hpn (barImage L (Q ⊓ L)) hSq hSidx
  obtain ⟨E, hE, hbarE, hEel, hEcard⟩ :=
    exists_lift_elemAbelian hq hq2 hQLsyl hSS hSel hScard
  have hEcent : E ≤ centralizer (Q : Set G) :=
    le_centralizer_of_barImage_le hq hq2 hQsyl.isPGroup (hQsyl.le.trans hN) hfix hE hEel
      (hbarE.symm ▸ hSS)
  have hER : E ≤ Q ⊓ centralizer (Q : Set G) :=
    le_inf (hE.trans inf_le_left) hEcent
  have hEq : IsPGroup q E := hQsyl.isPGroup.to_le (hE.trans inf_le_left)
  have hrank : 2 ≤ Open.pRank p (D.M ⊓ centralizer (E : Set G)) := by
    have h1 : 2 ≤ Open.pRank p (L ⊓ centralizer (E : Set G)) := by
      rw [← pRank_centralizer_barImage (hE.trans inf_le_right) hq hq2 hEq hp hp2,
        hbarE, top_inf_eq]
      exact hSrank
    exact h1.trans (CFSG.PreuniquenessRankFour.Helpers.pRank_mono p hp
      (inf_le_inf_right _ hLM))
  exact stronglyEmbedded_of_two_le_pRank_centralizer hSg hns h76 h614 hpσ hq hq2 hqs hQsyl hER
    hEel hEcard hrank

theorem stronglyEmbedded_of_dvd_two_pow_add_one {D : Data G} (hSg : SigmaStd D)
    (h76 : F07.R76Sig D) (h614 : UC6.R6_14 D) (hK4 : KU4SylOdd) {L P : Subgroup G} {p n : ℕ}
    (hH : F08.Hyp8102 D L P p n) (hX : IsU45 (Bar2 L) n) (hN : D.M ≤ normalizer (L : Set G))
    (hpn : p ∣ 2 ^ n + 1) {q : ℕ} (hq : q.Prime) (hqn : q ∣ 2 ^ n + 1) :
    IsStronglyPEmbedded q D.M := by
  classical
  have hns : ¬ Group.IsSolvable ↥D.M := UC6S846.not_solvable_of_mem_calC hH.1
  by_cases hqs : q ∈ D.sig
  · exact UC6S846.sp_of_mem_sig hSg hns hqs
  have hpσ : p ∈ D.sig := hH.2.2.2.1
  obtain ⟨hp, hp2⟩ := D.sig_prime p hpσ
  have hn1 : 1 ≤ n := by
    rw [Nat.one_le_iff_ne_zero]
    rintro rfl
    have hp2dvd : p ∣ 2 := by simpa using hpn
    exact hp2 ((Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 hp2dvd)
  have hq2 : q ≠ 2 := by
    rintro rfl
    have h2n : 2 ∣ 2 ^ n := by simpa only [pow_one] using pow_dvd_pow 2 hn1
    have h21 : 2 ∣ 1 := by
      rw [Nat.add_comm] at hqn
      exact (Nat.dvd_add_iff_left h2n).2 hqn
    norm_num at h21
  rcases hX with ⟨hU5, hn2⟩ | ⟨hU4, hne⟩
  · have hpn' : p ∣ 5 := by
      rw [hn2] at hpn
      norm_num at hpn
      exact hpn
    have hqn' : q ∣ 5 := by
      rw [hn2] at hqn
      norm_num at hqn
      exact hqn
    have hp5 : p = 5 := (Nat.prime_dvd_prime_iff_eq hp (by norm_num)).1 hpn'
    have hq5 : q = 5 := (Nat.prime_dvd_prime_iff_eq hq (by norm_num)).1 hqn'
    exact absurd (by rw [hq5]; exact hp5 ▸ hpσ) hqs
  · exact stronglyEmbedded_of_isU4 hSg h76 h614 hK4 hH hU4 hne hN hpn hq hq2 hqn hqs

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
