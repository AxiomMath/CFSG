module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Basic
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8.Eight102Transport
import CFSG.LocalAnalysis.UniquenessCase.UC22OddPRank
import CFSG.LocalAnalysis.UniquenessCase.UC6S846g

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8

open CFSG.Open Subgroup
open CFSG.ABGLocalTools (IsSylowOf)
open CFSG.RankThree.PartOne (IsStronglyPEmbedded)
open CFSG.LocalAnalysis.RankThreeUC (uniqueSet)
open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.UC6S846 (SigmaStd rhoL)

variable {G : Type} [Group G] [Finite G]

theorem exists_elemAbelian_nine (hK2 : KU45Syl3) {L P : Subgroup G} {n : ℕ}
    (hX : IsU45 (Bar2 L) n) (hP : IsSylowOf 3 P L) :
    ∃ E : Subgroup G, E ≤ P ∧ IsElemAbelian 3 E ∧ Nat.card E = 9 ∧
      ∀ x ∈ P, x ^ 3 = 1 → x ∈ E := by
  obtain ⟨hPbar, hPidx⟩ := isPGroup_barImage_of_isSylowOf (Nat.prime_three) hP
  obtain ⟨⟨Ebar, hEbarP, hEbarEl, hEbarCard, hEbarAll⟩, -⟩ :=
    hK2 (Bar2 L) n hX (barImage L P) hPbar hPidx
  obtain ⟨E, hEP, hbarE⟩ :=
    exists_barImage_eq hP.le Nat.prime_three (by norm_num) hP.isPGroup hEbarP
  have hEL : E ≤ L := hEP.trans hP.le
  have hE3 : IsPGroup 3 E := hP.isPGroup.to_le hEP
  refine ⟨E, hEP, ?_, ?_, ?_⟩
  · rw [← isElemAbelian_barImage_iff hEL Nat.prime_three (by norm_num) hE3, hbarE]
    exact hEbarEl
  · rw [← card_barImage_of_isPGroup hEL Nat.prime_three (by norm_num) hE3, hbarE, hEbarCard]
  · intro x hxP hx3
    have hxL : x ∈ L := hP.le hxP
    let xL : ↥L := ⟨x, hxL⟩
    have hx3bar : (QuotientGroup.mk xL : Bar2 L) ^ 3 = 1 := by
      change (uc22p21cPi L xL) ^ 3 = 1
      have hx3' : xL ^ 3 = 1 := by
        ext
        simpa using hx3
      rw [← map_pow, hx3', map_one]
    have hxbar : (QuotientGroup.mk xL : Bar2 L) ∈ barImage L E := by
      rw [hbarE]
      exact hEbarAll _ (uc22p21c_mem_barImage.2 ⟨xL, hxP, rfl⟩) hx3bar
    obtain ⟨m, hmE, hmeq⟩ := uc22p21c_mem_barImage.1 hxbar
    have hdisj : P ⊓ pCoreOf 2 L = ⊥ :=
      (IsPGroup.disjoint_of_ne 3 2 (by norm_num) P (pCoreOf 2 L) hP.isPGroup
        (UC6S846.isPGroup_pCoreOf L)).eq_bot
    have hker : m⁻¹ * xL ∈ CFSG.pCore 2 ↥L := by
      refine (QuotientGroup.eq_one_iff (m⁻¹ * xL)).1 ?_
      change uc22p21cPi L (m⁻¹ * xL) = 1
      have h2 : uc22p21cPi L m = uc22p21cPi L xL := hmeq
      rw [map_mul, map_inv, h2, inv_mul_cancel]
    have hmem : ((m⁻¹ * xL : ↥L) : G) ∈ P := by
      have hmP : (m : G) ∈ P := hEP hmE
      rw [Subgroup.coe_mul, Subgroup.coe_inv, Subgroup.coe_mk]
      exact P.mul_mem (P.inv_mem hmP) hxP
    have hbot : ((m⁻¹ * xL : ↥L) : G) ∈ (⊥ : Subgroup G) := by
      rw [← hdisj, Subgroup.mem_inf]
      exact ⟨hmem, ⟨m⁻¹ * xL, hker, rfl⟩⟩
    have hone : m⁻¹ * xL = 1 := Subtype.ext (Subgroup.mem_bot.1 hbot)
    have hxm : xL = m := by
      simpa using congrArg (fun z : ↥L => m * z) hone
    rw [show x = (m : G) from congrArg Subtype.val hxm]
    exact hmE

theorem mem_centralizer_of_isSylowOf (hK2 : KU45Syl3) {L P S : Subgroup G} {n : ℕ}
    (hX : IsU45 (Bar2 L) n) (hP : IsSylowOf 3 P L) (hS : IsPGroup 3 S)
    (hSN : S ≤ normalizer (L : Set G)) (hPS : P ≤ S) {x : G} (hxP : x ∈ P) (hx : x ^ 3 = 1) :
    x ∈ centralizer (S : Set G) := by
  obtain ⟨hPbar, hPidx⟩ := isPGroup_barImage_of_isSylowOf (Nat.prime_three) hP
  obtain ⟨-, hfixall⟩ := hK2 (Bar2 L) n hX (barImage L P) hPbar hPidx
  have hxL : x ∈ L := hP.le hxP
  have hSL : S ⊓ L = P := hP.eq_of_le (le_inf hPS hP.le) inf_le_right hS.to_inf_left
  have hfix : ∀ (s : G) (hs : s ∈ S),
      rhoL L ⟨s, hSN hs⟩ (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) =
        (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) := by
    intro s hs
    have hconjP : ∀ m : ↥L, (m : G) ∈ P →
        ((Subgroup.normalizerMonoidHom L ⟨s, hSN hs⟩ m : ↥L) : G) ∈ P := by
      intro m hmP
      rw [← hSL, Subgroup.mem_inf]
      refine ⟨?_, (Subgroup.normalizerMonoidHom L ⟨s, hSN hs⟩ m).2⟩
      rw [UC6S846.rhoL_mk_coe]
      exact S.mul_mem (S.mul_mem hs (hPS hmP)) (S.inv_mem hs)
    have hmap : ∀ y ∈ barImage L P, rhoL L ⟨s, hSN hs⟩ y ∈ barImage L P := by
      intro y hy
      obtain ⟨m, hmP, rfl⟩ := uc22p21c_mem_barImage.1 hy
      exact uc22p21c_mem_barImage.2
        ⟨Subgroup.normalizerMonoidHom L ⟨s, hSN hs⟩ m, hconjP m hmP, rfl⟩
    obtain ⟨k, hk⟩ := hS ⟨s, hs⟩
    have hs3 : s ^ (3 ^ k) = 1 := by
      simpa using congrArg Subtype.val hk
    have hpow : (⟨s, hSN hs⟩ : ↥(normalizer (L : Set G))) ^ (3 ^ k) = 1 := by
      ext
      simpa using hs3
    have hα : (rhoL L ⟨s, hSN hs⟩) ^ (3 ^ k) = 1 := by
      rw [← map_pow, hpow, map_one]
    have hxbar3 : (QuotientGroup.mk (⟨x, hxL⟩ : ↥L) : Bar2 L) ^ 3 = 1 := by
      change (uc22p21cPi L (⟨x, hxL⟩ : ↥L)) ^ 3 = 1
      rw [← map_pow]
      have hx3' : (⟨x, hxL⟩ : ↥L) ^ 3 = 1 := by
        ext
        simpa using hx
      rw [hx3', map_one]
    exact hfixall (rhoL L ⟨s, hSN hs⟩) ⟨k, hα⟩ hmap _
      (uc22p21c_mem_barImage.2 ⟨⟨x, hxL⟩, hxP, rfl⟩) hxbar3
  exact mem_centralizer_of_rhoL_fix Nat.prime_three (by norm_num) hS hSN (hPS hxP) hxL hfix

theorem le_normalizer_of_hyp8102 {D : Data G} (hSg : SigmaStd D) (hK2 : KU45Syl3)
    {L P : Subgroup G} {p n : ℕ} (hH : F08.Hyp8102 D L P p n) (hX : IsU45 (Bar2 L) n) :
    D.M ≤ normalizer (L : Set G) := by
  by_contra hN
  obtain ⟨E, hEP, hEel, hEcard, -⟩ := exists_elemAbelian_nine hK2 hX hH.2.2.2.2
  have hZ : ¬ 3 ∣ Nat.card (center (Bar2 L)) := by
    rw [center_bar2_eq_bot_of_hyp8102 hH, card_bot]
    norm_num
  have hrank := UC6S846.calCRankTwice D.M L hH.1 hN 3 Nat.prime_three (by norm_num) hZ
    E (hEP.trans hH.2.2.2.2.le) hEel 2 (by rw [hEcard]; norm_num)
  exact three_not_mem_sig_of_hyp8102 hSg hH
    (hSg.four_mem 3 Nat.prime_three (by norm_num) (by omega))

theorem even_of_hyp8102 {D : Data G} (h82 : F08.R82 D) (hK1 : KU4OddRank) {L P : Subgroup G}
    {p n : ℕ} (hH : F08.Hyp8102 D L P p n) : Even n := by
  by_contra hn
  have hnodd : Odd n := Nat.not_even_iff_odd.1 hn
  have hU4 : IsU4 (Bar2 L) n := by
    rcases hH.2.1 with ⟨-, hn2⟩ | h
    · rw [hn2] at hn
      exact absurd ⟨1, rfl⟩ hn
    · exact h
  have h3 := hK1 (Bar2 L) n hU4 hnodd
  rw [UC22.pRank_bar2_eq_of_odd (Y := L) (p := 3) Nat.prime_three (by norm_num)] at h3
  have hqs : CFSG.IsQuasisimple (Bar2 L) :=
    CFSG.Quasithin.B1Red.isQuasisimple_of_open hH.1.2.2
  exact hH.2.2.1 (h82 L ⟨hH.1.1, hH.1.2.1, by omega, Or.inl hqs⟩)

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Section8
