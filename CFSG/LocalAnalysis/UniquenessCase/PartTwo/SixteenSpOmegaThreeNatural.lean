module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenC1677ThreeDefs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Shape
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Par
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3Good
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3KbarDef
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3BranchIrr
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeCases
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeCentralizerRank
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeK7Residual
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeKNeOneFamilies
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenNaturalThreeCoverParabolic
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenH154E3Engine
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenAltSixSevenNaturalR880
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3SpecialShape
import CFSG.GroupTheory.CardSupInf
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.SixteenEightS1T3IrrNat

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo

open CFSG.Quasithin CFSG.Open Subgroup CFSG.LocalAnalysis.UniquenessCase.UC22

theorem T3SpecialShape.card_mem {W : Type} [CommGroup W] {L : Subgroup (MulAut W)}
    (h : T3SpecialShape L) :
    Nat.card ↥L ∈ ({60, 168, 360, 2520, 20160, 25920} : Finset ℕ) := by
  rcases h with h | h | h | h | h | h | h
  · obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
    let : Field K := hKf
    let : Finite K := hKfin
    have hK2 : Nat.card K = 2 := by simpa using hKcard
    rw [Nat.card_congr e.toEquiv,
      CFSG.Open.StatedAPI.card_statedSL_eq_prod (K := K) (d := 3) (by norm_num), hK2]
    decide +kernel
  · obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := h
    let : Field K := hKf
    let : Finite K := hKfin
    have hK2 : Nat.card K = 2 := by simpa using hKcard
    rw [Nat.card_congr e.toEquiv,
      CFSG.Open.StatedAPI.card_statedSL_eq_prod (K := K) (d := 4) (by norm_num), hK2]
    decide +kernel
  · have hcard : Nat.card ↥L = 60 := by
      rw [s15k_six_alt_card (s16k_isAlt_five_of_isOmegaMinus_four h) (by norm_num : 2 ≤ 5)]
      norm_num [Nat.factorial]
    rw [hcard]
    decide +kernel
  · have hcard : Nat.card ↥L = 25920 := s16c167_card_isOmegaMinus_six h
    rw [hcard]
    decide +kernel
  · have hcard : Nat.card ↥L = 60 := by
      rw [s15k_six_alt_card h (by norm_num : 2 ≤ 5)]
      norm_num [Nat.factorial]
    rw [hcard]
    decide +kernel
  · have hcard : Nat.card ↥L = 360 := by
      rw [s15k_six_alt_card h (by norm_num : 2 ≤ 6)]
      norm_num [Nat.factorial]
    rw [hcard]
    decide +kernel
  · have hcard : Nat.card ↥L = 2520 := by
      rw [s15k_six_alt_card h (by norm_num : 2 ≤ 7)]
      norm_num [Nat.factorial]
    rw [hcard]
    decide +kernel

theorem ThreeNat.t3EngineBranch_of_card {W : Type} [CommGroup W] [Finite W]
    {A L T : Subgroup (MulAut W)} (h : ThreeNat A L T)
    (hcard : Nat.card ↥L ∉ ({60, 168, 360, 2520, 20160, 25920} : Finset ℕ)) :
    T3EngineBranch L ⊤ (fixV L) 3 :=
  (ThreeNat.shape_cases h).resolve_right fun hS => hcard hS.card_mem

theorem ThreeNat.exists_t3Parab_of_natShapeGood {W : Type} [CommGroup W] [Finite W]
    {A L T : Subgroup (MulAut W)} (h : ThreeNat A L T) {I : Subgroup W}
    (hTI : StableUnder T I) (hS : NatShapeGood L I (I ⊓ fixV L)) :
    ∃ a : ℕ, 2 ≤ a ∧ T3Parab L T a := by
  obtain ⟨n, hc | hc | hc | hc | hc⟩ := hS
  · obtain ⟨hL, hn, hnat⟩ := hc
    exact ⟨n / 2, by omega, ThreeNat.parab_sl h (by omega) hL hTI hnat⟩
  · obtain ⟨hL, hn, hnat⟩ := hc
    exact ⟨(n + 2) / 4, by omega, ThreeNat.parab_sp h hn hL hTI hnat⟩
  · obtain ⟨hL, hn, hnat⟩ := hc
    exact ⟨(n + 4) / 4, by omega, ThreeNat.parab_omegaPlus h hn hL hTI hnat⟩
  · obtain ⟨hL, hn, hnat⟩ := hc
    exact ⟨(n + 2) / 4, by omega, ThreeNat.parab_omegaMinus h (by omega) hL hTI hnat⟩
  · obtain ⟨hL, hn, hnat⟩ := hc
    exact ⟨(n + 1) / 4, by omega, ThreeNat.parab_alt h hn hL hTI hnat⟩

theorem cover_center_three_free_of_isSpn_six {X : Type} [Group X] (h : IsSpn X 6 1) :
    ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* X) → ¬ 3 ∣ Nat.card (Subgroup.center Q) := by
  intro Q _ _ hQ ⟨eQ⟩
  obtain ⟨-, K, hKfield, hKfinite, hKcard, ⟨eSp⟩⟩ := h
  let : Field K := hKfield
  let : Finite K := hKfinite
  let : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime (p := 2) (by
    rw [Fintype.card_eq_nat_card, hK2])
  have hSp3 : X ≃* ↥(StatedSp 3 K) := by simpa using eSp
  have : Group.IsPerfect Q := ⟨hQ.1⟩
  exact s16lc_sp_center_three_free (F := K) (m := 3) (by norm_num) (Q := Q)
    (e := eQ.trans hSp3)

theorem cover_center_three_free_of_isOmegaMinus_eight {X : Type} [Group X]
    (h : IsOmegaMinus X 8 1) :
    ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* X) → ¬ 3 ∣ Nat.card (Subgroup.center Q) := by
  intro Q _ _ hQ ⟨eQ⟩
  obtain ⟨-, K, hKfield, hKfinite, b, c₀, hKcard, hirr, ⟨eOm⟩⟩ := h
  let : Field K := hKfield
  let : Finite K := hKfinite
  let : Fintype K := Fintype.ofFinite K
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : CharP K 2 := charP_of_card_eq_prime (p := 2) (by
    rw [Fintype.card_eq_nat_card, hK2])
  have hOm4 : X ≃* StatedProj (StatedOmega (StatedQuadMinus 4 K b c₀)) := by simpa using eOm
  have : Group.IsPerfect Q := ⟨hQ.1⟩
  exact s16lc_omegaMinus_center_three_free (F := K) (m := 4) (b := b) (d := c₀)
    (by norm_num) hirr (Q := Q) (e := eQ.trans hOm4)

variable {G : Type} [Group G] [Finite G]
variable {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}

theorem s168e3_sig_eq_three_of_three_not_dvd_kBar
    (c : S168e3Ctx D V₀ V L hV)
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (h3K : ¬ 3 ∣ Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)))
    (harith : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → p ≠ 7 →
      ¬ p ^ 2 ∣ 336 * Nat.card ↥(lBar V₀ V hV L)) :
    D.sig = {3} := by
  have hK := s168e3_kBar_card_seven_of_three_not_dvd hT h7 h3K
  have h7not : 7 ∉ D.sig := s168e3_seven_not_mem_sig_of_kBar_card_seven c hT h7 hK
  have hclass : ∀ p ∈ D.sig, p = 3 := by
    intro p hp
    by_contra hp3
    exact harith p (D.sig_prime p hp).1 (D.sig_prime p hp).2 hp3
      (fun h7' => h7not (h7' ▸ hp)) (s168e3_sq_dvd_336_of_mem_sig c hT h7 hp)
  rw [Set.eq_singleton_iff_unique_mem]
  refine ⟨?_, hclass⟩
  obtain ⟨p, hp⟩ := c.std.hx.sig_nonempty
  rw [hclass p hp] at hp
  exact hp

theorem s168e3_false_of_t3Parab_of_stronglyEmbedded
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hcover : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q))
    {a : ℕ} (hP : T3Parab (lBar V₀ V hV L) (barSub V₀ V hV D.T) a) (ha : 2 ≤ a)
    (hcase : V₀ ≠ ⊥ ∨ 3 ≤ a ∨
      ∃ v ∈ V, (∀ t ∈ D.T, t * v = v * t) ∧ Subgroup.centralizer ({v} : Set G) ≤ D.M) :
    False := by
  obtain ⟨Y, hYM, hY3, hYcard, hYexp, hYnc, hperm⟩ :=
    s168e3_exists_permuting_of_parabolic_three_free c hcomp hT hsimple hcover hP ha
  exact false_of_permuting_three_of_stronglyEmbedded D c.std.hx c.std.h61 c.std.h63 c.std.h126
    c.std.h1211 c.std.h111 c.std.h6161ii hsp c.setting
    (mBarGT_two_of_threeNat c.setting hT) hYM hY3 hYexp hYnc hperm (by
      rcases hcase with hV₀ | ha3 | hv
      · exact Or.inl hV₀
      · refine Or.inr (Or.inl ?_)
        rw [hYcard]
        calc 9 = 3 ^ 2 := by norm_num
          _ < 3 ^ 3 := by norm_num
          _ ≤ 3 ^ a := Nat.pow_le_pow_right (by norm_num) ha3
      · exact Or.inr (Or.inr hv))

theorem s168e3_false_of_t3Parab
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h3 : 3 ∈ D.sig)
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hcover : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q))
    {a : ℕ} (hP : T3Parab (lBar V₀ V hV L) (barSub V₀ V hV D.T) a) (ha : 2 ≤ a)
    (hcase : V₀ ≠ ⊥ ∨ 3 ≤ a ∨
      ∃ v ∈ V, (∀ t ∈ D.T, t * v = v * t) ∧ Subgroup.centralizer ({v} : Set G) ≤ D.M) :
    False := by
  exact s168e3_false_of_t3Parab_of_stronglyEmbedded c hcomp hT
    (c.std.hSg.sig1_sp 3 (c.std.h1219 V₀ V c.setting.hyp16.hyp125 ▸ h3))
    hsimple hcover hP ha hcase

theorem s168e3_false_of_t3EngineBranch_of_stronglyEmbedded
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (hsp : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M)
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hcover : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q))
    (hE : T3EngineBranch (lBar V₀ V hV L) ⊤ (fixV (lBar V₀ V hV L)) 3) :
    False := by
  obtain ⟨I, hI, hTI, -⟩ := hT.exists_stable_natural
  have hS := hT.natShapeGood_of_mem_irrSet hE hI
  obtain ⟨a, ha, hP⟩ := hT.exists_t3Parab_of_natShapeGood hTI hS
  refine s168e3_false_of_t3Parab_of_stronglyEmbedded c hcomp hT hsp hsimple hcover hP ha ?_
  by_cases hV₀ : V₀ = ⊥
  · obtain ⟨v, hvV, -, hvT, hvC⟩ :=
      c.setting.exists_good_vector_of_stronglyEmbedded c.std.h61 c.std.h63 hT.quasi hsp hV₀ hTI hS
    exact Or.inr (Or.inr ⟨v, hvV, hvT, hvC⟩)
  · exact Or.inl hV₀

theorem s168e3_false_of_t3EngineBranch
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L) (barSub V₀ V hV D.T))
    (h3 : 3 ∈ D.sig)
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hcover : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q))
    (hE : T3EngineBranch (lBar V₀ V hV L) ⊤ (fixV (lBar V₀ V hV L)) 3) :
    False := by
  exact s168e3_false_of_t3EngineBranch_of_stronglyEmbedded c hcomp hT
    (c.std.hSg.sig1_sp 3 (c.std.h1219 V₀ V c.setting.hyp16.hyp125 ▸ h3))
    hsimple hcover hE

theorem s168e3_false_of_sum_three_of_three_not_dvd_kBar
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom)
    (hs : s15 D.M V₀ V hV L = 1)
    (hsimple : IsSimpleGroup ↥(lBar V₀ V hV L))
    (hcover : ∀ (Q : Type) [Group Q] [Finite Q], CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* ↥(lBar V₀ V hV L)) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q))
    (h3K : ¬ 3 ∣ Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)))
    (harith : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → p ≠ 7 →
      ¬ p ^ 2 ∣ 336 * Nat.card ↥(lBar V₀ V hV L))
    (hcard : Nat.card ↥(lBar V₀ V hV L) ∉ ({60, 168, 360, 2520, 20160, 25920} : Finset ℕ)) :
    False := by
  have hT := s168e3_threeNat_of_s15_eq_one c hcomp hsum htrans hs
  have h7 := s168e3_irrSet_seven_of_sum_three c hcomp hsum htrans hs
  have h3 : 3 ∈ D.sig := by
    rw [s168e3_sig_eq_three_of_three_not_dvd_kBar c hT h7 h3K harith]
    exact Set.mem_singleton 3
  exact s168e3_false_of_t3EngineBranch c hcomp hT h3 hsimple hcover
    (hT.t3EngineBranch_of_card hcard)

private theorem s168e3_spom3_prime_dvd_2357 {p a b : ℕ} (hp : p.Prime)
    (h : p ∣ 2 ^ a * 3 ^ b * 5 * 7 ^ 2) : p = 2 ∨ p = 3 ∨ p = 5 ∨ p = 7 := by
  rcases (Nat.Prime.dvd_mul hp).1 h with h | h
  · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
    · rcases (Nat.Prime.dvd_mul hp).1 h with h | h
      · left
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).1 (hp.dvd_of_dvd_pow h)
      · right; left
        exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).1 (hp.dvd_of_dvd_pow h)
    · right; right; left
      exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_five).1 h
  · right; right; right
    exact (Nat.prime_dvd_prime_iff_eq hp Nat.prime_seven).1 (hp.dvd_of_dvd_pow h)

private theorem s168e3_spom3_not_sq_dvd_sp_six {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hp7 : p ≠ 7) : ¬ p ^ 2 ∣ 336 * 1451520 := by
  intro h
  have hN : p ^ 2 ∣ 2 ^ 13 * 3 ^ 5 * 5 * 7 ^ 2 := by
    rw [show 336 * 1451520 = 2 ^ 13 * 3 ^ 5 * 5 * 7 ^ 2 by norm_num] at h
    exact h
  have hpN : p ∣ 2 ^ 13 * 3 ^ 5 * 5 * 7 ^ 2 :=
    (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hN
  rcases s168e3_spom3_prime_dvd_2357 hp hpN with rfl | rfl | rfl | rfl
  · exact hp2 rfl
  · exact hp3 rfl
  · norm_num at hN
  · exact hp7 rfl

private theorem s168e3_spom3_not_sq_dvd_om_eight {p : ℕ} (hp : p.Prime) (hp2 : p ≠ 2)
    (hp3 : p ≠ 3) (hp7 : p ≠ 7) : ¬ p ^ 2 ∣ 336 * 197406720 := by
  intro h
  have hN : p ^ 2 ∣ 2 ^ 16 * 3 ^ 5 * 5 * 7 ^ 2 * 17 := by
    rw [show 336 * 197406720 = 2 ^ 16 * 3 ^ 5 * 5 * 7 ^ 2 * 17 by norm_num] at h
    exact h
  have hpN : p ∣ 2 ^ 16 * 3 ^ 5 * 5 * 7 ^ 2 * 17 :=
    (dvd_pow_self p (by norm_num : 2 ≠ 0)).trans hN
  rcases (Nat.Prime.dvd_mul hp).1 hpN with hpN | hpN
  · rcases s168e3_spom3_prime_dvd_2357 hp hpN with rfl | rfl | rfl | rfl
    · exact hp2 rfl
    · exact hp3 rfl
    · norm_num at hN
    · exact hp7 rfl
  · have h17 : p = 17 :=
      (Nat.prime_dvd_prime_iff_eq hp (by norm_num : Nat.Prime 17)).1 hpN
    subst h17
    norm_num at hN

theorem s168e3_false_of_sum_three_sp_six
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom)
    (hs : s15 D.M V₀ V hV L = 1)
    (hSp : IsSpn ↥(lBar V₀ V hV L) 6 1) :
    False := by
  have hcard : Nat.card ↥(lBar V₀ V hV L) = 1451520 := s16c1610_card_of_isSpn_six hSp
  refine s168e3_false_of_sum_three_of_three_not_dvd_kBar c hcomp hsum htrans hs
    (s16c167_cfg2_simple_sp hSp) (cover_center_three_free_of_isSpn_six hSp)
    (s168e3_three_not_dvd_kBar_of_sp_six c hcomp hSp) (fun p hp hp2 hp3 hp7 => ?_)
    (by rw [hcard]; decide +kernel)
  rw [hcard]
  exact s168e3_spom3_not_sq_dvd_sp_six hp hp2 hp3 hp7

theorem s168e3_false_of_sum_three_omega_minus_eight
    {G : Type} [Group G] [Finite G]
    {D : Data G} {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom)
    (hs : s15 D.M V₀ V hV L = 1)
    (hOm : IsOmegaMinus ↥(lBar V₀ V hV L) 8 1) :
    False := by
  have hcard : Nat.card ↥(lBar V₀ V hV L) = 197406720 :=
    s16c1610_card_of_isOmegaMinus_eight hOm
  refine s168e3_false_of_sum_three_of_three_not_dvd_kBar c hcomp hsum htrans hs
    (s16c167_cfg2_simple_omegaMinus_eight hOm) (cover_center_three_free_of_isOmegaMinus_eight hOm)
    (s168e3_three_not_dvd_kBar_of_omega_minus_eight c hcomp hOm) (fun p hp hp2 hp3 hp7 => ?_)
    (by rw [hcard]; decide +kernel)
  rw [hcard]
  exact s168e3_spom3_not_sq_dvd_om_eight hp hp2 hp3 hp7

theorem s168e3_sl_four_cover
    {X : Type} [Group X] (h : IsSLn X 4 1) :
    ∀ (Q : Type) [Group Q] [Finite Q],
      CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃* X) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q) :=
  cover_center_three_free_of_isSLn_three_or_four h (Or.inr rfl)

theorem s168e3_natShapeGood_or_sl_four {W : Type} [CommGroup W] [Finite W]
    {L : Subgroup (MulAut W)} {I Z : Subgroup W}
    (hq : CFSG.Open.IsQuasisimple ↥L) (hcardL : Nat.card ↥L = 20160)
    (hInat : SumOfNatShape L I Z 1) :
    NatShapeGood L I Z ∨
      (IsSLn ↥L 4 1 ∧ SumOfNat (fun H U Z => BinaryNaturalSL H U Z 4 1) L I Z 1) := by
  obtain ⟨n, hSL | hSp | hOp | hOm | hAlt⟩ := hInat
  · obtain ⟨hSLn, hsum⟩ := hSL
    have hn3 := s16k_three_le_of_isSLn hq hSLn
    by_cases hn4 : 4 ≤ n
    · by_cases hn5 : 5 ≤ n
      · exact Or.inl ⟨n, Or.inl ⟨hSLn, hn5, hsum⟩⟩
      · have hn : n = 4 := by omega
        subst hn
        exact Or.inr ⟨hSLn, hsum⟩
    · have hn : n = 3 := by omega
      subst hn
      obtain ⟨K, hKf, hKfin, hKcard, ⟨e⟩⟩ := hSLn
      let : Field K := hKf
      let : Finite K := hKfin
      have hK2 : Nat.card K = 2 := by simpa using hKcard
      have hc : Nat.card ↥L = 168 := by
        rw [Nat.card_congr e.toEquiv]
        rw [CFSG.Open.StatedAPI.card_statedSL_three, hK2]
        norm_num
      rw [hcardL] at hc
      norm_num at hc
  · obtain ⟨hSpn, hsum⟩ := hSp
    have hn6 := s16k_six_le_of_isSpn hq hSpn
    exact Or.inl ⟨n, Or.inr (Or.inl ⟨hSpn, hn6, hsum⟩)⟩
  · obtain ⟨hOpn, hsum⟩ := hOp
    have hn6 := s16k_six_le_of_isOmegaPlus hq hOpn
    exact Or.inl ⟨n, Or.inr (Or.inr (Or.inl ⟨hOpn, hn6, hsum⟩))⟩
  · obtain ⟨hOmn, hsum⟩ := hOm
    have hn4 := s16k_four_le_of_isOmegaMinus hq hOmn
    obtain ⟨r, hr⟩ := hOmn.1
    by_cases hn8 : 8 ≤ n
    · exact Or.inl ⟨n, Or.inr (Or.inr (Or.inr (Or.inl ⟨hOmn, hn8, hsum⟩)))⟩
    · have hn : n = 4 ∨ n = 6 := by omega
      rcases hn with rfl | rfl
      · have hc : Nat.card ↥L = 60 := by
          rw [s15k_six_alt_card (s16k_isAlt_five_of_isOmegaMinus_four hOmn) (by norm_num : 2 ≤ 5)]
          norm_num [Nat.factorial]
        rw [hcardL] at hc
        norm_num at hc
      · have hc : Nat.card ↥L = 25920 := s16c167_card_isOmegaMinus_six hOmn
        rw [hcardL] at hc
        norm_num at hc
  · obtain ⟨hAltn, hsum⟩ := hAlt
    have hn5 := s16k_five_le_of_isAlt hq hAltn
    by_cases hn8 : 8 ≤ n
    · exact Or.inl ⟨n, Or.inr (Or.inr (Or.inr (Or.inr ⟨hAltn, hn8, hsum⟩)))⟩
    · have hn : n = 5 ∨ n = 6 ∨ n = 7 := by omega
      rcases hn with rfl | rfl | rfl
      · have hc : Nat.card ↥L = 60 := by
          rw [s15k_six_alt_card hAltn (by norm_num : 2 ≤ 5)]
          norm_num [Nat.factorial]
        rw [hcardL] at hc
        norm_num at hc
      · have hc : Nat.card ↥L = 360 := by
          rw [s15k_six_alt_card hAltn (by norm_num : 2 ≤ 6)]
          norm_num [Nat.factorial]
        rw [hcardL] at hc
        norm_num at hc
      · have hc : Nat.card ↥L = 2520 := by
          rw [s15k_six_alt_card hAltn (by norm_num : 2 ≤ 7)]
          norm_num [Nat.factorial]
        rw [hcardL] at hc
        norm_num at hc

theorem s168e3_false_of_kBar_seven_sl_four
    {G : Type} [Group G] [Finite G] {D : Data G}
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hSL : IsSLn ↥(lBar V₀ V hV L) 4 1)
    (hk7 : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 7) :
    False := by
  classical
  have h3K : ¬ 3 ∣ Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) := by
    rw [hk7]; norm_num
  have hSLcopy := hSL
  obtain ⟨K, hKf, hKfin, hKcard, ⟨eL⟩⟩ := hSL
  let : Field K := hKf
  let : Finite K := hKfin
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  have hcardL : Nat.card ↥(lBar V₀ V hV L) = 20160 := by
    rw [Nat.card_congr eL.toEquiv,
      CFSG.Open.StatedAPI.card_statedSL_four_of_card_eq_two hK2]
  have harith : ∀ p : ℕ, p.Prime → p ≠ 2 → p ≠ 3 → p ≠ 7 →
      ¬ p ^ 2 ∣ 336 * Nat.card ↥(lBar V₀ V hV L) := by
    intro p hp hp2 hp3 hp7 hsq
    have hbound : 336 * Nat.card ↥(lBar V₀ V hV L) ∣ 935911159612047360 := by
      rw [hcardL]; norm_num
    rcases s168e3_prime_eq_three_or_seven_of_sq_dvd_336_mul hp hp2 hsq hbound with h | h
    · exact hp3 h
    · exact hp7 h
  have hsig := s168e3_sig_eq_three_of_three_not_dvd_kBar c hT h7 h3K harith
  have h3 : 3 ∈ D.sig := by rw [hsig]; exact Set.mem_singleton 3
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    s16c167_cfg2_simple_ln (s16k_isLn_of_isSLn (by norm_num) hSLcopy)
  have hcover := s168e3_sl_four_cover hSLcopy
  obtain ⟨I, hI, hTI, hInat⟩ := hT.exists_stable_natural
  rcases s168e3_natShapeGood_or_sl_four hT.quasi hcardL hInat with hgood | ⟨hSL4, hsum4⟩
  · obtain ⟨a, ha, hP⟩ := hT.exists_t3Parab_of_natShapeGood hTI hgood
    refine s168e3_false_of_t3Parab c hcomp hT h3 hsimple hcover hP ha ?_
    by_cases hV0 : V₀ = ⊥
    · obtain ⟨v, hvV, hvne, hvT, hvC⟩ :=
        c.setting.exists_good_vector c.std.h61 hT.quasi h3 hV0 hTI hgood
      exact Or.inr (Or.inr ⟨v, hvV, hvT, hvC⟩)
    · exact Or.inl hV0
  · have hnat4 : BinaryNaturalSL (lBar V₀ V hV L) I (I ⊓ fixV (lBar V₀ V hV L)) 4 1 :=
      s16t3_sumOfNat_one hsum4
    have hP2 : T3Parab (lBar V₀ V hV L) (barSub V₀ V hV D.T) 2 := by
      simpa using hT.parab_sl (n := 4) (by norm_num) hSL4 hTI hsum4
    refine s168e3_false_of_t3Parab c hcomp hT h3 hsimple hcover hP2 (by norm_num) ?_
    by_cases hV0 : V₀ = ⊥
    · have hpker : 3 ∣ Nat.card (F11.CTilde D.M V₀ V) := by
        by_contra hnd
        have hle := pRank_le_pRank_mbar_of_not_dvd hV
          c.setting.hyp16.hyp125.pairFacts Nat.prime_three hnd
        have hM3 : CFSG.Open.pRank 3 D.M = 3 := c.std.pRank_eq_three h3
        have hbar2 : CFSG.Open.pRank 3 (Mbar D.M V₀ V hV) ≤ 2 :=
          hT.pRank_three_le_two h7 (Or.inr ⟨Or.inl hSL4, hk7⟩)
        rw [hM3] at hle
        omega
      obtain ⟨w, hwI, hwne, hwT⟩ :=
        exists_fixed_of_stable_subgroup hTI hInat hT.quasi
          (fun w => by rw [pow_two]; exact hT.elem w) hT.sylow.isPGroup
      obtain ⟨P, hPL, hPperf, hPcard, hPfix⟩ :=
        s16t3_perfect_stabilizer_of_binaryNaturalSL_four hnat4 inf_le_right hwI
      obtain ⟨x, hxmk, hx0, hxT, hP₀⟩ :=
        s16g_fix_good_vector_witness c.setting hV0 hwne hwT
          (hPL.trans (by simpa [lBar, Mbar] using barSub_mono V₀ V hV c.setting.hyp151.le))
          hPfix
      have h4 : Nat.card V₀ ≤ 4 := by rw [hV0, Subgroup.card_bot]; norm_num
      obtain ⟨X, hXle, hXp, hXc⟩ :=
        exists_noncyclic_cent_of_perfect_bar D Nat.prime_three (by norm_num) hV
          c.setting.hyp16.hyp125.pairFacts (Or.inl hV0) h4 x hx0 hP₀ hPperf hPcard hpker
      have hx1' : x.val ≠ 1 := by
        intro h1
        exact hx0 (by rw [hV0]; exact Subgroup.mem_bot.2 h1)
      have hx2 : ∃ n : ℕ, x.val ^ (2 ^ n) = 1 :=
        ⟨1, by simpa using hV.2 x.val x.val_mem⟩
      have hcent := centralizer_le_of_noncyclic D c.std.h61 h3
        (hXle.trans inf_le_left) hXp hXc hx1' hx2 (hXle.trans inf_le_right)
      exact Or.inr (Or.inr ⟨x.val, x.val_mem, hxT, hcent⟩)
    · exact Or.inl hV0

theorem s168e3_false_of_kBar_21_sl_four_of_r880
    {G : Type} [Group G] [Finite G] {D : Data G}
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h880 : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R880 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hSL : IsSLn ↥(lBar V₀ V hV L) 4 1)
    (hk21 : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 21) :
    False := by
  have hLn4 : IsLn ↥(lBar V₀ V hV L) 4 1 := s16k_isLn_of_isSLn (by norm_num) hSL
  have hstrong : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    isStronglyPEmbedded_three_of_r880 c.setting.hyp16.hyp125 c.std.h127 c.std.h119 h880 hcomp
      (Or.inr (Or.inr (Or.inl hLn4)))
  have hop3 : UC22.F10.OpRes 3 D.M = D.M :=
    c.std.h638 3 Nat.prime_three (by norm_num) (Or.inr hstrong)
  exact c.setting.false_of_kBar_order_21_of_opRes hop3 hT h7 hk21

theorem s168e3_false_of_kBar_168_sl_four_of_r880
    {G : Type} [Group G] [Finite G] {D : Data G}
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h880 : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R880 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hT : ThreeNat (Mbar D.M V₀ V hV) (lBar V₀ V hV L)
      (barSub V₀ V hV D.T))
    (h7 : Nat.card ↥(irrSet (lBar V₀ V hV L)) = 7)
    (hSL : IsSLn ↥(lBar V₀ V hV L) 4 1)
    (hk168 : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 168) :
    False := by
  classical
  have hSLcopy := hSL
  obtain ⟨K, hKf, hKfin, hKcard, ⟨eL⟩⟩ := hSL
  let : Field K := hKf
  let : Finite K := hKfin
  have hK2 : Nat.card K = 2 := by simpa using hKcard
  have hcardL : Nat.card ↥(lBar V₀ V hV L) = 20160 := by
    rw [Nat.card_congr eL.toEquiv,
      CFSG.Open.StatedAPI.card_statedSL_four_of_card_eq_two hK2]
  have hsimple : IsSimpleGroup ↥(lBar V₀ V hV L) :=
    s16c167_cfg2_simple_ln (s16k_isLn_of_isSLn (by norm_num) hSLcopy)
  have hcoverL := s168e3_sl_four_cover hSLcopy
  obtain ⟨N, hNA, hLN, -, hcommNK, hNKbot, hNKsup, hKord⟩ := hT.structure_of_seven h7
  obtain ⟨-, hKsimple⟩ : Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = 168 ∧
      IsSimpleGroup ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) := by
    rcases hKord with h | h | h
    · rw [h] at hk168; norm_num at hk168
    · rw [h] at hk168; norm_num at hk168
    · exact h
  have hKA : s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) ≤ Mbar D.M V₀ V hV :=
    inf_le_left
  have hKnorm : ((s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)).subgroupOf
      (Mbar D.M V₀ V hV)).Normal :=
    s16t3_special_kBar_normal hT
  have hnormK : Mbar D.M V₀ V hV ≤ Subgroup.normalizer
      ((s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) :
        Set (MulAut (Vtil V₀ V hV))) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hKA).1 hKnorm
  have hKnc : ¬ IsMulCommutative ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) := by
    intro hc
    have : IsMulCommutative ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) := hc
    have hp : (Nat.card ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L))).Prime :=
      (Group.is_simple_iff_prime_card).1 hKsimple
    rw [hk168] at hp
    norm_num at hp
  have hKQ : CFSG.Open.IsQuasisimple
      ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) := by
    have hperf : Group.IsPerfect
        ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) :=
      TauCeti.IsSimpleGroup.isPerfect_of_not_isMulCommutative hKnc
    have hZ : Subgroup.center
        ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) = ⊥ :=
      TauCeti.IsSimpleGroup.center_eq_bot_of_not_isMulCommutative hKnc
    let e : (↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) ⧸
        Subgroup.center ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L))) ≃*
        ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) :=
      (QuotientGroup.quotientMulEquivOfEq hZ).trans QuotientGroup.quotientBot
    exact ⟨hperf.commutator_eq_top,
      (MulEquiv.isSimpleGroup_congr e).mpr hKsimple⟩
  have hcompK : IsComponentOf (s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L))
      (Mbar D.M V₀ V hV) :=
    ⟨hKA, IsSubnormal.step hKA hKnorm (IsSubnormal.refl _), hKQ⟩
  have hcoverK : ∀ (Q : Type) [Group Q] [Finite Q],
      CFSG.Open.IsQuasisimple Q →
      Nonempty ((Q ⧸ Subgroup.center Q) ≃*
        ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L))) →
      ¬ 3 ∣ Nat.card (Subgroup.center Q) := by
    intro Q _ _ hQ ⟨eQ⟩
    have hGL : CFSG.StandardType.GGCenterPrime 3 (GL (Fin 3) (ZMod 2)) := ggCenterPrime_gl_three_zmod_two
    obtain ⟨eK⟩ := s16t3_kBar_mulEquiv_gl3 hT h7 hk168
    have hcpK : CFSG.StandardType.GGCenterPrime 3
        ↥(s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L)) :=
      CFSG.StandardType.ggCenterPrime_of_mulEquiv eK hGL
    have : Group.IsPerfect Q := ⟨hQ.1⟩
    exact s16lc_center_three_free_of_ggCenterPrime hcpK eQ
  obtain ⟨YL, -, hYLM, hYLN, hYLbar, hYL3⟩ :=
    s168e3_exists_normal_cover_three_free c hcomp hsimple hT.normal hcoverL
  obtain ⟨YK, -, hYKM, hYKN, hYKbar, hYK3⟩ :=
    s168e3_exists_normal_cover_prime_free (B := s1t3KBar (Mbar D.M V₀ V hV)
      (lBar V₀ V hV L)) c hcompK hKsimple hnormK Nat.prime_three (by norm_num) hcoverK
  have hLK : lBar V₀ V hV L ⊓
      s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) = ⊥ := by
    refine le_bot_iff.1 fun x hx => ?_
    have hxN : x ∈ N := hLN hx.1
    have hxNK : x ∈ N ⊓ s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) :=
      ⟨hxN, hx.2⟩
    rw [hNKbot] at hxNK
    simpa using hxNK
  have hCnorm : ((YL ⊔ YK).subgroupOf D.M).Normal := by
    have : (YL.subgroupOf D.M).Normal := hYLN
    have : (YK.subgroupOf D.M).Normal := hYKN
    rw [Subgroup.subgroupOf_sup hYLM hYKM]
    infer_instance
  have hC3 : ¬ 3 ∣ Nat.card ↥((YL ⊔ YK) ⊓ F11.CTilde D.M V₀ V) := by
    rw [sup_inf_cTilde_eq_of_disjoint_barSub c.m_le_stabTil hYLM hYKM hYKN hYLbar hYKbar hLK]
    have hCTN : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal :=
      s15_Three_cTilde_normal hV c.m_le_stabTil
    have hYKCTN : ((YK ⊓ F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := by
      have : (YK.subgroupOf D.M).Normal := hYKN
      have : ((F11.CTilde D.M V₀ V).subgroupOf D.M).Normal := hCTN
      have h : (YK ⊓ F11.CTilde D.M V₀ V).subgroupOf D.M =
          YK.subgroupOf D.M ⊓ (F11.CTilde D.M V₀ V).subgroupOf D.M :=
        Subgroup.comap_inf YK (F11.CTilde D.M V₀ V) D.M.subtype
      rw [h]
      infer_instance
    have hle : YL ⊓ F11.CTilde D.M V₀ V ≤
        Subgroup.normalizer ((YK ⊓ F11.CTilde D.M V₀ V) : Set G) :=
      (inf_le_left.trans hYLM).trans
        ((Subgroup.normal_subgroupOf_iff_le_normalizer
          (inf_le_left.trans hYKM)).1 hYKCTN)
    exact CFSG.GroupTheory.not_dvd_card_sup_of_not_dvd Nat.prime_three hle hYL3 hYK3
  obtain ⟨I, hI, hTI, hInat⟩ := hT.exists_stable_natural
  have hparab : ∃ a : ℕ, 2 ≤ a ∧ T3Parab (lBar V₀ V hV L) (barSub V₀ V hV D.T) a := by
    rcases s168e3_natShapeGood_or_sl_four hT.quasi hcardL hInat with hgood | ⟨hSL4, hsum4⟩
    · obtain ⟨a, ha, hP⟩ := hT.exists_t3Parab_of_natShapeGood hTI hgood
      exact ⟨a, ha, hP⟩
    · refine ⟨2, by norm_num, ?_⟩
      simpa using hT.parab_sl (n := 4) (by norm_num) hSL4 hTI hsum4
  obtain ⟨a, ha, hP⟩ := hparab
  obtain ⟨J, hTJ, hJL, hJcard, hJexp⟩ :=
    T3ParabK.of_kBar hT h7 hk168 hP
  have hbarsup : barSub V₀ V hV (YL ⊔ YK) =
      lBar V₀ V hV L ⊔ s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) := by
    have hYLS : YL ≤ stabTil V₀ V := hYLM.trans c.m_le_stabTil
    have hYKS : YK ≤ stabTil V₀ V := hYKM.trans c.m_le_stabTil
    unfold barSub
    rw [Subgroup.subgroupOf_sup hYLS hYKS, Subgroup.map_sup]
    have hYLbar' : (YL.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV) =
        lBar V₀ V hV L := hYLbar
    have hYKbar' : (YK.subgroupOf (stabTil V₀ V)).map (actTil V₀ V hV) =
        s1t3KBar (Mbar D.M V₀ V hV) (lBar V₀ V hV L) := hYKbar
    rw [hYLbar', hYKbar']
  have hJL' : J ≤ barSub V₀ V hV (YL ⊔ YK) ⊔ barSub V₀ V hV D.T := by
    rw [hbarsup]
    exact hJL
  obtain ⟨Y, hYM, hY3, hYcard, hYexp, hYnc, hperm⟩ :=
    s168e3_exists_permuting_of_normal_subgroup_three_free c (sup_le hYLM hYKM)
      hCnorm hC3 hTJ hJL' hJcard (by omega) hJexp
  have hLn4 : IsLn ↥(lBar V₀ V hV L) 4 1 := s16k_isLn_of_isSLn (by norm_num) hSLcopy
  have hstrong : CFSG.RankThree.PartOne.IsStronglyPEmbedded 3 D.M :=
    isStronglyPEmbedded_three_of_r880 c.setting.hyp16.hyp125 c.std.h127 c.std.h119 h880 hcomp
      (Or.inr (Or.inr (Or.inl hLn4)))
  have hk1 : D.k = 1 := Data.k_eq_one_of_isStronglyPEmbedded D hstrong
  refine false_of_permuting_three_big_of_stronglyEmbedded D c.std.h63 c.std.h126
    c.std.h1211 c.std.h111 c.std.h6161ii hk1 hstrong c.setting
    (mBarGT_two_of_threeNat c.setting hT) hYM hY3 hYexp hYnc hperm (Or.inr ?_)
  rw [hYcard]
  calc 9 = 3 ^ 2 := by norm_num
    _ < 3 ^ 3 := by norm_num
    _ ≤ 3 ^ (a + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)

theorem s168e3_false_of_sum_three_sl_four_of_r880
    {G : Type} [Group G] [Finite G] {D : Data G}
    {V₀ V L : Subgroup G} {hV : IsElemAbelian 2 V}
    (c : S168e3Ctx D V₀ V L hV)
    (h880 : CFSG.LocalAnalysis.UniquenessCase.UC22.F08.R880 D)
    (hcomp : IsComponentOf (lBar V₀ V hV L) (Mbar D.M V₀ V hV))
    (hsum : SumOfNatShape (lBar V₀ V hV L) (wTil V₀ V hV L)
      (wTil V₀ V hV L ⊓ fixV (lBar V₀ V hV L)) 3)
    (htrans : ∀ I₁ ∈ irrSet (lBar V₀ V hV L),
      ∀ I₂ ∈ irrSet (lBar V₀ V hV L),
      ∃ g ∈ Mbar D.M V₀ V hV ⊓ Subgroup.normalizer
        (lBar V₀ V hV L : Set (MulAut (Vtil V₀ V hV))),
        I₂ = I₁.map g.toMonoidHom)
    (hs : s15 D.M V₀ V hV L = 1)
    (hSL : IsSLn ↥(lBar V₀ V hV L) 4 1) : False := by
  have hT := s168e3_threeNat_of_s15_eq_one c hcomp hsum htrans hs
  have h7 := s168e3_irrSet_seven_of_sum_three c hcomp hsum htrans hs
  obtain ⟨N, hNA, hLN, hfixN, hcommNK, hNKbot, hNKsup, hKord⟩ := hT.structure_of_seven h7
  rcases hKord with hK7 | hK21 | ⟨hK168, hKsimple⟩
  · exact s168e3_false_of_kBar_seven_sl_four c hcomp hT h7 hSL hK7
  · exact s168e3_false_of_kBar_21_sl_four_of_r880 c h880 hcomp hT h7 hSL hK21
  · exact s168e3_false_of_kBar_168_sl_four_of_r880 c h880 hcomp hT h7 hSL hK168

end CFSG.LocalAnalysis.UniquenessCase.PartTwo
