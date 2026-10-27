module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBar
public import CFSG.LocalAnalysis.UniquenessCase.UCKInputs2
public import CFSG.LocalAnalysis.RankThreeTheoremC.SmallRankE3.P622KDEven
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBarJ1
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBarSz
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBarL3Two
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBarEven
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBarOdd
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBarBN
import CFSG.LocalAnalysis.UniquenessCase.UC22K108BigCoprime
import CFSG.LocalAnalysis.ComponentPrimeOrderAction
import CFSG.NumberTheory.TwoPowAddOneOdd
import CFSG.GroupTheory.ComponentCovering
import CFSG.Quasithin.Background.F7TwoE2Comp
import CFSG.GroupTheory.PRankZeroOfPrimeNotDvd
import CFSG.LocalAnalysis.UniquenessCase.UC22P2214h
import CFSG.Quasithin.Vol2.Ch5Sec1L34Lem516
public import CFSG.LocalAnalysis.ABGTheoremB.IV1

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBar

open Subgroup CFSG.LocalAnalysis.RankThreeTheoremC CFSG.Blueprint

variable {X : Type} [Group X] [Finite X]

theorem pRank_three_eq_one_of_dvd_card {L : Subgroup X}
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1) (h3L : 3 ∣ Nat.card L) :
    CFSG.Open.pRank 3 (⊤ : Subgroup ↥L) = 1 := by
  refine le_antisymm ?_ (CFSG.one_le_pRank_of_dvd_card Nat.prime_three h3L)
  exact (CFSG.SectionRank.pRank_top_le_of_injective (p := 3) (by norm_num) L.subtype
    L.subtype_injective).trans h3

theorem le_normalizer_inf_of_permuted {A U L : Subgroup X} {r : ℕ} (hr : r.Prime)
    (hr2 : r ≠ 2) (hA : Nat.card A = r) (hAU : UC22.Permutes A U) (hU : IsPGroup 2 U)
    (hAL : A ≤ normalizer (L : Set X)) (hrL : ¬ r ∣ Nat.card L)
    (hS : CFSG.ABGLocalTools.IsSylowOf 2 (U ⊓ L) L) :
    A ≤ normalizer ((U ⊓ L : Subgroup X) : Set X) := by
  have : Fact (Nat.Prime r) := ⟨hr⟩
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hAp : IsPGroup r A := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hA)
  have hdisj : A ⊓ U = ⊥ :=
    (IsPGroup.disjoint_of_ne r 2 hr2 A U hAp hU).eq_bot
  have hcard : Nat.card (A ⊔ U : Subgroup X) = r * Nat.card U := by
    rw [UC22.uc22p2214_card_sup_of_permutes hAU hdisj, hA]
  set M : Subgroup X := (A ⊔ U) ⊓ L with hM
  have hAM : A ≤ normalizer (M : Set X) :=
    (le_inf ((le_sup_left : A ≤ A ⊔ U).trans (A ⊔ U).le_normalizer) hAL).trans
      Subgroup.inf_normalizer_le_normalizer_inf
  have hML : M ≤ L := inf_le_right
  have hrM : ¬ r ∣ Nat.card M := fun h => hrL (h.trans (Subgroup.card_dvd_of_le hML))
  have hcopM : Nat.Coprime (Nat.card M) r :=
    (Nat.Prime.coprime_iff_not_dvd hr).mpr hrM |>.symm
  have hM_dvd : Nat.card M ∣ r * Nat.card U := by
    rw [← hcard]
    exact Subgroup.card_dvd_of_le inf_le_left
  have hM_dvd_U : Nat.card M ∣ Nat.card U :=
    (Nat.Coprime.dvd_mul_left hcopM).mp hM_dvd
  obtain ⟨k, hUk⟩ := hU.exists_card_eq
  have hMp : IsPGroup 2 M :=
    IsPGroup.of_card_dvd_pow (n := k) (by rwa [hUk] at hM_dvd_U)
  have hle : U ⊓ L ≤ M := le_inf (inf_le_left.trans le_sup_right) inf_le_right
  have hMeq : M = U ⊓ L := hS.eq_of_le hle hML hMp
  rwa [hMeq] at hAM

theorem inf_sup_centralizer_eq_of_splitBNPair_two {A U L : Subgroup X} {r : ℕ}
    [IsSimpleGroup ↥L] (hU : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤) (hL : CFSG.IsComponent L)
    (hAL : A ≤ normalizer (L : Set X)) (hrL : ¬ r ∣ Nat.card L) (hr : r.Prime)
    (hA : Nat.card A = r) (hAU : UC22.Permutes A U)
    (hBN : ∃ B N : Subgroup ↥L, CFSG.ASVolI.ChIJK.IsSplitBNPair 2 B N)
    (h2L : 2 ∣ Nat.card L) :
    (U ⊓ L) ⊔ (centralizer (A : Set X) ⊓ L) = L := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have hS : CFSG.ABGLocalTools.IsSylowOf 2 (U ⊓ L) L :=
    hU.inf_of_isSubnormal (CFSG.Open.IsSubnormal.top_iff.mpr hL.2)
  have hr2 : r ≠ 2 := fun h => hrL (h ▸ h2L)
  have hAS : A ≤ normalizer ((U ⊓ L : Subgroup X) : Set X) :=
    le_normalizer_inf_of_permuted hr hr2 hA hAU hU.isPGroup hAL hrL hS
  have hcop : ¬ Nat.card A ∣ Nat.card L := by rwa [hA]
  have hAp : (Nat.card A).Prime := by rw [hA]; exact hr
  exact UC22.F10.sylow_sup_centralizer_eq_of_splitBNPair Nat.prime_two hBN h2L hAp hAL
    hcop hS hAS

theorem commutator_eq_bot_of_component_odd {A L : Subgroup X} {r p : ℕ}
    [IsSimpleGroup ↥L] (hr : r.Prime) (hr3 : 3 < r)
    (hA : Nat.card A = r) (hAL : A ≤ normalizer (L : Set X)) (hrL : ¬ r ∣ Nat.card L)
    (hstar : StarCentralizes A r) (hp : p.Prime) (hp2 : p ≠ 2) (hpL : p ∣ Nat.card L)
    (hBN : ∃ B N : Subgroup ↥L, CFSG.ASVolI.ChIJK.IsSplitBNPair p B N)
    (hsq : p ^ 2 - 1 ∣ 6 * Nat.card L) : ⁅L, A⁆ = ⊥ := by
  have : Fact (Nat.Prime r) := ⟨hr⟩
  have : Fact (Nat.Prime p) := ⟨hp⟩
  have hAp : IsPGroup r A := IsPGroup.of_card (n := 1) (by rw [pow_one]; exact hA)
  obtain ⟨S, hSsyl, hAS⟩ :=
    CFSG.ABGTheoremB.exists_isSylowOf_normalized_of_coprime (p := r) (r := p) hr hp hAp hAL hrL
  have hcop : ¬ Nat.card A ∣ Nat.card L := by rwa [hA]
  have hAp' : (Nat.card A).Prime := by rw [hA]; exact hr
  have hgen : S ⊔ (centralizer (A : Set X) ⊓ L) = L :=
    UC22.F10.sylow_sup_centralizer_eq_of_splitBNPair hp hBN hpL hAp' hAL hcop hSsyl hAS
  have hpne : p ≠ r := fun h => hrL (h ▸ hpL)
  have hr6 : ¬ r ∣ 6 := by
    intro h
    have h23 : r = 2 ∨ r = 3 := by
      rw [show 6 = 2 * 3 by norm_num] at h
      rcases (Nat.Prime.dvd_mul hr).1 h with h2 | h3
      · exact Or.inl ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2)
      · exact Or.inr ((Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h3)
    omega
  have hnotdvd : ¬ r ∣ p ^ 2 - 1 := fun h => (hr.not_dvd_mul hr6 hrL) (h.trans hsq)
  have hScent : A ≤ centralizer (S : Set X) :=
    hstar p hp hp2 hpne hnotdvd S hSsyl.isPGroup hAS
  have hCcent : A ≤ centralizer (((centralizer (A : Set X)) ⊓ L : Subgroup X) : Set X) := by
    intro a ha
    exact (Subgroup.centralizer_le inf_le_left) (Set.subset_centralizer_centralizer ha)
  have hSc : S ≤ centralizer (A : Set X) := (Subgroup.le_centralizer_iff).mp hScent
  have hCc : ((centralizer (A : Set X)) ⊓ L : Subgroup X) ≤
      centralizer (A : Set X) := inf_le_left
  have hsup : S ⊔ (centralizer (A : Set X) ⊓ L) ≤ centralizer (A : Set X) := sup_le hSc hCc
  have hAcent : A ≤ centralizer (L : Set X) := by
    rw [← hgen]
    exact (Subgroup.le_centralizer_iff).mpr hsup
  have hcomm : ⁅A, L⁆ = ⊥ := Subgroup.commutator_eq_bot_iff_le_centralizer.mpr hAcent
  simpa [Subgroup.commutator_comm] using hcomm

theorem isJ1_or_suzuki_or_lieModel_of_isComponent (hK32 : UCK.K32)
    (hSz : SmallRankE3.KFactSuzukiThreeFree) (hK : CFSG.Open.IsKGroup X)
    (hrad : CFSG.solvableRadical X = ⊥) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1) :
    UC22.IsJ1 ↥L ∨ (∃ f : ℕ, SuzukiModel ↥L 2 f) ∨
      (∃ p f : ℕ, LieModel ↥L .PSL 2 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 2 ∧ LieModel ↥L .PSL 3 p f) ∨
      (∃ p f : ℕ, p ^ f % 3 = 1 ∧ LieModel ↥L .PSU 3 p f) := by
  have hsimp := CFSG.Quasithin.F7Two.isSimpleGroup_of_isComponent hrad hL
  have hnab := CFSG.Quasithin.F7Two.exists_mul_ne_of_isComponent hL
  have hKsub := hK.subgroup L
  by_cases h3L : 3 ∣ Nat.card L
  · have hrank := pRank_three_eq_one_of_dvd_card h3 h3L
    rcases hK32 ↥L hKsub hsimp hnab hrank with h2 | h3' | h3'' | hJ1
    · exact Or.inr (Or.inr (Or.inl h2))
    · exact Or.inr (Or.inr (Or.inr (Or.inl h3')))
    · exact Or.inr (Or.inr (Or.inr (Or.inr h3'')))
    · exact Or.inl hJ1
  · refine Or.inr (Or.inl (hSz ↥L hsimp ?_ hKsub h3L))
    rintro h
    obtain ⟨a, b, hab⟩ := hnab
    exact hab (h a b)

theorem barOne_or_barTwo_of_classical [IsSimpleGroup X] {A U : Subgroup X} {r : ℕ}
    (hnab : ∃ a b : X, a * b ≠ b * a) (hr : r.Prime) (hr3 : 3 < r)
    (hn : ∃ n : ℕ, Odd n ∧ r ∣ 2 ^ n + 1) (hA : Nat.card A = r)
    (hU : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤) (hAU : UC22.Permutes A U)
    (hrr : CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 1) {p f : ℕ}
    (hX : LieModel X .PSL 2 p f ∨
      (p ^ f % 3 = 2 ∧ LieModel X .PSL 3 p f) ∨
      (p ^ f % 3 = 1 ∧ LieModel X .PSU 3 p f)) :
    BarOne A U ∨ BarTwo A := by
  have h11 : 11 ≤ r := by
    obtain ⟨n, hodd, hrn⟩ := hn
    exact CFSG.NumberTheory.eleven_le_of_dvd_two_pow_add_one hr hr3 hodd hrn
  have hr2 : r ≠ 2 := by have := hr.two_le; omega
  have hrr' : CFSG.pRank r ↥(⊤ : Subgroup X) ≤ 1 := by
    rw [CFSG.SectionRank.pRank_eq_open_pRank_top r ↥(⊤ : Subgroup X),
      ← CFSG.SectionRank.pRank_eq_pRank_top_subgroup (⊤ : Subgroup X)]
    exact hrr
  rcases hX with h2 | ⟨hf, h3⟩ | ⟨hf, h3⟩
  · by_cases hp2 : p = 2
    · subst hp2
      exact Or.inl (barOne_of_lieModel_psl2_two hnab h2 hr hr2 hA hU hAU hrr')
    · exact Or.inr (barTwo_of_lieModel_odd h2.admissible.1 hp2 (Or.inl h2) hr h11 hA)
  · by_cases hp2 : p = 2
    · subst hp2
      exact (false_of_lieModel_psl3_two hnab h3 hf hr hr3 hn hA hU hAU).elim
    · exact Or.inr (barTwo_of_lieModel_odd h3.admissible.1 hp2
        (Or.inr (Or.inl ⟨hf, h3⟩)) hr h11 hA)
  · by_cases hp2 : p = 2
    · subst hp2
      exact Or.inl (barOne_of_lieModel_psu3_two hnab h3 hr hr2 hA hU hAU hrr')
    · exact Or.inr (barTwo_of_lieModel_odd h3.admissible.1 hp2
        (Or.inr (Or.inr ⟨hf, h3⟩)) hr h11 hA)

theorem le_normalizer_of_isComponent
    (hSz : SmallRankE3.KFactSuzukiThreeFree) (hK : CFSG.Open.IsKGroup X)
    (hrad : CFSG.solvableRadical X = ⊥) {A : Subgroup X} {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hn : ∃ n : ℕ, Odd n ∧ r ∣ 2 ^ n + 1) (hA : Nat.card A = r) (hstar : StarCentralizes A r) :
    ∀ L : Subgroup X, CFSG.IsComponent L → A ≤ normalizer (L : Set X) := by
  intro L hL
  by_contra hAL
  have hAp : (Nat.card A).Prime := by rw [hA]; exact hr
  by_cases h3L : 3 ∣ Nat.card L
  · obtain ⟨P, hP, hAP, hAPc⟩ :=
      CFSG.LocalAnalysis.exists_isPGroup_not_le_centralizer_of_not_le_normalizer hrad hL hAp hAL
        Nat.prime_three h3L
    have hnot8 : ¬ r ∣ 3 ^ 2 - 1 := by
      intro h
      have h2 : r ∣ 2 := by
        have h8 : 3 ^ 2 - 1 = 2 ^ 3 := by norm_num
        rw [h8] at h
        exact hr.dvd_of_dvd_pow h
      have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 h2
      omega
    exact hAPc (hstar 3 Nat.prime_three (by norm_num) (by omega) hnot8 P hP hAP)
  · have hsimp : IsSimpleGroup ↥L := CFSG.Quasithin.F7Two.isSimpleGroup_of_isComponent hrad hL
    have hnab := CFSG.Quasithin.F7Two.exists_mul_ne_of_isComponent hL
    have hnotcomm : ¬ ∀ a b : ↥L, a * b = b * a := by
      rintro h
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (h a b)
    obtain ⟨f, hSzM⟩ := hSz ↥L hsimp hnotcomm (hK.subgroup L) h3L
    have h5L : 5 ∣ Nat.card L := (CFSG.Quasithin.H13.five_dvd_card_of_suzukiModel hSzM).1
    obtain ⟨P, hP, hAP, hAPc⟩ :=
      CFSG.LocalAnalysis.exists_isPGroup_not_le_centralizer_of_not_le_normalizer hrad hL hAp hAL
        Nat.prime_five h5L
    have hr5 : r ≠ 5 := by
      intro h5
      subst h5
      obtain ⟨n, hodd, hrn⟩ := hn
      exact CFSG.NumberTheory.not_dvd_two_pow_add_one_of_even Nat.prime_five (by norm_num) hodd
        hrn (m := 2) even_two (by norm_num)
    have hnot24 : ¬ r ∣ 5 ^ 2 - 1 := by
      intro h
      have h24 : 5 ^ 2 - 1 = 2 ^ 3 * 3 := by norm_num
      rw [h24] at h
      rcases (Nat.Prime.dvd_mul hr).1 h with h2 | h3
      · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_two).1 (hr.dvd_of_dvd_pow h2)
        omega
      · have := (Nat.prime_dvd_prime_iff_eq hr Nat.prime_three).1 h3
        omega
    exact hAPc (hstar 5 Nat.prime_five (by norm_num) (Ne.symm hr5) hnot24 P hP hAP)

theorem barOne_or_barTwo_of_isSimpleGroup
    (hK32 : UCK.K32) (hSz : SmallRankE3.KFactSuzukiThreeFree)
    (hK : CFSG.Open.IsKGroup X) (hrad : CFSG.solvableRadical X = ⊥) (hsimp : IsSimpleGroup X)
    {A U : Subgroup X} {r : ℕ} (hr : r.Prime) (hr3 : 3 < r)
    (hn : ∃ n : ℕ, Odd n ∧ r ∣ 2 ^ n + 1) (hA : Nat.card A = r)
    (hU : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤) (hAU : UC22.Permutes A U)
    (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1)
    (hrr : CFSG.Open.pRank r (⊤ : Subgroup X) ≤ 1) : BarOne A U ∨ BarTwo A := by
  have hnab : ∃ a b : X, a * b ≠ b * a := by
    by_contra h
    push Not at h
    have : IsMulCommutative X := IsMulCommutative.of_comm h
    have htop : (⊤ : Subgroup X) ≤ CFSG.solvableRadical X :=
      le_sSup (show (⊤ : Subgroup X) ∈
        {N : Subgroup X | N.Normal ∧ Group.IsSolvable N} from ⟨inferInstance, inferInstance⟩)
    rw [hrad] at htop
    exact top_ne_bot (le_bot_iff.mp htop)
  have hrs : r ∣ Nat.card X := by
    rw [← hA]
    exact A.card_subgroup_dvd_card
  by_cases h3X : 3 ∣ Nat.card X
  · have hrank : CFSG.Open.pRank 3 (⊤ : Subgroup X) = 1 :=
      le_antisymm h3 (CFSG.one_le_pRank_of_dvd_card Nat.prime_three h3X)
    rcases hK32 X hK hsimp hnab hrank with h2 | h3' | h3'' | hJ1
    · obtain ⟨p, f, hX2⟩ := h2
      exact barOne_or_barTwo_of_classical hnab hr hr3 hn hA hU hAU hrr (p := p) (f := f)
        (Or.inl hX2)
    · obtain ⟨p, f, hf, hX3⟩ := h3'
      exact barOne_or_barTwo_of_classical hnab hr hr3 hn hA hU hAU hrr (p := p) (f := f)
        (Or.inr (Or.inl ⟨hf, hX3⟩))
    · obtain ⟨p, f, hf, hX3⟩ := h3''
      exact barOne_or_barTwo_of_classical hnab hr hr3 hn hA hU hAU hrr (p := p) (f := f)
        (Or.inr (Or.inr ⟨hf, hX3⟩))
    · have h11 : 11 ≤ r := by
        obtain ⟨n, hodd, hrn⟩ := hn
        exact CFSG.NumberTheory.eleven_le_of_dvd_two_pow_add_one hr hr3 hodd hrn
      exact (false_of_isJ1 hJ1 hr h11 hA hU hAU).elim
  · have hnotcomm : ¬ ∀ a b : X, a * b = b * a := by
      rintro h
      obtain ⟨a, b, hab⟩ := hnab
      exact hab (h a b)
    obtain ⟨f, hSzM⟩ := hSz X hsimp hnotcomm hK h3X
    exact (not_dvd_card_of_suzukiModel hSzM hr hr3 hn hrs).elim

theorem barThree_of_isComponent
    (hK32 : UCK.K32) (hSz : SmallRankE3.KFactSuzukiThreeFree) (hK : CFSG.Open.IsKGroup X)
    (hrad : CFSG.solvableRadical X = ⊥) {A U : Subgroup X} {r : ℕ} (hr : r.Prime)
    (hr3 : 3 < r) (hA : Nat.card A = r) (hU : CFSG.ABGLocalTools.IsSylowOf 2 U ⊤)
    (hAU : UC22.Permutes A U) (h3 : CFSG.Open.pRank 3 (⊤ : Subgroup X) ≤ 1)
    (hstar : StarCentralizes A r) {L : Subgroup X} (hL : CFSG.IsComponent L)
    (hAL : A ≤ normalizer (L : Set X)) (hrL : ¬ r ∣ Nat.card L) (hLA : ⁅L, A⁆ ≠ ⊥) :
    BarThree A U r := by
  have hAprime : (Nat.card A).Prime := by rw [hA]; exact hr
  have hcopA : ¬ Nat.card A ∣ Nat.card L := by rwa [hA]
  have hsimpleL : IsSimpleGroup ↥L := CFSG.Quasithin.F7Two.isSimpleGroup_of_isComponent hrad hL
  have hperfL : ⁅L, L⁆ = L := by
    have : Group.IsPerfect ↥L := hL.1.1
    exact Subgroup.commutator_eq_self
  have hgen : (U ⊓ L) ⊔ (centralizer (A : Set X) ⊓ L) = L := by
    have : IsSimpleGroup ↥L := hsimpleL
    rcases isJ1_or_suzuki_or_lieModel_of_isComponent hK32 hSz hK hrad hL h3 with
      hJ1 | ⟨f, hSzM⟩ | ⟨p, f, hX2⟩ | ⟨p, f, hf, hX3⟩ | ⟨p, f, hf, hX3⟩
    · exact absurd (commutator_eq_bot_of_isJ1 (G := X) hJ1 hAprime hAL hcopA) hLA
    · obtain ⟨h2L, hBN⟩ := exists_splitBNPair_of_suzukiModel hSzM
      exact inf_sup_centralizer_eq_of_splitBNPair_two hU hL hAL hrL hr hA hAU hBN h2L
    · obtain ⟨hp, hpL, hBN⟩ := exists_splitBNPair_of_lieModel hX2 (Or.inl ⟨rfl, Or.inl rfl⟩)
      by_cases hp2 : p = 2
      · subst hp2
        exact inf_sup_centralizer_eq_of_splitBNPair_two hU hL hAL hrL hr hA hAU hBN hpL
      · exact absurd (commutator_eq_bot_of_component_odd hr hr3 hA hAL hrL hstar hp hp2
          hpL hBN (sq_sub_one_dvd_of_lieModel hX2 (Or.inl ⟨rfl, Or.inl rfl⟩))) hLA
    · obtain ⟨hp, hpL, hBN⟩ := exists_splitBNPair_of_lieModel hX3 (Or.inl ⟨rfl, Or.inr rfl⟩)
      by_cases hp2 : p = 2
      · subst hp2
        exact inf_sup_centralizer_eq_of_splitBNPair_two hU hL hAL hrL hr hA hAU hBN hpL
      · exact absurd (commutator_eq_bot_of_component_odd hr hr3 hA hAL hrL hstar hp hp2
          hpL hBN (sq_sub_one_dvd_of_lieModel hX3 (Or.inl ⟨rfl, Or.inr rfl⟩))) hLA
    · obtain ⟨hp, hpL, hBN⟩ := exists_splitBNPair_of_lieModel hX3 (Or.inr ⟨rfl, rfl⟩)
      by_cases hp2 : p = 2
      · subst hp2
        exact inf_sup_centralizer_eq_of_splitBNPair_two hU hL hAL hrL hr hA hAU hBN hpL
      · exact absurd (commutator_eq_bot_of_component_odd hr hr3 hA hAL hrL hstar hp hp2
          hpL hBN (sq_sub_one_dvd_of_lieModel hX3 (Or.inr ⟨rfl, rfl⟩))) hLA
  exact ⟨L, hsimpleL, hperfL, hAL, hLA, hrL, hgen⟩

theorem k_UC146N_Bar_of_inputs
    (hK32 : UCK.K32) (hSz : SmallRankE3.KFactSuzukiThreeFree) : K_UC146N_Bar := by
  intro X _ _ A U r hK hrad hr hr3 hn hA hU hAU hgen h3 hrr hstar
  have hr2 : r ≠ 2 := by omega
  rcases CFSG.LocalAnalysis.isSimpleGroup_or_exists_isComponent hrad hr hr2 hA hgen hrr
      (le_normalizer_of_isComponent hSz hK hrad hr hr3 hn hA hstar) with
    hsimp | ⟨L, hL, hAL, hrL, hLA⟩
  · rcases barOne_or_barTwo_of_isSimpleGroup hK32 hSz hK hrad hsimp hr hr3 hn hA hU hAU h3 hrr
      with h | h
    · exact Or.inl h
    · exact Or.inr (Or.inl h)
  · exact Or.inr (Or.inr
      (barThree_of_isComponent hK32 hSz hK hrad hr hr3 hA hU hAU h3 hstar hL hAL hrL hLA))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs1719.KFourteenSixNBar
