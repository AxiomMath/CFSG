module

public import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z3Res
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229SEFZ
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229L34Torus
public import CFSG.LocalAnalysis.UniquenessCase.Lie.RankOneInput
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.KInputs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.Open.GriessAllModelsStatement
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3B1
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3L34
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229L34U3
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z5U3
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z6b
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZB
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Good
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
import CFSG.LocalAnalysis.UniquenessCase.UCR638
public import CFSG.GroupTheory.PCore.Transport
public import CFSG.LocalAnalysis.AGLEmbedding.ResidualTools

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Sec7Core4 StronglyEmbeddedFive
  StronglyEmbeddedFiveZ StronglyEmbeddedThree)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)

variable {G : Type} [Group G] [Finite G]

theorem R847E3.normalizer_le_of_isSU3_not_dvd (hSE : StronglyEmbeddedFive)
    (hSEZ : StronglyEmbeddedFiveZ) (hgr : GriessAllModelsStatement) (hC : uc22pwCartanSU3)
    (hS : Standing G) (S : Setup G) {p : ℕ} (hp : p ∈ (dataOfSetup hS S).sig) (hp5 : 5 ≤ p)
    {Y : Subgroup G} (hY : Y ∈ calC S.M) (hYN : (Y.subgroupOf S.M).Normal) {n : ℕ}
    (hYn : IsSU3 (Bar2 Y) n) (hpn : ¬ p ∣ 2 ^ n + 1) {X : Subgroup G} (hXY : X ≤ Y) {q : ℕ}
    (hq : q.Prime) (hq2 : q ≠ 2) (hqn : q ∣ 2 ^ n - 1) (hXc : Nat.card X = q) :
    normalizer (X : Set G) ≤ S.M := by
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  obtain ⟨hpP, hp2⟩ := (dataOfSetup hS S).sig_prime p hp
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hY) hp
  let k : Sec7Core4 G := Sec7Core4.ofThree hS S.M S.witness.maxLocal p hpP hp2 hsp
    (PartTwo.Three.normalizer_le_of_mem_sigmaOf S hp)
  have hYM : Y ≤ S.M := hY.1.le
  have hX1 : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hXc
    exact hq.one_lt.ne hXc
  obtain ⟨B₁, hB₁M, hB₁, hB₁c, hB₁X, hB₁Y⟩ := R847E3.exists_B₁_of_isSU3 hY
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hYM).1 hYN) hYn hpP hp2 hpn
    (UC6.opRes_eq_of_stronglyEmbedded_uc6 hS.simple hS.nonab hpP hsp) (hSg.three_le p hp) hXY
    hq hq2 (IsPGroup.of_card (n := 1) (by rw [hXc, pow_one]))
  obtain ⟨t, ht, ht2⟩ := uc22ine229_exists_involution_of_isSU3 hgr hC hY hYn hq hq2 hqn hXY hXc
  exact uc22ine229_normalizer_le_of_involution k hp5
    (k.kIDExcluded_of_evenRank_le_three (le_of_eq hS.rank)) hSE hSEZ hX1 (hXY.trans hYM) hB₁M
    hB₁ hB₁c hB₁X hYM hB₁Y ht ht2

theorem R847E3.normalizer_le_of_isSU3_three (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (hK3 : StronglyEmbeddedThree)
    (hgr : GriessAllModelsStatement) (hC : uc22pwCartanSU3) (hT : uc22pwTorusSU3)
    (hS : Standing G) (S : Setup G) (h846 : F08.R846 (dataOfSetup hS S))
    (hp : 3 ∈ (dataOfSetup hS S).sig) {Y : Subgroup G} (hY : Y ∈ calC S.M)
    (hYN : (Y.subgroupOf S.M).Normal) {n : ℕ} (hYn : IsSU3 (Bar2 Y) n) (hn : Even n)
    {X : Subgroup G} (hXY : X ≤ Y) {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) (hqn : q ∣ 2 ^ n - 1)
    (hXc : Nat.card X = q) : normalizer (X : Set G) ≤ S.M := by
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hY) hp
  let k : Sec7Core4 G := Sec7Core4.ofThree hS S.M S.witness.maxLocal 3 Nat.prime_three
    (by norm_num) hsp (PartTwo.Three.normalizer_le_of_mem_sigmaOf S hp)
  have hYM : Y ≤ S.M := hY.1.le
  have hq2 : q ≠ 2 := by omega
  have hpn : ¬ 3 ∣ 2 ^ n + 1 := by
    obtain ⟨m, hm⟩ := hn
    have h4 : 2 ^ n % 3 = 1 := by
      rw [hm, ← two_mul, pow_mul, Nat.pow_mod]
      norm_num
    omega
  obtain ⟨B₁, hB₁M, hB₁, hB₁c, hB₁X, hB₁Y⟩ := R847E3.exists_B₁_of_isSU3 hY
    ((Subgroup.normal_subgroupOf_iff_le_normalizer hYM).1 hYN) hYn Nat.prime_three (by norm_num)
    hpn (UC6.opRes_eq_of_stronglyEmbedded_uc6 hS.simple hS.nonab Nat.prime_three hsp)
    (hSg.three_le 3 hp) hXY hq hq2 (IsPGroup.of_card (n := 1) (by rw [hXc, pow_one]))
  obtain ⟨t, ht, ht2⟩ := uc22ine229_exists_involution_of_isSU3 hgr hC hY hYn hq hq2 hqn hXY hXc
  rcases R847E3.normalizer_le_or_l34 hG3 hRee hK3 k rfl hY hq hXY hXc hB₁M hB₁ hB₁c hB₁X hB₁Y ht
    ht2 with h | ⟨hH, hF⟩
  · exact h
  · exact (uc22ine229_l34_false_of_isSU3 hT hgr hG3 hRee k rfl hY hYn (h846 Y hY n hYn) hXY hq
      hq5 hXc hqn hH hF hB₁M hB₁ hB₁c hB₁X hB₁Y).elim

theorem r847E3SU3_dataOfSetup_of_dvd (hSE : StronglyEmbeddedFive)
    (hSEZ : StronglyEmbeddedFiveZ) (hG3 : Gls3StronglyThreeEmbeddedPlus)
    (hRee : CFSG.AGLEmbedding.KFactReeInvolution) (hK3 : StronglyEmbeddedThree)
    (hgr : GriessAllModelsStatement) (hC : uc22pwCartanSU3) (hT : uc22pwTorusSU3)
    (hS : Standing G) (S : Setup G) (h846 : F08.R846 (dataOfSetup hS S))
    (hdvd : R847E3Dvd (dataOfSetup hS S)) : R847E3SU3 (dataOfSetup hS S) := by
  intro Y hY hYN n hYn X hXY q hq hq2 hqn hXc p hp
  obtain ⟨hpP, hp2⟩ := (dataOfSetup hS S).sig_prime p hp
  rcases eq_or_ne p 3 with rfl | hp3
  · rcases Nat.even_or_odd n with hn | hn
    · rcases eq_or_ne q 3 with rfl | hq3
      · refine Or.inl (uc22ine229_normalizer_le_of_mem_sig (UC6S846.sigmaStd_dataOfSetup hS S) hY
          hp hXY ?_ (IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])))
        intro h
        rw [h, Subgroup.card_bot] at hXc
        omega
      · exact Or.inl (R847E3.normalizer_le_of_isSU3_three hG3 hRee hK3 hgr hC hT hS S h846 hp hY
          hYN hYn hn hXY hq (hq.five_le_of_ne_two_of_ne_three hq2 hq3) hqn hXc)
    · exact Or.inr ⟨rfl, hn⟩
  · have hp5 := hpP.five_le_of_ne_two_of_ne_three hp2 hp3
    by_cases hpn : p ∣ 2 ^ n + 1
    · exact Or.inl (hdvd Y hY hYN n hYn X hXY q hq hq2 hqn hXc p hp hp5 hpn)
    · exact Or.inl (R847E3.normalizer_le_of_isSU3_not_dvd hSE hSEZ hgr hC hS S hp hp5 hY hYN hYn
        hpn hXY hq hq2 hqn hXc)

end CFSG.LocalAnalysis.UniquenessCase.UC22
