module

public import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofCharThree
public import CFSG.RankThree.PartTwo.Sec4.Item417Res5ProofOut
import CFSG.RankThree.PartTwo.Sec4.Item413BackL43
import CFSG.RankThree.PartTwo.Sec4.Census.CoverCenterThreeRestG2
import CFSG.RankThree.PartTwo.Sec4.Item417Res3ProofIn
import CFSG.RankThree.PartTwo.KFacts.KS21Mult

public section

namespace CFSG.RankThree.PartTwo.Sec4

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo CFSG.Blueprint
open CFSG.Assembly.RankThreeEven (projSL projSU)

open CFSG.Assembly.LowTwoRank (StatedLieAdmissible)

open CFSG.ComponentClassification.TBLit (GriessMultipliersAllModels)

open Res417Three Res417Five

namespace Res417Five

theorem not_dvd_of_dvd_forty_eight {n : ℕ} (hn : n ∣ 48) {p : ℕ} (hp : p.Prime) (hp3 : 3 < p) :
    ¬ p ∣ n := by
  intro hpn
  have h : p ∣ 2 ^ 4 * 3 := (hpn.trans hn).trans (by norm_num)
  rcases (Nat.Prime.dvd_mul hp).mp h with h2 | h3
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
    omega
  · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
    omega

theorem card_table_PSL_four_three :
    Nat.card (Blueprint.Multiplier.generic .PSL 4 3 1 ×
      Blueprint.Multiplier.exceptional .PSL 4 3 1) ∣ 48 := by
  rw [Nat.card_prod, Res417.card_zmod_prod, Res417.card_zmod_prod]
  simp [Blueprint.Multiplier.genericOrders, Blueprint.Multiplier.exceptionalOrders]

@[expose] def K417NoActLThreeThree : Prop :=
  ∀ e : ℕ, 1 ≤ e → e ≤ 2 →
    (∀ F T : Subgroup (projSL 3 (GaloisField 3 e)), CFSG.Assembly.IsElemAbelian 3 F →
      9 ≤ Nat.card F → IsPGroup 2 T → F ≤ Subgroup.normalizer (T : Set _) →
        T ≤ Subgroup.centralizer (F : Set _)) ∧
    (∀ F T : Subgroup (projSU 3 3 e), CFSG.Assembly.IsElemAbelian 3 F →
      9 ≤ Nat.card F → IsPGroup 2 T → F ≤ Subgroup.normalizer (T : Set _) →
        T ≤ Subgroup.centralizer (F : Set _))

@[expose] def K417E81G23 : Prop :=
  ∀ (X : Type) [Group X], ChevalleyExceptionalModel X .G2 3 1 →
    ∃ P E₀ T₀ : Subgroup X, CFSG.Assembly.IsElemAbelian 3 P ∧ Nat.card P = 3 ^ 4 ∧
      E₀ ≤ P ∧ Nat.card E₀ = 9 ∧ IsPGroup 2 T₀ ∧
      E₀ ≤ Subgroup.normalizer (T₀ : Set X) ∧ ¬ T₀ ≤ Subgroup.centralizer (E₀ : Set X)

@[expose] def K417E81U43 : Prop :=
  ∃ P E₀ T₀ : Subgroup (projSU 4 3 1), CFSG.Assembly.IsElemAbelian 3 P ∧ Nat.card P = 3 ^ 4 ∧
    E₀ ≤ P ∧ Nat.card E₀ = 9 ∧ IsPGroup 2 T₀ ∧
    E₀ ≤ Subgroup.normalizer (T₀ : Set (projSU 4 3 1)) ∧
    ¬ T₀ ≤ Subgroup.centralizer (E₀ : Set (projSU 4 3 1))

end Res417Five

section Certs


theorem item417OutCharThreeRest_of (hGA : GriessMultipliersAllModels)
    (hL3 : K417NoActLThreeThree) (hG2 : K417E81G23) (hU4 : K417E81U43) :
    Item417OutCharThreeRest := by
  intro G _ _ L A E c m hconf hX
  have hLq := hconf.2.2.1.1
  have : Group.IsPerfect L := hLq.1
  have hθ48 : Nat.card (Subgroup.center L) ∣ 48 → aschbacherSolvableCore 3 L = ⊥ := fun h48 =>
    theta_eq_bot_of_two_three hconf.2.1 hconf.2.2.1 fun p hp hp3 =>
      not_dvd_of_dvd_forty_eight h48 hp hp3
  rcases hX with ⟨e, he1, he2, ⟨⟨φ⟩⟩ | ⟨⟨φ⟩⟩⟩ | ⟨⟨φ⟩⟩ | hG2m | ⟨⟨φ⟩⟩
  ·
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hadm : StatedLieAdmissible .PSL 3 3 e :=
      ⟨Nat.prime_three, he1, by norm_num, by simp, by simp⟩
    have hdvd := KFacts.KS21Mult.card_center_dvd_griess hLq.1 (hconf.centerEquiv.trans φ)
    obtain ⟨eM⟩ := (hGA _ .PSL 3 3 e (KFacts.KS21Mult.lieModel_projSL hadm)).2
    rw [Nat.card_congr eM.toEquiv] at hdvd
    have hθ := hθ48 (hdvd.trans (Res417.card_table_PSL_three_dvd 3 e))
    obtain ⟨hdat, -, -⟩ := hconf.datum ((Res417.thetaQuotEquivOfEqBot hθ).symm.trans φ)
    obtain ⟨hDe, -, F, hFD, hF9, T, hT2, hFT, hTF⟩ := hdat
    exact hTF ((hL3 e he1 he2).1 F T (isElemAbelian_of_le hDe hFD) hF9 hT2 hFT)
  ·
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hq2 : 3 ^ e ≠ 2 := by
      have : 3 ≤ 3 ^ e := by
        calc 3 = 3 ^ 1 := by norm_num
          _ ≤ 3 ^ e := Nat.pow_le_pow_right (by norm_num) he1
      omega
    have hadm : StatedLieAdmissible .PSU 3 3 e :=
      ⟨Nat.prime_three, he1, le_refl 3, fun h3 => hq2 (Prod.mk.inj h3).2⟩
    have hdvd := KFacts.KS21Mult.card_center_dvd_griess hLq.1 (hconf.centerEquiv.trans φ)
    obtain ⟨eM⟩ := (hGA _ .PSU 3 3 e (KFacts.KS21Mult.lieModel_projSU hadm)).2
    rw [Nat.card_congr eM.toEquiv] at hdvd
    have hθ := hθ48 ((hdvd.trans (Res417.card_table_PSU_three_dvd 3 e)).trans (by norm_num))
    obtain ⟨hdat, -, -⟩ := hconf.datum ((Res417.thetaQuotEquivOfEqBot hθ).symm.trans φ)
    obtain ⟨hDe, -, F, hFD, hF9, T, hT2, hFT, hTF⟩ := hdat
    exact hTF ((hL3 e he1 he2).2 F T (isElemAbelian_of_le hDe hFD) hF9 hT2 hFT)
  ·
    have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
    have hadm : StatedLieAdmissible .PSL 4 3 1 :=
      ⟨Nat.prime_three, le_rfl, by norm_num, by simp, by simp⟩
    have hdvd := KFacts.KS21Mult.card_center_dvd_griess hLq.1 (hconf.centerEquiv.trans φ)
    obtain ⟨eM⟩ := (hGA _ .PSL 4 3 1 (KFacts.KS21Mult.lieModel_projSL hadm)).2
    rw [Nat.card_congr eM.toEquiv] at hdvd
    have hθ := hθ48 (hdvd.trans card_table_PSL_four_three)
    set ψ := (Res417.thetaQuotEquivOfEqBot hθ).symm.trans φ
    obtain ⟨P, E₀, T₀, hP, hP81, hE₀P, hE₀9, hT₀, hE₀T₀, hT₀E₀⟩ := L43.backSimple_L43 L ψ
    exact hconf.false_of_e81 hθ (MulEquiv.refl L) hP hP81 hE₀P hE₀9 hT₀ hE₀T₀ hT₀E₀
  ·
    have hM := CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv hconf.centerEquiv hG2m
    have h3 := Census.CoverCenterThreeRest.card_center_dvd_three_of_G2 hGA hLq hM
    have hθ := hθ48 (h3.trans (by norm_num))
    have hG2L := CFSG.SectionRank.chevalleyExceptionalModel_of_mulEquiv
      (Res417.thetaQuotEquivOfEqBot hθ).symm hG2m
    obtain ⟨P, E₀, T₀, hP, hP81, hE₀P, hE₀9, hT₀, hE₀T₀, hT₀E₀⟩ := hG2 L hG2L
    exact hconf.false_of_e81 hθ (MulEquiv.refl L) hP hP81 hE₀P hE₀9 hT₀ hE₀T₀ hT₀E₀
  ·
    have h12 : ∀ z ∈ Subgroup.center L, z ^ 12 = 1 := fun z hz =>
      pow_twelve_eq_one_of_center_U43 hGA hLq (hconf.centerEquiv.trans φ) hz
    have hθ : aschbacherSolvableCore 3 L = ⊥ :=
      theta_eq_bot_of_two_three hconf.2.1 hconf.2.2.1 fun p hp hp3 hpZ => by
        have : Fact p.Prime := ⟨hp⟩
        obtain ⟨z, hz⟩ := exists_prime_orderOf_dvd_card' (G := Subgroup.center L) p hpZ
        have hz12 : z ^ 12 = 1 := Subtype.ext (by simpa using h12 z z.2)
        have hd : p ∣ 12 := hz ▸ orderOf_dvd_of_pow_eq_one hz12
        have : p ∣ 2 ^ 2 * 3 := by simpa using hd
        rcases (Nat.Prime.dvd_mul hp).mp this with h2 | h3
        · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_two).mp (hp.dvd_of_dvd_pow h2)
          omega
        · have := (Nat.prime_dvd_prime_iff_eq hp Nat.prime_three).mp h3
          omega
    obtain ⟨P, E₀, T₀, hP, hP81, hE₀P, hE₀9, hT₀, hE₀T₀, hT₀E₀⟩ := hU4
    exact hconf.false_of_e81 hθ ((Res417.thetaQuotEquivOfEqBot hθ).symm.trans φ) hP hP81 hE₀P
      hE₀9 hT₀ hE₀T₀ hT₀E₀

end Certs

end CFSG.RankThree.PartTwo.Sec4
