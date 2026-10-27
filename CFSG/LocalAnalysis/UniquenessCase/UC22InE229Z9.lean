module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z6b
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229ZBThin
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z7
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z8
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z34
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4 Setup4)

variable {G : Type} [Group G] [Finite G]

theorem uc22ine229_le_pPrimeCore_normalizer {X : Subgroup G} {p q : ℕ} (hp : p.Prime)
    (hq : q.Prime) (hqp : q ≠ p) (hXc : Nat.card X = q) :
    X ≤ (CFSG.pPrimeCore p ↥(normalizer (X : Set G))).map (normalizer (X : Set G)).subtype := by
  have hXH : X ≤ normalizer (X : Set G) := Subgroup.le_normalizer
  have hcop : Nat.Coprime p (Nat.card (X.subgroupOf (normalizer (X : Set G)))) := by
    rw [Nat.card_congr (Subgroup.subgroupOfEquivOfLe hXH).toEquiv, hXc]
    exact (Nat.coprime_primes hp hq).mpr (Ne.symm hqp)
  have hle : X.subgroupOf (normalizer (X : Set G)) ≤
      CFSG.pPrimeCore p ↥(normalizer (X : Set G)) :=
    le_sSup ⟨Subgroup.normal_in_normalizer, hcop⟩
  intro x hx
  exact ⟨⟨x, hXH hx⟩, hle (Subgroup.mem_subgroupOf.mpr hx), rfl⟩

theorem uc22ine229_normalizer_le_of_thin_setup4 (hSE : StronglyEmbeddedFive)
    (hSEZ : StronglyEmbeddedFiveZ) (hB3 : BadNoStrongThree) (hThin : PartTwo.ThinList13)
    (hOut : RankThreeTheoremC.KFactOutCyclic) (hS : Standing4 G) (hU : uniqueFourUnique G)
    (S : Setup4 G) (hσ : S.InMSigma) {p : ℕ} (hp : p ∈ (UC6.dataOfSetup4 hS hU S).sig)
    (hp5 : 5 ≤ p) {Y : Subgroup G} (hY : Y ∈ calC (UC6.dataOfSetup4 hS hU S).M)
    (hthin : F08.Thin8 Y) {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {X : Subgroup G} (hXY : X ≤ Y)
    (hXc : Nat.card X = q) : normalizer (X : Set G) ≤ (UC6.dataOfSetup4 hS hU S).M := by
  have hSg := UC6S846.sigmaStd_dataOfSetup4 hS hU S
  have hpP : p.Prime := ((UC6.dataOfSetup4 hS hU S).sig_prime p hp).1
  haveI : Fact p.Prime := ⟨hpP⟩
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hY) hp
  let k : Sec7Core4 G := .ofUnique hS hU S.M S.maxLocal p hp hsp
  have hno : Sec7Core4.KIDExcluded k := uc22ine229_kIDExcluded_setup4 hB3 hS hU S hσ hp hp5 hsp
  have h75 : Sec7Core4.Step75 k := k.step75 hp5 hSE
  have h76C : Sec7Core4.Step76C k := k.step76C_of_kIDExcluded hp5 hno hSE
  have hK : CFSG.Open.IsKGroup ↥(UC6.dataOfSetup4 hS hU S).M := hS.kProper.isKGroup S.M hsp.1
  have h4 := UC6.four_le_pRank_of_sigma hp
  have hYM : Y ≤ (UC6.dataOfSetup4 hS hU S).M := hY.1.le
  suffices h : ∀ q : ℕ, ∀ X : Subgroup G, X ≤ Y → q.Prime → q ≠ 2 → Nat.card X = q →
      normalizer (X : Set G) ≤ (UC6.dataOfSetup4 hS hU S).M from h q X hXY hq hq2 hXc
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro X hXY hq hq2 hXc
  have hXq : IsPGroup q X := IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])
  have hX1 : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hXc
    exact hq.one_lt.ne hXc
  by_cases hqs : q ∈ (UC6.dataOfSetup4 hS hU S).sig
  · exact uc22ine229_normalizer_le_of_mem_sig hSg hY hqs hXY hX1 hXq
  have hqp : q ≠ p := fun h => hqs (h ▸ hp)
  obtain ⟨B₁, hB₁M, hB₁, hB₁c, hB₁X, hB₁Y⟩ := uc22ine229_exists_B₁_of_thin hThin hOut hK hY
    hthin hpP hp5 h4 hXY hq hq2 hXc (uc22ine229_pRank_le_three hSg hq hq2 hqs)
  rcases uc22ine229_normalizer_le_or_inf_eq_bot k hp5 hno hSE hX1 (hXY.trans hYM) hB₁M hB₁ hB₁c
    hB₁X with h | hQ
  · exact h
  by_contra hnot
  have hB₁N : B₁ ≤ normalizer (X : Set G) :=
    hB₁X.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  have hH := k.config_normalizer hX1 (hXY.trans hYM)
    (CFSG.SectionRank.le_pRank hpP.one_lt (le_inf hB₁M hB₁N) hB₁ hB₁c) hnot
  have hW := uc22ine229_le_centralizer hQ hB₁X hB₁Y
  obtain ⟨w, ⟨hwY, hwN⟩, hwC⟩ :=
    uc22ine229_exists_not_mem_centralizer_of_thin hY hthin hq hq2 hXY hXc
  rcases uc22ine229_trichotomy hq hXc hwY hwN hwC p with
    ⟨t, ht, ht2⟩ | ⟨y, hy, hyP, hy2, hyp, hyq⟩ | ⟨-, u, hu, hup, huC⟩
  · exact hnot (uc22ine229_normalizer_le_of_involution k hp5 hno hSE hSEZ hX1 (hXY.trans hYM)
      hB₁M hB₁ hB₁c hB₁X hYM hB₁Y ht ht2)
  ·
    obtain ⟨x, hxB, hx1⟩ : ∃ x ∈ B₁, x ≠ 1 := by
      rcases Subgroup.bot_or_exists_ne_one B₁ with h | h
      · rw [h, Subgroup.card_bot] at hB₁c
        exact absurd hB₁c (Nat.one_lt_pow (by norm_num) hpP.one_lt).ne
      · exact h
    obtain ⟨j, hjM, hjy⟩ := k.exists_not_mem_commute_of_prime h75 k.step72L h76C hH
      ⟨hB₁N hxB, hB₁M hxB⟩ ⟨hy.2, hYM hy.1⟩ (hB₁.isPGroup.to_le (Subgroup.zpowers_le.2 hxB))
      hx1 hyP hy2 hyp ((Subgroup.mem_centralizer_iff.mp (hW hy)) x hxB)
    have hyN := ih (orderOf y) hyq (Subgroup.zpowers y) (Subgroup.zpowers_le.2 hy.1) hyP hy2
      (Nat.card_zpowers y)
    have hjC : j ∈ centralizer ((Subgroup.zpowers y : Subgroup G) : Set G) := by
      rw [Subgroup.zpowers_eq_closure, Subgroup.centralizer_closure,
        Subgroup.mem_centralizer_singleton_iff]
      exact hjy
    exact hjM (hyN (Subgroup.centralizer_le_normalizer _ hjC))
  ·
    exact huC (k.mem_centralizer_of_commute h75 hH (k.goodZ_of_kIDExcluded hp5 hno hH hSEZ h75).2
      (uc22ine229_le_pPrimeCore_normalizer hpP hq hqp hXc) (le_inf hB₁N hB₁M) hB₁ hB₁c hB₁X
      ⟨hu.2, hYM hu.1⟩ hup fun a ha => (Subgroup.mem_centralizer_iff.mp (hW hu)) a ha)

end CFSG.LocalAnalysis.UniquenessCase.UC22
