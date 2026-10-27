module

public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229SEFZ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3Thin
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3L34
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z9
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z7
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z8
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z34
import CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7.Conclusion76
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeFacts
public import CFSG.LocalAnalysis.UniquenessCase.UC22S21a
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Sec7Core4 StronglyEmbeddedFive
  StronglyEmbeddedFiveZ StronglyEmbeddedThree)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)

variable {G : Type} [Group G] [Finite G]

@[expose] def R847E3Cent (D : Data G) : Prop :=
  ∀ Y ∈ calC D.M, F08.Thin8 Y → ∀ p ∈ D.sig,
    (∃ B₀ : Subgroup G, B₀ ≤ D.M ∧ IsElemAbelian p B₀ ∧ Nat.card B₀ = p ^ 2 ∧
      ∀ b ∈ B₀, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 D.M) →
    ∀ X : Subgroup G, X ≤ Y → ∀ q : ℕ, q.Prime → q ≠ 2 → Nat.card X = q →
      normalizer (X : Set G) ≤ D.M ∨
        (p = 3 ∧ 2 ≤ CFSG.Open.pRank 3 (barPreimage D.M (centE D.M)))

theorem R847E3.normalizer_le_of_thin_five_of_cent (hSE : StronglyEmbeddedFive)
    (hSEZ : StronglyEmbeddedFiveZ) (hS : Standing G) (S : Setup G) {p : ℕ}
    (hp : p ∈ (dataOfSetup hS S).sig) (hp5 : 5 ≤ p) {Y : Subgroup G} (hY : Y ∈ calC S.M)
    (hthin : F08.Thin8 Y) {B₀ : Subgroup G} (hB₀M : B₀ ≤ S.M) (hB₀ : IsElemAbelian p B₀)
    (hB₀c : Nat.card B₀ = p ^ 2) (hB₀Y : ∀ b ∈ B₀, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 S.M)
    {q : ℕ} (hq : q.Prime) (hq2 : q ≠ 2) {X : Subgroup G} (hXY : X ≤ Y) (hXc : Nat.card X = q) :
    normalizer (X : Set G) ≤ S.M := by
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  obtain ⟨hpP, hp2⟩ := (dataOfSetup hS S).sig_prime p hp
  haveI : Fact p.Prime := ⟨hpP⟩
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hY) hp
  let k : Sec7Core4 G := Sec7Core4.ofThree hS S.M S.witness.maxLocal p hpP hp2 hsp
    (PartTwo.Three.normalizer_le_of_mem_sigmaOf S hp)
  have hno : Sec7Core4.KIDExcluded k := k.kIDExcluded_of_evenRank_le_three (le_of_eq hS.rank)
  have h75 : Sec7Core4.Step75 k := k.step75 hp5 hSE
  have h76C : Sec7Core4.Step76C k := k.step76C_of_kIDExcluded hp5 hno hSE
  have hYM : Y ≤ S.M := hY.1.le
  suffices h : ∀ q : ℕ, ∀ X : Subgroup G, X ≤ Y → q.Prime → q ≠ 2 → Nat.card X = q →
      normalizer (X : Set G) ≤ S.M from h q X hXY hq hq2 hXc
  intro q
  induction q using Nat.strong_induction_on with
  | _ q ih =>
  intro X hXY hq hq2 hXc
  have hXq : IsPGroup q X := IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])
  have hX1 : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hXc
    exact hq.one_lt.ne hXc
  rcases eq_or_ne q p with rfl | hqp
  · exact uc22ine229_normalizer_le_of_mem_sig hSg hY hp hXY hX1 hXq
  obtain ⟨B₁, hB₁M, hB₁, hB₁c, hB₁X, hB₁Y⟩ := uc22ine229_exists_copy hYM hpP hp2 hq hq2
    hB₀M hB₀ hB₀c hB₀Y hXY hXq
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

theorem R847E3.normalizer_le_or_centE_of_thin_three_of_cent
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hRee : CFSG.AGLEmbedding.KFactReeInvolution)
    (hK3 : StronglyEmbeddedThree) (hS : Standing G) (S : Setup G)
    (hp : 3 ∈ (dataOfSetup hS S).sig) {Y : Subgroup G} (hY : Y ∈ calC S.M)
    (hthin : F08.Thin8 Y) {B₀ : Subgroup G} (hB₀M : B₀ ≤ S.M) (hB₀ : IsElemAbelian 3 B₀)
    (hB₀c : Nat.card B₀ = 3 ^ 2) (hB₀Y : ∀ b ∈ B₀, ∀ y ∈ Y, b * y * b⁻¹ * y⁻¹ ∈ pCoreOf 2 S.M)
    {q : ℕ} (hq : q.Prime) (hq5 : 5 ≤ q) {X : Subgroup G} (hXY : X ≤ Y)
    (hXc : Nat.card X = q) :
    normalizer (X : Set G) ≤ S.M ∨ 2 ≤ CFSG.Open.pRank 3 (barPreimage S.M (centE S.M)) := by
  have hYM : Y ≤ S.M := hY.1.le
  refine R847E3.normalizer_le_or_of_thin_three_of_l34
    (A := fun M => 2 ≤ CFSG.Open.pRank 3 (barPreimage M (centE M))) hG3 hRee hK3 ?_ hS S hp hY
    hthin ?_ hq hq5 hXY hXc
  · intro k hp3 h75 Y' hY' X' hXY' q' hq' hq5' hXc' hq1 hH hF B₁ hB₁M hB₁ hB₁c hB₁X hB₁Y
    exact R847E3.two_le_pRank_centE_of_l34 hG3 hRee k hp3 hY' hXY' hq' hq5' hXc' hq1 hH hF hB₁M
      hB₁ hB₁c hB₁Y
  · intro q hq hq5 X hXY hXc
    have hq2 : q ≠ 2 := by omega
    have hXq : IsPGroup q X := IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])
    exact uc22ine229_exists_copy hYM Nat.prime_three (by norm_num) hq hq2 hB₀M hB₀ hB₀c hB₀Y hXY
      hXq

theorem r847E3Cent_dataOfSetup (hSE : StronglyEmbeddedFive) (hSEZ : StronglyEmbeddedFiveZ)
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hRee : CFSG.AGLEmbedding.KFactReeInvolution)
    (hK3 : StronglyEmbeddedThree) (hS : Standing G) (S : Setup G) :
    R847E3Cent (dataOfSetup hS S) := by
  intro Y hY hthin p hp ⟨B₀, hB₀M, hB₀, hB₀c, hB₀Y⟩ X hXY q hq hq2 hXc
  obtain ⟨hpP, hp2⟩ := (dataOfSetup hS S).sig_prime p hp
  rcases eq_or_ne p 3 with rfl | hp3
  · rcases eq_or_ne q 3 with rfl | hq3
    · refine Or.inl (uc22ine229_normalizer_le_of_mem_sig (UC6S846.sigmaStd_dataOfSetup hS S) hY
        hp hXY ?_ (IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])))
      intro h
      rw [h, Subgroup.card_bot] at hXc
      omega
    · rcases R847E3.normalizer_le_or_centE_of_thin_three_of_cent hG3 hRee hK3 hS S hp hY
        hthin hB₀M hB₀ hB₀c hB₀Y hq (hq.five_le_of_ne_two_of_ne_three hq2 hq3) hXY hXc with h | h
      · exact Or.inl h
      · exact Or.inr ⟨rfl, h⟩
  · exact Or.inl (R847E3.normalizer_le_of_thin_five_of_cent hSE hSEZ hS S hp
      (hpP.five_le_of_ne_two_of_ne_three hp2 hp3) hY hthin hB₀M hB₀ hB₀c hB₀Y hq hq2 hXY hXc)

end CFSG.LocalAnalysis.UniquenessCase.UC22
