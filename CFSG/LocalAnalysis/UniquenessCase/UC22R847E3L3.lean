module

public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
public import CFSG.LocalAnalysis.AGLEmbedding.CaseTwoReeFacts
public import CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree.Gls3Plus
public import CFSG.LocalAnalysis.UniquenessCase.UC22InE229SEFZ
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Inputs13
public import CFSG.RankThree.PartTwo.Sec11.Item116R1CensusPure
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3Thin
import CFSG.LocalAnalysis.UniquenessCase.UC22R847E3B1
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z3Good
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z3Inv
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z8
import CFSG.LocalAnalysis.UniquenessCase.UC22InE229Z9
import CFSG.LocalAnalysis.UniquenessCase.UC22P2251b
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Conclusion76Three
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Fourteen1
import CFSG.LocalAnalysis.UniquenessCase.UC6S846h
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
public import CFSG.LocalAnalysis.UniquenessCase.UCFront08
public import CFSG.LocalAnalysis.UniquenessCase.UCR638

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open CFSG.LocalAnalysis.RankThreeUC Subgroup
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (Sec7Core4 StronglyEmbeddedFive
  StronglyEmbeddedFiveZ StronglyEmbeddedThree)
open CFSG.HardMathSupport.RichardWeiss.RecognitionPresentation.StrongThree
  (Gls3StronglyThreeEmbeddedPlus)
open CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three (dataOfSetup)

variable {G : Type} [Group G] [Finite G]

theorem R847E3.mem_centralizer_of_isL3 {Y : Subgroup G} (hL3 : IsL3 (Bar2 Y) 1)
    {X : Subgroup G} (hXY : X ≤ Y) (hXc : Nat.card X = 7) {u : G}
    (hu : u ∈ Y ⊓ normalizer (X : Set G)) {e : ℕ} (he : u ^ 2 ^ e = 1) :
    u ∈ centralizer (X : Set G) := by
  have hXb : Nat.card ((X.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))) = 7 :=
    uc22ine229_card_map hXY Nat.prime_seven (by norm_num) hXc
  have h21 := PartTwo.card_normalizer_seven_of_isL3 hL3 hXb
  let y : ↥Y := ⟨u, hu.1⟩
  have hyN : y ∈ normalizer ((X.subgroupOf Y : Subgroup ↥Y) : Set ↥Y) := by
    rw [← Subgroup.subgroupOf_normalizer_eq hXY, Subgroup.mem_subgroupOf]
    exact hu.2
  have hyb := Subgroup.le_normalizer_map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y))
    (Subgroup.mem_map_of_mem _ hyN)
  have h1 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y) ∣ 2 ^ e := by
    refine orderOf_dvd_of_pow_eq_one ?_
    rw [← map_pow, show y ^ 2 ^ e = 1 from Subtype.ext (by simpa using he), map_one]
  have h2 := Subgroup.orderOf_dvd_natCard _ hyb
  rw [h21] at h2
  have h3 : orderOf (QuotientGroup.mk' (CFSG.pCore 2 ↥Y) y) = 1 :=
    Nat.Coprime.eq_one_of_dvd
      (Nat.Coprime.coprime_dvd_left h1 (Nat.Coprime.pow_left e (by norm_num))) h2
  rw [orderOf_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff] at h3
  rw [Subgroup.mem_centralizer_iff]
  intro x hx
  let x' : ↥Y := ⟨x, hXY hx⟩
  have hcP : y * x' * y⁻¹ * x'⁻¹ ∈ CFSG.pCore 2 ↥Y := by
    have h := (inferInstance : (CFSG.pCore 2 ↥Y).Normal).conj_mem _ (inv_mem h3) x'
    simpa [mul_assoc] using mul_mem h3 h
  have hcX : y * x' * y⁻¹ * x'⁻¹ ∈ X.subgroupOf Y := by
    rw [Subgroup.mem_subgroupOf]
    exact mul_mem ((Subgroup.mem_normalizer_iff.1 hu.2 x).1 hx) (inv_mem hx)
  have hXq : IsPGroup 7 X := IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])
  have h1 := UC6S846.eq_one_of_mem_isPGroup_of_mem_isPGroup Nat.prime_seven (by norm_num)
    hXq.comap_subtype CFSG.pCore_isPGroup hcX hcP
  have h2 : u * x * u⁻¹ * x⁻¹ = 1 := congrArg Subtype.val h1
  calc x * u = u * x * u⁻¹ * x⁻¹ * (x * u) := by rw [h2, one_mul]
    _ = u * x := by group

theorem R847E3.normalizer_le_of_isL3_three (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hRee : CFSG.AGLEmbedding.KFactReeInvolution)
    (hK3 : StronglyEmbeddedThree) (hS : Standing G) (S : Setup G)
    (hp : 3 ∈ (dataOfSetup hS S).sig) {Y : Subgroup G} (hY : Y ∈ calC S.M)
    (hYN : (Y.subgroupOf S.M).Normal) (hL3 : IsL3 (Bar2 Y) 1) {X : Subgroup G} (hXY : X ≤ Y)
    (hXc : Nat.card X = 7) : normalizer (X : Set G) ≤ S.M := by
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hthin : F08.Thin8 Y := uc22p2251b_thin8 (Or.inr hL3)
  have hsp := UC6S846.sp_of_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hY) hp
  let k : Sec7Core4 G := Sec7Core4.ofThree hS S.M S.witness.maxLocal 3 Nat.prime_three
    (by norm_num) hsp (PartTwo.Three.normalizer_le_of_mem_sigmaOf S hp)
  have hp3 : k.p = 3 := rfl
  have hK : CFSG.Open.IsKGroup ↥S.M := hS.kProper.isKGroup S.M hsp.1
  have hYM : Y ≤ S.M := hY.1.le
  have hMN : S.M ≤ normalizer (Y : Set G) :=
    (Subgroup.normal_subgroupOf_iff_le_normalizer hYM).1 hYN
  have hOp := UC6.opRes_eq_of_stronglyEmbedded_uc6 hS.simple hS.nonab Nat.prime_three hsp
  have h3 := hSg.three_le 3 hp
  have h75 : Sec7Core4.Step75 k := k.step75_of_stronglyEmbeddedThree hp3 hK3
  have hq : (7 : ℕ).Prime := by norm_num
  have hXq : IsPGroup 7 X := IsPGroup.of_card (n := 1) (by rw [hXc, pow_one])
  have hX1 : X ≠ ⊥ := by
    intro h
    rw [h, Subgroup.card_bot] at hXc
    omega
  obtain ⟨B₁, hB₁M, hB₁, hB₁c, hB₁X, hB₁Y⟩ := R847E3.exists_B₁_of_thin hThin hCyc hK hY hMN
    hthin Nat.prime_three (by norm_num) hOp h3 hXY hq (by norm_num) hXq
  rcases uc22ine229_normalizer_le_or_card_le_two k hp3 hK3 hX1 (hXY.trans hYM) hB₁M hB₁ hB₁c
    hB₁X with h | hQ
  · exact h
  by_contra hnot
  have hB₁N : B₁ ≤ normalizer (X : Set G) :=
    hB₁X.trans (Subgroup.centralizer_le_normalizer (X : Set G))
  have hH := k.config_normalizer hX1 (hXY.trans hYM)
    (CFSG.SectionRank.le_pRank k.prime.one_lt (le_inf hB₁M hB₁N) hB₁ hB₁c) hnot
  have hW := uc22ine229_le_centralizer3 hB₁M hQ hB₁ hB₁X hB₁Y
  obtain ⟨w, ⟨hwY, hwN⟩, hwC⟩ :=
    uc22ine229_exists_not_mem_centralizer_of_thin hY hthin hq (by norm_num) hXY hXc
  obtain ⟨ℓ, hℓ, hℓ6, u, hu, ⟨e, he⟩, huC⟩ := uc22ine229_exists_prime_part hq hXc hwN hwC
  have huW : u ∈ Y ⊓ normalizer (X : Set G) :=
    (Subgroup.zpowers_le.2 (show w ∈ Y ⊓ normalizer (X : Set G) from ⟨hwY, hwN⟩)) hu
  have hℓ' : ℓ ∣ 2 * 3 := hℓ6
  rcases (Nat.Prime.dvd_mul hℓ).1 hℓ' with h2 | h3'
  ·
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_two).1 h2
    exact huC (R847E3.mem_centralizer_of_isL3 hL3 hXY hXc huW he)
  ·
    obtain rfl := (Nat.prime_dvd_prime_iff_eq hℓ Nat.prime_three).1 h3'
    obtain ⟨j, -, hj⟩ := (Nat.dvd_prime_pow Nat.prime_three).1 (orderOf_dvd_of_pow_eq_one he)
    have hup : IsPGroup 3 (Subgroup.zpowers u) :=
      IsPGroup.of_card (n := j) (by rw [Nat.card_zpowers, hj])
    exact huC (k.mem_centralizer_of_commute h75 hH (k.goodZ3_of_config hG3 hRee hp3 hH).1
      (uc22ine229_le_pPrimeCore_normalizer k.prime hq (by rw [hp3]; norm_num) hXc)
      (le_inf hB₁N hB₁M) hB₁ hB₁c hB₁X ⟨huW.2, hYM huW.1⟩ hup
      fun a ha => (Subgroup.mem_centralizer_iff.mp (hW huW)) a ha)

@[expose] def R847E3L3 (D : Data G) : Prop :=
  ∀ Y ∈ calC D.M, (Y.subgroupOf D.M).Normal → IsL3 (Bar2 Y) 1 → ∀ X : Subgroup G, X ≤ Y →
    (Nat.card X).Prime → Nat.card X ≠ 2 → normalizer (X : Set G) ≤ D.M

theorem r847E3L3_dataOfSetup (hSE : StronglyEmbeddedFive) (hSEZ : StronglyEmbeddedFiveZ)
    (hThin : PartTwo.ThinList13)
    (hCyc : CFSG.RankThree.PartTwo.Sec11.CyclicSylowThreeOutAbelian)
    (hG3 : Gls3StronglyThreeEmbeddedPlus) (hRee : CFSG.AGLEmbedding.KFactReeInvolution)
    (hK3 : StronglyEmbeddedThree) (hS : Standing G) (S : Setup G) :
    R847E3L3 (dataOfSetup hS S) := by
  intro Y hY hYN hL3 X hXY hXp hX2
  have hSg := UC6S846.sigmaStd_dataOfSetup hS S
  obtain ⟨p, hp⟩ := hSg.nonempty
  obtain ⟨hpP, hp2⟩ := (dataOfSetup hS S).sig_prime p hp
  have hthin : F08.Thin8 Y := uc22p2251b_thin8 (Or.inr hL3)
  rcases eq_or_ne p 3 with rfl | hp3
  · rcases eq_or_ne (Nat.card X) 3 with h3 | h3
    · refine uc22ine229_normalizer_le_of_mem_sig hSg hY hp hXY ?_
        (IsPGroup.of_card (n := 1) (by rw [h3, pow_one]))
      intro h
      rw [h, Subgroup.card_bot] at h3
      omega
    · have hdvd : Nat.card X ∣ 2 ^ 3 * (3 * 7) := by
        have h := Subgroup.card_subgroup_dvd_card
          ((X.subgroupOf Y).map (QuotientGroup.mk' (CFSG.pCore 2 ↥Y)))
        rwa [uc22ine229_card_map hXY hXp hX2 rfl, PartTwo.card_eq_of_isL3 hL3] at h
      have h7 : Nat.card X = 7 := by
        rcases (Nat.Prime.dvd_mul hXp).1 hdvd with h | h
        · exact absurd ((Nat.prime_dvd_prime_iff_eq hXp Nat.prime_two).1
            (hXp.dvd_of_dvd_pow h)) hX2
        · rcases (Nat.Prime.dvd_mul hXp).1 h with h | h
          · exact absurd ((Nat.prime_dvd_prime_iff_eq hXp Nat.prime_three).1 h) h3
          · exact (Nat.prime_dvd_prime_iff_eq hXp (by norm_num)).1 h
      exact R847E3.normalizer_le_of_isL3_three hThin hCyc hG3 hRee hK3 hS S hp hY hYN hL3 hXY h7
  · exact R847E3.normalizer_le_of_thin_five hSE hSEZ hThin hCyc hS S hp
      (hpP.five_le_of_ne_two_of_ne_three hp2 hp3) hY hYN hthin hXp hX2 hXY rfl

end CFSG.LocalAnalysis.UniquenessCase.UC22

end
