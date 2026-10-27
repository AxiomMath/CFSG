module

public import CFSG.RankThree.PartTwo.Sec17.Item1712StepsProofClaims
import CFSG.LocalAnalysis.RankThreeEvenClassification.CoprimeFactorization
import CFSG.RankThree.PartTwo.Sec14.Item147
import CFSG.RankThree.PartTwo.Sec17.Item171ProofTools
import CFSG.RankThree.PartTwo.Sec15.HypS

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.RankThree.PartTwo.Sec16 CFSG.RankThree.PartTwo.Late CFSG.GH74.GLS
  CFSG.RankThree.PartTwo.Sec17.HeadProof
open CFSG.RankThreeEvenClassification.Helpers
  (exists_centralizer_with_same_image_of_trivial_quotient_action)

namespace Proof17Res6

variable {G : Type} [Group G] [Finite G] {A : Subgroup G} {c : G} {L Y₀ : Subgroup G}

theorem lB_inf_eq_bot
    (h : Sec17Std G A c L Y₀)
    (hΩ : omegaA A = {Subgroup.zpowers c}) :
    lB A (A ⊓ L) = ⊥ := by
  refine lB_eq_bot fun b d L' hc => ?_
  obtain ⟨hB, hbΩ, -⟩ := hc
  rw [hΩ, Set.mem_singleton_iff] at hbΩ
  have hcL : c ∉ L := h.toSec15R.hypS.2.2 c h.zpowers_mem_omegaA L h.mem_lA
  apply hcL
  have hcb : c ∈ Subgroup.zpowers b := hbΩ ▸ Subgroup.mem_zpowers c
  have hb : b ∈ A ⊓ L := by
    rw [hB]
    exact Subgroup.subset_closure (Set.mem_insert b {d})
  exact (Subgroup.mem_inf.mp (Subgroup.zpowers_le.mpr hb hcb)).2

omit [Finite G] in
theorem conj_inv_mul_mem_of_mem_cQuot {q b : G} (hq : q ∈ cQuot Y₀) (hb : b ∈ Y₀) :
    (b * q * b⁻¹)⁻¹ * q ∈ CFSG.Open.pCoreOf 2 Y₀ := by
  have hq' : q⁻¹ ∈ (cQuot Y₀ : Set G) := inv_mem hq
  rw [coe_cQuot] at hq'
  have h1 := inv_mem (hq'.2 b hb)
  have e : (q⁻¹ * b * q⁻¹⁻¹ * b⁻¹)⁻¹ = (b * q * b⁻¹)⁻¹ * q := by group
  rwa [e] at h1

theorem le_inf_centralizer_sup_of_le_cQuot {B Q : Subgroup G} (hB : IsPGroup 3 B) (hBY : B ≤ Y₀)
    (hBQ : B ≤ Subgroup.normalizer (Q : Set G)) (hQC : Q ≤ cQuot Y₀) :
    Q ≤ (Q ⊓ Subgroup.centralizer (B : Set G)) ⊔ CFSG.Open.pCoreOf 2 Y₀ := by
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  set M := Subgroup.normalizer (Y₀ : Set G) with hM
  set O := CFSG.Open.pCoreOf 2 Y₀ with hO
  have hOM : O ≤ M := (CFSG.LieType.BorelTits.pCoreOf_le 2 Y₀).trans Subgroup.le_normalizer
  have hMO : M ≤ Subgroup.normalizer (O : Set G) :=
    CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀
  have : (O.subgroupOf M).Normal := (Subgroup.normal_subgroupOf_iff_le_normalizer hOM).mpr hMO
  have hcQM : cQuot Y₀ ≤ M := fun z hz => by
    have hz' : z ∈ (cQuot Y₀ : Set G) := hz
    rw [coe_cQuot] at hz'
    exact hz'.1
  have hQM : Q ≤ M := hQC.trans hcQM
  set f : ↥Q →* ↥M ⧸ O.subgroupOf M :=
    (QuotientGroup.mk' (O.subgroupOf M)).comp (Subgroup.inclusion hQM) with hf
  have hfeq : ∀ x y : ↥Q, f x = f y ↔ ((x : G)⁻¹ * y) ∈ O := by
    intro x y
    rw [hf, MonoidHom.comp_apply, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      QuotientGroup.mk'_apply, QuotientGroup.eq, Subgroup.mem_subgroupOf]
    rfl
  have hker : ¬ 3 ∣ Nat.card f.ker := by
    have h2 : IsPGroup 2 f.ker := by
      have hk : f.ker = (O.subgroupOf M).comap (Subgroup.inclusion hQM) := by
        rw [hf, ← MonoidHom.comap_ker, QuotientGroup.ker_mk']
      rw [hk]
      exact ((CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₀).comap_subtype).comap_of_injective
        _ (Subgroup.inclusion_injective hQM)
    exact Proof171.not_three_dvd_of_isPGroup_two h2
  have htriv : ∀ (b : ↥B) (x : ↥Q), f ⟨b * x * (b : G)⁻¹,
      Subgroup.le_normalizer_iff.mp hBQ b b.property x x.property⟩ = f x := by
    intro b x
    refine (hfeq _ _).mpr ?_
    exact conj_inv_mul_mem_of_mem_cQuot (hQC x.2) (hBY b.2)
  intro q hq
  obtain ⟨q', hq'C, hq'e⟩ := exists_centralizer_with_same_image_of_trivial_quotient_action 3
    Nat.prime_three B Q hB hBQ f hker htriv ⟨q, hq⟩
  have hO' : ((q' : G))⁻¹ * q ∈ O := (hfeq q' ⟨q, hq⟩).mp hq'e
  have e : q = (q' : G) * ((q' : G)⁻¹ * q) := by group
  rw [e]
  exact Subgroup.mul_mem_sup ⟨q'.2, hq'C⟩ hO'

end Proof17Res6

section Certified

theorem claim1716Odd_proof (h9 : CardInfNineS17) : Claim1716Odd := by
  intro G _ _ A c L Y₀ h hΩ
  have : Fact (Nat.Prime 2) := ⟨Nat.prime_two⟩
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  set B := A ⊓ L with hBdef
  set O := CFSG.Open.pCoreOf 2 Y₀ with hO
  set P₁ := pPrimeCoreOf 3 (Subgroup.centralizer (B : Set G)) with hP₁
  set P₂ := pPrimeCoreOf 3 (Subgroup.centralizer (A : Set G)) with hP₂
  set F := P₁ ⊔ P₂ with hF
  set E := (F ⊓ cQuot Y₀) ⊔ O with hE
  have hA : IsE27 A := isE27_of_std h
  have hBhyp : IsHyperplane A B := ⟨inf_le_left, by rw [hA.2, h9 G A c L Y₀ h]⟩
  have hBY : B ≤ Y₀ := inf_le_right.trans h.le_y0
  have hLB : lB A B = ⊥ := Proof17Res6.lB_inf_eq_bot h hΩ
  have hB3 : IsPGroup 3 B := hA.isPGroup.to_le inf_le_left
  have hDE : delta A (lB A) (cQuot Y₀) ≤ E := by
    refine sSup_le fun Q hQ => ?_
    obtain ⟨hQQ, hQC⟩ := hQ
    have hBQ : B ≤ Subgroup.normalizer (Q : Set G) := inf_le_left.trans hQQ.1.2.2
    have hle := Proof17Res6.le_inf_centralizer_sup_of_le_cQuot hB3 hBY hBQ hQC
    have hQF : Q ⊓ Subgroup.centralizer (B : Set G) ≤ F := by
      have := hQQ.2 B hBhyp
      rwa [qBound, hLB, sup_bot_eq] at this
    refine hle.trans (sup_le_sup_right (le_inf hQF (inf_le_left.trans hQC)) _)
  have hcQM : cQuot Y₀ ≤ Subgroup.normalizer (Y₀ : Set G) := fun z hz => by
    have hz' : z ∈ (cQuot Y₀ : Set G) := hz
    rw [coe_cQuot] at hz'
    exact hz'.1
  have hFO : F ⊓ cQuot Y₀ ≤ Subgroup.normalizer (O : Set G) :=
    inf_le_right.trans (hcQM.trans (CFSG.LieType.BorelTits.normalizer_le_normalizer_pCoreOf 2 Y₀))
  have hP₂P₁ : P₂ ≤ Subgroup.normalizer (P₁ : Set G) :=
    ((pPrimeCoreOf_le 3 _).trans (Subgroup.centralizer_le (inf_le_left : B ≤ A))).trans
      (le_normalizer_pPrimeCoreOf 3 _)
  have hF' : F = P₂ ⊔ P₁ := sup_comm _ _
  have hFdvd : Nat.card F ∣ Nat.card P₂ * Nat.card P₁ := by
    rw [hF']
    exact card_sup_dvd_card_mul hP₂P₁
  have hEdvd : Nat.card E ∣ Nat.card P₂ * Nat.card P₁ * Nat.card O :=
    (card_sup_dvd_card_mul hFO).trans
      (Nat.mul_dvd_mul_right ((Subgroup.card_dvd_of_le inf_le_left).trans hFdvd) _)
  have hO3 : ¬ 3 ∣ Nat.card O :=
    Proof171.not_three_dvd_of_isPGroup_two (CFSG.LieType.BorelTits.pCoreOf_isPGroup (r := 2) Y₀)
  have hP₁3 : ¬ 3 ∣ Nat.card P₁ :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  have hP₂3 : ¬ 3 ∣ Nat.card P₂ :=
    (Nat.Prime.coprime_iff_not_dvd Nat.prime_three).mp (coprime_card_pPrimeCoreOf 3 _)
  intro h3
  rcases (Nat.Prime.dvd_mul Nat.prime_three).mp
      ((h3.trans (Subgroup.card_dvd_of_le hDE)).trans hEdvd) with h1 | h1
  · rcases (Nat.Prime.dvd_mul Nat.prime_three).mp h1 with h2 | h2
    · exact hP₂3 h2
    · exact hP₁3 h2
  · exact hO3 h1

end Certified

end CFSG.RankThree.PartTwo.Sec17
