module

public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndStarOuter
public import CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3.A10EndAutThreeInner

import CFSG.HardMathSupport.Solomon.Coordinator.B3Local
import CFSG.LocalAnalysis.RankThreeTheoremC.KFactProofs.SmallRank.OutThreeCore
import CFSG.LocalAnalysis.SectionRank.SubgroupRank

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3

variable {X : Type} [Group X] [Finite X]

@[expose] def KFactOutThreeTwentySeven : Prop :=
  ∀ (L : Type) [Group L] [Finite L], IsSimpleGroup L → (∃ a b : L, a * b ≠ b * a) →
    CFSG.Open.IsCatalogGroup L → CFSG.Open.pRank 3 (⊤ : Subgroup L) = 2 →
    (Nat.card L).factorization 3 = 3 →
    ∀ φ : MulAut L, (∃ n : ℕ, φ ^ (3 ^ n) = 1) → ∃ k : L, φ = MulAut.conj k

private lemma mem_of_pow_eq_one (h27 : KFactOutThreeTwentySeven) {L : Subgroup X}
    (hLn : L.Normal) (hLs : IsSimpleGroup ↥L) (hnab : ∃ a b : ↥L, a * b ≠ b * a)
    (hcat : CFSG.Open.IsCatalogGroup ↥L) (hC : Subgroup.centralizer (L : Set X) = ⊥)
    (hrank : CFSG.Open.pRank 3 L = 2) (hfac : (Nat.card L).factorization 3 = 3)
    {x : X} {n : ℕ} (hx : x ^ (3 ^ n) = 1) : x ∈ L := by
  haveI : L.Normal := hLn
  have hφ : ∃ m : ℕ, (MulAut.conjNormal (H := L) x) ^ (3 ^ m) = 1 :=
    ⟨n, by rw [← map_pow, hx, map_one]⟩
  obtain ⟨k, hk⟩ := h27 ↥L hLs hnab hcat
    (by rw [← CFSG.SectionRank.pRank_eq_pRank_top_subgroup L]; exact hrank) hfac _ hφ
  have hmem : (k : X)⁻¹ * x ∈ Subgroup.centralizer (L : Set X) := by
    rw [Subgroup.mem_centralizer_iff]
    intro y hy
    have hconj : ((MulAut.conjNormal (H := L) x) ⟨y, hy⟩ : ↥L) = (MulAut.conj k) ⟨y, hy⟩ := by
      rw [hk]
    have h1 : x * y * x⁻¹ = (k : X) * y * (k : X)⁻¹ := by
      have := congrArg Subtype.val hconj
      simpa [MulAut.conjNormal_apply, MulAut.conj_apply] using this
    calc y * ((k : X)⁻¹ * x) = (k : X)⁻¹ * ((k : X) * y * (k : X)⁻¹) * x := by group
      _ = (k : X)⁻¹ * (x * y * x⁻¹) * x := by rw [h1]
      _ = ((k : X)⁻¹ * x) * y := by group
  rw [hC, Subgroup.mem_bot] at hmem
  have hxk : x = (k : X) := by
    calc x = (k : X) * ((k : X)⁻¹ * x) := by group
      _ = (k : X) := by rw [hmem, mul_one]
  rw [hxk]
  exact k.2

theorem kFactAutThreeRankTwo_of_kFacts (hIA : RankThreeTheoremC.KFactInnerAction)
    (h27 : KFactOutThreeTwentySeven) : KFactAutThreeRankTwo := by
  intro X _ _ L hKg hLn hLs hnab hC hrank hnot81L h81X
  haveI : IsSimpleGroup ↥L := hLs
  have hK : CFSG.IsKGroup ↥L :=
    CFSG.IsKGroup.subgroup
      (CFSG.HardMathSupport.Solomon.Coordinator.isKGroup_of_openIsKGroup hKg) L
  have hcat : CFSG.Open.IsCatalogGroup ↥L :=
    RankThreeTheoremC.KFactProofs.SmallRank.isCatalogGroup_of_isKGroup_simple hK
  have h9 : 9 ∣ Nat.card L := by
    obtain ⟨E, hE, -, hEcard⟩ := CFSG.SectionRank.exists_pRank (p := 3) (by norm_num) L
    have hdvd : Nat.card E ∣ Nat.card L := Subgroup.card_dvd_of_le hE
    rw [hEcard, hrank] at hdvd
    simpa using hdvd
  by_cases h27L : 27 ∣ Nat.card L
  ·
    have hfac : (Nat.card L).factorization 3 = 3 := by
      have hne : Nat.card L ≠ 0 := (Nat.card_pos (α := ↥L)).ne'
      have h3 : 3 ≤ (Nat.card L).factorization 3 :=
        (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mp (by
          simpa [show (3 : ℕ) ^ 3 = 27 by norm_num] using h27L)
      have h4 : ¬ 4 ≤ (Nat.card L).factorization 3 := by
        intro h
        have hd : 3 ^ 4 ∣ Nat.card L :=
          (Nat.Prime.pow_dvd_iff_le_factorization Nat.prime_three hne).mpr h
        exact hnot81L (by simpa [show (3 : ℕ) ^ 4 = 81 by norm_num] using hd)
      omega
    obtain ⟨R⟩ : Nonempty (Sylow 3 X) := Sylow.nonempty
    have h81R : 81 ∣ Nat.card ↥(R : Subgroup X) := by
      have h := R.pow_dvd_card_of_pow_dvd_card (p := 3) (n := 4)
        (by simpa [show (3 : ℕ) ^ 4 = 81 by norm_num] using h81X)
      simpa [show (3 : ℕ) ^ 4 = 81 by norm_num] using h
    have hRL : (R : Subgroup X) ≤ L := by
      intro x hx
      have hxcard : x ^ (3 ^ (Nat.card X).factorization 3) = 1 := by
        have h1 : (⟨x, hx⟩ : ↥(R : Subgroup X)) ^ Nat.card ↥(R : Subgroup X) = 1 :=
          pow_card_eq_one'
        rw [R.card_eq_multiplicity] at h1
        simpa using congrArg Subtype.val h1
      exact mem_of_pow_eq_one h27 hLn hLs hnab hcat hC hrank hfac hxcard
    exact hnot81L (h81R.trans (Subgroup.card_dvd_of_le hRL))
  · exact A10Gen.not_eightyone_dvd_card_of_innerAction hIA hLn hLs hnab hcat hC h9 h27L h81X

end CFSG.LocalAnalysis.UniquenessCase.PartOne.Theorem82E3
