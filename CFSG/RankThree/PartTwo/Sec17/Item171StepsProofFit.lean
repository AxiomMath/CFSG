module

public import CFSG.RankThree.PartTwo.Sec17.Item1711Proof
import CFSG.RankThree.PartTwo.Sec14.Item148StepPoint

public section

namespace CFSG.RankThree.PartTwo.Sec17

open CFSG CFSG.RankThree CFSG.RankThree.LocalRank CFSG.RankThree.PartTwo
  CFSG.RankThree.PartTwo.Sec13 CFSG.RankThree.PartTwo.Sec14 CFSG.RankThree.PartTwo.Sec15
  CFSG.GH74.GLS

@[expose] noncomputable def Step1711FitP : Prop :=
  ∀ (G : Type) [Group G] [Finite G] (A : Subgroup G) (c : G) (L Y₀ : Subgroup G),
    Sec17Std G A c L Y₀ → ∀ a ∈ A, a ≠ 1 → ∀ b ∈ A, b ≠ 1 →
    ∀ U ∈ fourGroups A, U = ⁅U, Subgroup.zpowers a⁆ →
      U ∈ collectionIn (scriptQ A (lB A))
        (CFSG.Open.pCoreOf 2 (Subgroup.normalizer (Y₀ : Set G)) ⊓
          Subgroup.centralizer ({b} : Set G)) →
      CFSG.Open.pCoreOf 2 (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) = ⊥ →
      ¬ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ≤ Subgroup.normalizer (Y₀ : Set G) →
      ⁅k1711 A b, U⁆ ≤ pPrimeCoreOf 3 (k1711 A b) →
        ∃ (p : ℕ) (Z : Subgroup G), p.Prime ∧ p ≠ 2 ∧ p ≠ 3 ∧ IsPGroup p Z ∧
          Z ≤ delta A (lB A) (Subgroup.centralizer ({b} : Set G)) ∧
          A ≤ Subgroup.normalizer (Z : Set G) ∧ U ≤ Subgroup.normalizer (Z : Set G) ∧ ⁅Z, U⁆ ≠ ⊥

namespace Proof171Steps

variable {G : Type} [Group G] [Finite G]

theorem mem_scriptQ_of_le_delta {A : Subgroup G} (h142 : Concl142 A (lB A))
    (h143 : Concl143 A (lB A)) {b : G} (hb : b ∈ A) (hb1 : b ≠ 1) {Z : Subgroup G}
    (hZD : Z ≤ delta A (lB A) (Subgroup.centralizer ({b} : Set G))) (hZ3 : ¬ 3 ∣ Nat.card Z)
    (hAZ : A ≤ Subgroup.normalizer (Z : Set G)) : Z ∈ scriptQ A (lB A) := by
  have hpi : IsPiSubgroup (piCompl 3) Z := (isPiSubgroup_piCompl_iff Nat.prime_three Z).mpr hZ3
  by_cases hbΩ : Subgroup.zpowers b ∈ omegaA A
  · have hCH : Subgroup.centralizer ({b} : Set G) ≤
        Subgroup.normalizer (Subgroup.zpowers b : Set G) := by
      rw [← centralizer_zpowers148]
      exact Subgroup.centralizer_le_normalizer _
    have hZH : Z ∈ invariantPiSubgroups (Subgroup.normalizer (Subgroup.zpowers b : Set G)) A
        (piCompl 3) := ⟨(hZD.trans (delta_le _)).trans hCH, hpi, hAZ⟩
    obtain ⟨Qs, hQs, hZQs⟩ := exists_le_mem_maxInvariantPiSubgroups hZH
    exact mem_scriptQ_of_le (h142 b hbΩ Qs hQs).1 hZQs hAZ
  · have hZΔ : Z ∈ invariantPiSubgroups (delta A (lB A) (Subgroup.centralizer ({b} : Set G))) A
        (piCompl 3) := ⟨hZD, hpi, hAZ⟩
    obtain ⟨Qs, hQs, hZQs⟩ := exists_le_mem_maxInvariantPiSubgroups hZΔ
    exact mem_scriptQ_of_le (h143 b hb hb1 hbΩ Qs hQs).1 hZQs hAZ

end Proof171Steps

end CFSG.RankThree.PartTwo.Sec17
