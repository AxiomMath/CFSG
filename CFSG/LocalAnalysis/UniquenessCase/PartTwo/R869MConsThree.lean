module

public import CFSG.LocalAnalysis.UniquenessCase.UC22C117MCons
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.DataThree
public import CFSG.LocalAnalysis.UniquenessCase.UC7P3Defs
import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R869MThreeA
import CFSG.LocalAnalysis.UniquenessCase.UC6R869MConj
import CFSG.LocalAnalysis.UniquenessCase.UC6S846e

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22.F08

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]

@[expose] def R869MRest3 (D : Data G) : Prop :=
  ∀ L : Subgroup G,
    (L ∈ calC D.M ∨ (L ≤ D.M ∧ D.M ≤ normalizer (L : Set G) ∧ IsProdOfCalC D.M L)) →
    ¬ Thin8 L → (∀ p ∈ D.sig, CFSG.Open.pRank p L ≤ 1) →
    (∀ q : ℕ, q.Prime → q ≠ 2 → ∀ Q : Subgroup G, Q ≤ L → IsPGroup q Q →
      2 ≤ CFSG.Open.pRank q Q → ¬ rankThreeGamma 1 q Q ≤ D.M) →
    (D.M ≤ normalizer (L : Set G) →
      ¬ (center (Bar2 L) = ⊥ ∧
        IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L))) ∧
      ∀ p ∈ D.sig, p ∣ Nat.card L ∧
        ∀ A : Subgroup G, A ≤ D.M → IsElemAbelian p A → Nat.card A = p ^ 2 →
          ¬ ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ pCoreOf 2 L) →
    UniqueMax D.M L

@[expose] def R869MConsRest3 (D : Data G) : Prop :=
  ∀ L : Subgroup G, L ∈ calC D.M → D.M ≤ normalizer (L : Set G) → ¬ Thin8 L →
    ¬ (center (Bar2 L) = ⊥ ∧
      IsCyclic (CFSG.ComponentClassification.OuterAutomorphisms.Outer (Bar2 L))) →
    (∀ p ∈ D.sig, CFSG.Open.pRank p L ≤ 1 ∧ p ∣ Nat.card L ∧
      ∀ A : Subgroup G, A ≤ D.M → IsElemAbelian p A → Nat.card A = p ^ 2 →
        ¬ ∀ a ∈ A, ∀ l ∈ L, a * l * a⁻¹ * l⁻¹ ∈ pCoreOf 2 L) →
    (∀ q : ℕ, q.Prime → q ≠ 2 → ∀ Q : Subgroup G, Q ≤ L → IsPGroup q Q →
      2 ≤ CFSG.Open.pRank q Q → ¬ rankThreeGamma 1 q Q ≤ D.M) →
    UniqueMax D.M L

end CFSG.LocalAnalysis.UniquenessCase.UC22.F08

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three

open Subgroup CFSG.Open CFSG.LocalAnalysis.RankThreeUC CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.LocalAnalysis.UniquenessCase.PartOne.Section7 (StronglyEmbeddedFive StronglyEmbeddedThree)

variable {G : Type} [Group G] [Finite G]

theorem r869MCons_dataOfSetup_of_rest3 (hSE : StronglyEmbeddedFive)
    (hSE3 : StronglyEmbeddedThree) (hS : Standing G) (hUC : rankThreeUC G)
    (hC : AGL81TheoremC G) (S : Setup G) (h : F08.R869MConsRest3 (dataOfSetup hS S)) :
    F08.R869MCons (dataOfSetup hS S) := by
  intro L hL hthin
  have hLM : L ≤ S.M := by
    rcases hL with ⟨hL, -⟩ | ⟨K, hK, -, rfl⟩
    · exact hL.1.le
    · exact (uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hK).1
  have hML : S.M ≤ normalizer (L : Set G) := by
    rcases hL with ⟨-, hN⟩ | ⟨K, hK, -, rfl⟩
    · exact hN
    · exact (uc22p22u_conjClosure_isProd le_rfl Subgroup.le_normalizer hK).2.1
  have hns : ¬ Group.IsSolvable ↥(dataOfSetup hS S).M := by
    rcases hL with ⟨hL, -⟩ | ⟨K, hK, -, -⟩
    · exact UC6S846.not_solvable_of_mem_calC hL
    · exact UC6S846.not_solvable_of_mem_calC hK
  by_cases hΓ : ∃ q : ℕ, q.Prime ∧ q ≠ 2 ∧ ∃ Q : Subgroup G, Q ≤ L ∧ IsPGroup q Q ∧
      2 ≤ CFSG.Open.pRank q Q ∧ rankThreeGamma 1 q Q ≤ S.M
  · obtain ⟨q, hq, hq2, Q, hQL, hQ, h2, hQΓ⟩ := hΓ
    exact UC6.R869S.uniqueMax_of_theoremCAt S.witness.maxLocal
      (hC hUC S.p S.hp S.P S.M S.witness) hq hq2 hLM hQL hQ h2 hQΓ
  have hfree : ∀ q : ℕ, q.Prime → q ≠ 2 → ∀ Q : Subgroup G, Q ≤ L → IsPGroup q Q →
      2 ≤ CFSG.Open.pRank q Q → ¬ rankThreeGamma 1 q Q ≤ S.M :=
    fun q hq hq2 Q hQL hQ h2 hQΓ => hΓ ⟨q, hq, hq2, Q, hQL, hQ, h2, hQΓ⟩
  have hσ1 : ∀ p ∈ sigmaOf S.M, CFSG.Open.pRank p L ≤ 1 := fun p hp =>
    pRank_le_one_of_gammaFree hS S hns hLM hfree hp
  have hdvd : ∀ p ∈ sigmaOf S.M, p ∣ Nat.card L := fun p hp => by
    by_contra hLp
    exact hΓ (exists_gamma_le_of_not_dvd hSE hSE3 hS hUC S hns hLM hML hthin hp hLp)
  rcases hL with ⟨hL, hN⟩ | ⟨K, hK, hnot, rfl⟩
  · refine h L hL hN hthin (fun ⟨hZ, hOut⟩ => ?_) (fun p hp => ⟨hσ1 p hp, hdvd p hp,
      fun A hAM hAel hAc hAL => hΓ (exists_gamma_le_of_centralizing hSE hSE3 hS S hns hLM hN
        hthin hp hAM hAel hAc hAL)⟩) hfree
    obtain ⟨A, hAM, hAel, hAc, hAL⟩ := exists_centralizing_of_cyclic_outer hS S hLM hN hZ hOut
      (mem_sigmaOf S) (hσ1 S.p (mem_sigmaOf S))
    exact hΓ (exists_gamma_le_of_centralizing hSE hSE3 hS S hns hLM hN hthin (mem_sigmaOf S)
      hAM hAel hAc hAL)
  ·
    have hpσ := mem_sigmaOf S
    have hσ := (dataOfSetup hS S).sig_prime S.p hpσ
    exact absurd (hdvd S.p hpσ)
      (UC6.R869S.not_dvd_card_conjClosure hK hnot hσ.1 hσ.2 (hσ1 S.p hpσ))

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.Three
