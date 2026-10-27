module

public import CFSG.RankThree.PartOne.Mult.Trim
public import CFSG.RankThree.PartOne.K159.CenterRank
import CFSG.RankThree.PartOne.S10.EmbeddingTransport
public import CFSG.RankThree.PartOne.S8.Statements

public section

namespace CFSG.RankThree.PartOne.K159

open CFSG CFSG.Assembly CFSG.Assembly.LowTwoRank CFSG.Blueprint.Multiplier CFSG.RankThree.PartOne
  CFSG.RankThree.PartOne.Mult Subgroup
open CFSG.Blueprint.NativeSporadic (Carrier)

theorem centerRankFour_of_residual_trim
    (hbridge : TauCetiCatalogBridge)
    (hGA : CFSG.Open.GriessAllModelsStatement)
    (hres : SporadicResidualKernelsTrim)
    (hFi22 : SectionsForceEvenRankFour (Carrier .Fi22))
    (hFi23 : SectionsForceEvenRankFour (Carrier .Fi23))
    (hFi24 : SectionsForceEvenRankFour (Carrier .Fi24Prime))
    (hB : SectionsForceEvenRankFour (Carrier .B))
    (hM : SimplePresentationMSectionsForceEvenRankFour) : CenterRankFour := by
  intro X _ _ he hKX O _ hQq p hp hp3 hpZ hodd
  set Q := X ⧸ O with hQ
  have hQK : CFSG.IsKGroup Q := EmbeddingTransport.isKGroup_quotient hKX _
  have hqt : CFSG.IsQuasisimple (⊤ : Subgroup Q) :=
    CFSG.LocalCores.isQuasisimple_of_mulEquiv (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q).symm hQq
  have hsimple' : IsSimpleGroup ((⊤ : Subgroup Q) ⧸ Subgroup.center (⊤ : Subgroup Q)) := hqt.2.1
  have hcat : CFSG.Blueprint.Catalog ((⊤ : Subgroup Q) ⧸ Subgroup.center (⊤ : Subgroup Q)) :=
    hbridge _ hqt.2.2 (hQK ⊤ (Subgroup.center (⊤ : Subgroup Q)) hsimple')
  have hcardZ : Nat.card (Subgroup.center (⊤ : Subgroup Q)) = Nat.card (Subgroup.center Q) :=
    Nat.card_congr (Subgroup.centerCongr (Subgroup.topEquiv : (⊤ : Subgroup Q) ≃* Q)).toEquiv
  have hpZ' : p ∣ Nat.card (Subgroup.center (⊤ : Subgroup Q)) := by rw [hcardZ]; exact hpZ
  have hodd' : Odd (Nat.card (Subgroup.center (⊤ : Subgroup Q))) := by rw [hcardZ]; exact hodd
  have : Group.IsPerfect ↥(⊤ : Subgroup Q) := hqt.1
  have transport : (∃ B : Subgroup ↥(⊤ : Subgroup Q), (∀ b ∈ B, b ^ p = 1) ∧
      (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧ p ^ 4 ≤ Nat.card B) →
      ∃ B : Subgroup Q, (∀ b ∈ B, b ^ p = 1) ∧ (∀ a ∈ B, ∀ b ∈ B, a * b = b * a) ∧
        p ^ 4 ≤ Nat.card B := by
    rintro ⟨B, hBp, hBc, hBcard⟩
    refine ⟨B.map (⊤ : Subgroup Q).subtype, ?_, ?_, ?_⟩
    · rintro _ ⟨b, hb, rfl⟩
      rw [← map_pow, hBp b hb, map_one]
    · rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
      rw [← map_mul, ← map_mul, hBc a ha b hb]
    · rw [Subgroup.card_map_of_injective (⊤ : Subgroup Q).subtype_injective]
      exact hBcard
  apply transport
  rcases hcat with ⟨q, hq, ⟨e⟩⟩ | ⟨m, hm, ⟨e⟩⟩ | hcl | hex | hsp
  · exfalso
    obtain ⟨a, b, hab⟩ := hqt.2.2
    exact hab (e.injective (by rw [map_mul, map_mul]; exact mul_comm _ _))
  · exact absurd hpZ' (alternating_center_small_primes hm e hp hp3)
  · obtain ⟨t, n, ℓ, f, hmod⟩ := hcl
    exact exists_elemAbelian_four_of_model hGA hqt hmod hp hp3 hpZ' hodd'
  · exact absurd hpZ' (exceptionalCenterSmallPrimes_of_griess hGA _ hqt hex p hp hp3)
  · exfalso
    obtain ⟨s, ⟨e⟩⟩ := hsp
    by_cases hexc : SectionExcluded s
    ·
      obtain ⟨H, K, hK, ⟨φ⟩⟩ := exists_section_of_quotient_subgroup O (⊤ : Subgroup Q)
      have hrank : 4 ≤ evenRank X := by
        rcases hexc with rfl | rfl | rfl | rfl | rfl
        · exact hFi22 X H K ⟨φ.trans e⟩
        · exact hFi23 X H K ⟨φ.trans e⟩
        · exact hFi24 X H K ⟨φ.trans e⟩
        · exact hB X H K ⟨φ.trans e⟩
        · have : IsSimpleGroup (↥(⊤ : Subgroup Q) ⧸ center ↥(⊤ : Subgroup Q)) := hqt.2.1
          exact hM X H K (↥(⊤ : Subgroup Q) ⧸ center ↥(⊤ : Subgroup Q)) hqt.2.2 ⟨φ⟩ ⟨e⟩
      have := CFSG.RankThree.OddKernel.evenRank_eq_twoLocalOddRank X
      omega
    · obtain ⟨hpair, hnot⟩ := sporadic_residual_of_center e hp hp3 hpZ'
      exact hnot (hres.trivial_of_pair hexc hpair)

end CFSG.RankThree.PartOne.K159
