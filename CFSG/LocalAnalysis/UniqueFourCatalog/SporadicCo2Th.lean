module

public import CFSG.LocalAnalysis.UniqueFourCatalog.Standing4Basic
public import CFSG.LocalAnalysis.UniqueFourCatalog.Glue
public import Certificates.Certificate9419
public import CFSG.LocalAnalysis.AGLEmbedding.KFactProofs.SporCaseThreeThThree
import CFSG.LocalAnalysis.AGLEmbedding.SporCaseThreeDataAux
import CFSG.RankThree.PartOne.CTP.SporadicOrders

public section

namespace CFSG.LocalAnalysis.UniqueFourCatalog

open CFSG.Open CFSG.AGLEmbedding CFSG.Blueprint
open CFSG.Yardstones.Mf4cdcdf2e013 (Standing4)

theorem not_pow_four_dvd_of_primeFactors {N : ℕ} (hN : N ≠ 0) (S : Finset ℕ)
    (hS : N.primeFactors = S) (h : ∀ p ∈ S, p = 2 ∨ p = 3 ∨ ¬ p ^ 4 ∣ N) :
    ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → ¬ r ^ 4 ∣ N := by
  intro r hr hr2 hr3 hdvd
  have hrN : r ∈ N.primeFactors :=
    Nat.mem_primeFactors.2 ⟨hr, (dvd_pow_self r (by norm_num)).trans hdvd, hN⟩
  rw [hS] at hrN
  rcases h r hrN with h1 | h1 | h1
  · exact hr2 h1
  · exact hr3 h1
  · exact h1 hdvd

theorem not_pow_four_dvd_Co2 : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → ¬ r ^ 4 ∣ 42305421312000 := by
  refine not_pow_four_dvd_of_primeFactors (N := 42305421312000) (by norm_num)
    {2, 3, 5, 7, 11, 23} (by norm_num [Nat.primeFactors]) ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem not_pow_four_dvd_Th : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → ¬ r ^ 4 ∣ 90745943887872000 := by
  refine not_pow_four_dvd_of_primeFactors (N := 90745943887872000) (by norm_num)
    {2, 3, 5, 7, 13, 19, 31} (by norm_num [Nat.primeFactors]) ?_
  intro p hp
  simp only [Finset.mem_insert, Finset.mem_singleton] at hp
  rcases hp with rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> norm_num

theorem not_uniqueFour_of_tcGenDatum {G H : Type} [Group G] [Finite G] [Group H] [Finite H]
    (hS : Standing4 G) (e : G ≃* H)
    (h3 : 3 ∈ CFSG.Open.uniqueFourBeta G) (hTC : TCGenDatum H 3) :
    ¬ CFSG.Open.uniqueFourUnique G := by
  have : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  let P : Sylow 3 G := default
  let T : Sylow 3 H := Sylow.mapSurjective (f := e.toMonoidHom) e.surjective P
  have hT : (T : Subgroup H) = (P : Subgroup G).map e.toMonoidHom := Sylow.coe_mapSurjective _ _
  have hcore : GLBWeakCore 3 (T : Subgroup H) = ⊤ := weakCoreOfTC H 3 hTC T
  have hP : (P : Subgroup G) = (T : Subgroup H).map e.symm.toMonoidHom := by
    rw [hT, Subgroup.map_map]
    have : e.symm.toMonoidHom.comp e.toMonoidHom = MonoidHom.id G := by ext x; simp
    rw [this, Subgroup.map_id]
  have hcoreG : GLBWeakCore 3 (P : Subgroup G) = ⊤ :=
    glbWeakCore_eq_top_of_mulEquiv Nat.prime_three e.symm hP hcore
  have hle : GLBWeakCore 3 (P : Subgroup G) ≤ uniqueFourGamma 3 (P : Subgroup G) :=
    CFSG.PreuniquenessRankFour.Helpers.weakCore_le_fullCore 3 _
  rw [hcoreG] at hle
  exact not_uniqueFour_of_gamma_eq_top hS h3 P (top_le_iff.mp hle)

theorem not_uniqueFour_of_Co2
    {G : Type} [Group G] [Finite G] (hS : Standing4 G)
    (e : G ≃* NativeSporadic.Carrier .Co2) : ¬ CFSG.Open.uniqueFourUnique G := by
  have hcard : Nat.card (NativeSporadic.Carrier .Co2) = 42305421312000 :=
    CFSG.Sporadic.Co2.card_Co2
  have h4 : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → ¬ r ^ 4 ∣ Nat.card G := by
    rw [Nat.card_congr e.toEquiv, hcard]
    exact not_pow_four_dvd_Co2
  have h3 : 3 ∈ CFSG.Open.uniqueFourBeta G :=
    CFSG.Yardstones.Mf4cdcdf2e013.three_mem_uniqueFourBeta_of_card hS h4
  have : Finite (NativeSporadic.Carrier .Co2) := Finite.of_equiv G e.toEquiv
  exact not_uniqueFour_of_tcGenDatum hS e h3
    (CFSG.AGLEmbedding.R3.tcGenDatum_of_check (CFSG.SectionRank.spec2 22)
      (D := CFSG.AGLEmbedding.R3.Co2Three.tcSpec) Nat.prime_three
      Certificates.certificate9419.1)

theorem not_uniqueFour_of_Th
    {G : Type} [Group G] [Finite G] (hS : Standing4 G)
    (e : G ≃* NativeSporadic.Carrier .Th) : ¬ CFSG.Open.uniqueFourUnique G := by
  have hcard : Nat.card (NativeSporadic.Carrier .Th) = 90745943887872000 :=
    CFSG.RankThree.PartOne.CTP.card_Th
  have h4 : ∀ r : ℕ, r.Prime → r ≠ 2 → r ≠ 3 → ¬ r ^ 4 ∣ Nat.card G := by
    rw [Nat.card_congr e.toEquiv, hcard]
    exact not_pow_four_dvd_Th
  have h3 : 3 ∈ CFSG.Open.uniqueFourBeta G :=
    CFSG.Yardstones.Mf4cdcdf2e013.three_mem_uniqueFourBeta_of_card hS h4
  have : Finite (NativeSporadic.Carrier .Th) := Finite.of_equiv G e.toEquiv
  exact not_uniqueFour_of_tcGenDatum hS e h3 tcGenDatum_Th_three

end CFSG.LocalAnalysis.UniqueFourCatalog
