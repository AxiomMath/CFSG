module

public import CFSG.RankThree.PartTwo.KFacts.KS166J2A5Three
import CFSG.RankThree.PartTwo.KFacts.KS166J2A5Core
import CFSG.LocalAnalysis.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.J2
public import CFSG.RankThree.PartTwo.Sec4.Sporadic.J2Base

public section

namespace CFSG.RankThree.PartTwo.KFacts.KS166

open Subgroup CFSG.RankThree.PartTwo.Sec4.Sporadic.J2 CFSG.ComponentClassification.J2Cover

theorem ks166J2A5Three :
    KFacts.KS166J2A5Three := by
  intro X _ _ hX K hKp hKA E hEK hE3 hE9 x hxE hxS
  rcases hxS with ⟨S, hxS, hSC⟩
  by_cases hx1 : x = 1
  · rw [hx1]
    exact Subgroup.one_mem _
  obtain ⟨ψ, hψE, _, hKZ⟩ := exists_frame hX hKp hKA hEK hE9
  haveI : Fact (Nat.Prime 3) := ⟨Nat.prime_three⟩
  have hfac3 : (604800 : ℕ).factorization 3 = 3 := by
    rw [Nat.factorization_def _ Nat.prime_three]
    decide +kernel
  have hS27 : Nat.card (S : Subgroup X) = 27 := by
    rw [Sylow.card_eq_multiplicity,
      CFSG.RankThree.PartTwo.KFacts.KS14.card_eq_of_j2 hX, hfac3]
    norm_num
  have hdvdC : 27 ∣ Nat.card (Subgroup.centralizer ({x} : Set X)) := by
    rw [← hS27]
    exact Subgroup.card_dvd_of_le hSC
  have hψxC : Nat.card (Subgroup.centralizer ({ψ x} : Set GJ)) =
      Nat.card (Subgroup.centralizer ({x} : Set X)) :=
    CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.card_centralizer_singleton_mulEquiv
      ψ x
  have h27 : 27 ∣ Nat.card (Subgroup.centralizer ({ψ x} : Set GJ)) := by
    rw [hψxC]
    exact hdvdC
  have hψxE : ψ x ∈ E0 := by
    rw [← hψE]
    exact Subgroup.mem_map_of_mem ψ.toMonoidHom hxE
  have hψx1 : ψ x ≠ 1 := by
    intro h
    apply hx1
    apply ψ.injective
    rw [h, map_one]
  rcases E0_elt_pow hψxE hψx1 with ⟨n, hn⟩ | ⟨k, n, hn⟩
  · have hψx3 : (ψ x) ^ 3 = 1 := by
      rw [← map_pow, hE3 x hxE, map_one]
    have hCeq : Subgroup.centralizer ({ψ x} : Set GJ) =
        Subgroup.centralizer ({zJ} : Set GJ) :=
      CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.centralizer_eq_of_pow hn hψx3
        zJ_ne_one
    rw [Subgroup.mem_centralizer_iff]
    intro k hk
    have hkZ : ψ k ∈ Subgroup.centralizer ({zJ} : Set GJ) :=
      hKZ (Subgroup.mem_map_of_mem ψ.toMonoidHom hk)
    have hkC : ψ k ∈ Subgroup.centralizer ({ψ x} : Set GJ) := by
      rw [hCeq]
      exact hkZ
    have hcomm : ψ k * ψ x = ψ x * ψ k :=
      Subgroup.mem_centralizer_singleton_iff.mp hkC
    apply ψ.injective
    rw [map_mul, map_mul]
    exact hcomm
  · have hle : Subgroup.centralizer ({ψ x} : Set GJ) ≤
        Subgroup.centralizer ({aJ k} : Set GJ) :=
      CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.centralizer_le_of_pow hn
    have h36 : Nat.card (Subgroup.centralizer ({ψ x} : Set GJ)) ∣ 36 := by
      have h := Subgroup.card_dvd_of_le hle
      rwa [CFSG.AGLEmbeddingD2.Wilson.MaximalityAmbient.KF148Sig.card_centralizer_aJ k] at h
    exact absurd (h27.trans h36) (by norm_num)

end CFSG.RankThree.PartTwo.KFacts.KS166
