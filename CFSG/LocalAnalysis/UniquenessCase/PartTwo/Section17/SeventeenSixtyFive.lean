module

public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.Section17.HypSeventeenFiftyFour

public section

namespace CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17

open Subgroup CFSG.Open CFSG.LocalAnalysis.UniquenessCase.UC22
open CFSG.Blueprint (LieModel)

variable {G : Type} [Group G] [Finite G]

theorem calL0Star_nonempty_of_exists {D : Data G} {p : ℕ}
    (h : ∃ j : ℕ, 1 ≤ j ∧ j ≤ 5 ∧ (calLjStar D p j).Nonempty) :
    (calL0Star D p).Nonempty := by
  classical
  have hS : {j : ℕ | 1 ≤ j ∧ j ≤ 5 ∧ (calLjStar D p j).Nonempty}.Nonempty := h
  have hmem : sInf {j : ℕ | 1 ≤ j ∧ j ≤ 5 ∧ (calLjStar D p j).Nonempty} ∈
      {j : ℕ | 1 ≤ j ∧ j ≤ 5 ∧ (calLjStar D p j).Nonempty} := Nat.sInf_mem hS
  unfold calL0Star jM
  exact hmem.2.2

theorem seventeen_sixtyfive_of_hyp1754 (D : Data G)
    {V₀ V : Subgroup G} (h641 : R17_64_1At D V₀ V) (h642 : R17_64_2At D V₀ V)
    (h643 : R17_64_3At D V₀ V) :
    ∀ p ∈ D.sig, Hyp1754 D p → (calL0Star D p).Nonempty := by
  intro p hp h54
  have hp_prime : p.Prime := (D.sig_prime p hp).1
  have hH : Hinf D.M = Lp D p := h641 p h54
  obtain ⟨n, hn⟩ := h642 p h54
  obtain ⟨hnpow, hncong⟩ := h643 p h54 n hn
  have hp_dvd : p ∣ 2 ^ n + 1 := UC22.uc22p22r_dvd_succ hncong
  obtain ⟨K, -, hKmem, -, hK2, -, -⟩ := exists_two_calC_of_p1642 hn hH
  have hpK : p ∣ Nat.card K := by
    have hpd : p ∣ Nat.card (Bar2 K) := dvd_card_bar2_of_isL2 hK2 hp_dvd
    rw [Subgroup.card_eq_card_quotient_mul_card_subgroup (CFSG.pCore 2 ↥K)]
    exact hpd.mul_right _
  have hpPi : p ∈ piSet K := ⟨hp_prime, hpK⟩
  have hXmem : conjClosure D.M K ∈ calLpStar D p := ⟨K, ⟨hKmem, hpPi⟩, rfl⟩
  have hnorm : (K.subgroupOf D.M).Normal := (h54.2 K hKmem).1
  have hXeq : conjClosure D.M K = K := uc22p2214_conjClosure_eq_of_normal hKmem.1.le hnorm
  have hX2 : IsL2 (Bar2 (conjClosure D.M K)) n := by rw [hXeq]; exact hK2
  obtain ⟨k, hk⟩ := hnpow
  by_cases hAlt : IsAlt (Bar2 (conjClosure D.M K)) 5
  · exact calL0Star_nonempty_of_exists
      ⟨5, by norm_num, by norm_num, ⟨_, ⟨hXmem, hAlt⟩⟩⟩
  · exact calL0Star_nonempty_of_exists
      ⟨4, by norm_num, by norm_num,
        ⟨_, ⟨hXmem, ⟨k, by rw [← hk]; exact Or.inl hX2⟩, hAlt⟩⟩⟩

theorem seventeen_sixtyfive
    (D : Data G) {V₀ V : Subgroup G}
    (h42 : R17_42At D V₀ V) (h641 : R17_64_1At D V₀ V) (h642 : R17_64_2At D V₀ V)
    (h643 : R17_64_3At D V₀ V) : R17_65At D V₀ V := by
  intro p hp
  by_cases h54 : Hyp1754 D p
  · exact seventeen_sixtyfive_of_hyp1754 D h641 h642 h643 p hp h54
  · have hnot : ¬ ∀ L ∈ calC D.M,
        (L.subgroupOf D.M).Normal ∧
          (F08.Thin8 L ∨ (∃ n : ℕ, IsU3 (Bar2 L) n) ∨ IsL3 (Bar2 L) 2) := by
      intro hgood
      exact h54 ⟨hp, hgood⟩
    have hex : ∃ L, L ∈ calC D.M ∧
        ¬ ((L.subgroupOf D.M).Normal ∧
          (F08.Thin8 L ∨ (∃ n : ℕ, IsU3 (Bar2 L) n) ∨ IsL3 (Bar2 L) 2)) := by
      by_contra h
      apply hnot
      intro L hL
      by_contra hP
      exact h ⟨L, hL, hP⟩
    obtain ⟨L, hL, hbad⟩ := hex
    rcases hyp1754_clause_or_mem_calL123Star D h42 hp hL with hgood | hX1 | hX2 | hX3
    · exact absurd hgood hbad
    · exact calL0Star_nonempty_of_exists
        ⟨1, by norm_num, by norm_num, ⟨_, by simpa [calLjStar] using hX1⟩⟩
    · exact calL0Star_nonempty_of_exists
        ⟨2, by norm_num, by norm_num, ⟨_, by simpa [calLjStar] using hX2⟩⟩
    · exact calL0Star_nonempty_of_exists
        ⟨3, by norm_num, by norm_num, ⟨_, by simpa [calLjStar] using hX3⟩⟩

end CFSG.LocalAnalysis.UniquenessCase.PartTwo.S17
