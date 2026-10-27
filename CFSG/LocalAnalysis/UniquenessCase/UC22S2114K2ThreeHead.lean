module

public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114E3Defs
public import CFSG.LocalAnalysis.UniquenessCase.PartTwo.R76Sig
public import CFSG.LocalAnalysis.UniquenessCase.UC6S846e
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2N
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2Five
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2Three
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114K2ThreeX
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114D4Three
import CFSG.LocalAnalysis.UniquenessCase.UC22S2114a
public import CFSG.LocalAnalysis.UniquenessCase.UC22S2114Defs

public section

namespace CFSG.LocalAnalysis.UniquenessCase.UC22

open CFSG.Open Subgroup

variable {G : Type} [Group G] [Finite G]


theorem s21_14K2_of_s21_14K2T (hGA : GriessAllModelsStatement) {D : Data G} {Ch : Choice2011 G}
    (hSg : UC6S846.SigmaStd D) (h614 : UC6.R6_14 D) (h76 : F07.R76Sig D)
    (hD4T : S21_14D4T D Ch) (hK2T : S21_14K2T D Ch) : S21_14K2 D Ch := by
  intro hH c L hL hX hpow hcase hk2 hn3 hBL hfaith
  by_cases h36 : (∃ f : ℕ, Is3D4 (BarInf L) f) ∧ (c.n = 3 ∨ c.n = 6)
  · obtain ⟨⟨f, hD⟩, hn⟩ := h36
    by_cases h2 : ∀ p ∈ D.sig, 2 ≤ CFSG.Open.pRank p L
    · exact hD4T hH c L hL hX hpow ⟨f, hD⟩ hn
        (fun h1 => absurd (h1.symm.trans hk2) (by norm_num)) hBL hfaith h2
    · simp only [not_forall, not_le] at h2
      obtain ⟨p, hp, hpL⟩ := h2
      exact (uc22s2114_false_of_is3D4_of_three_dvd_three hSg h614 h76 hH c hL hD
        (hpow f (Or.inr (Or.inr (Or.inr (Or.inl hD))))) (by omega) hp (by omega)).elim
  have key : ∀ f : ℕ, LieRankTwoEven (BarInf L) f → 4 ∣ c.n ∧ IsPowTwo f := by
    intro f hRT
    have hf := hpow f hRT
    rcases uc22s2114_four_dvd_n_of_lieRankTwo c hL hRT hf hBL hfaith hn3 with h | ⟨hD, hn⟩
    · exact ⟨h, hf⟩
    · exact absurd ⟨⟨f, hD⟩, hn⟩ h36
  have hfive : 4 ∣ c.n → (∀ p ∈ D.sig, p ∣ 5) → False := fun hn h5 => by
    obtain ⟨p, hp⟩ := hSg.nonempty
    have hp5 : p = 5 :=
      (Nat.prime_dvd_prime_iff_eq (D.sig_prime p hp).1 Nat.prime_five).1 (h5 p hp)
    exact uc22s2114_not_mem_sig hSg (UC6S846.not_solvable_of_mem_calC hL) hH c Nat.prime_five
      ((by norm_num : 5 ∣ 2 ^ 4 - 1).trans (Nat.pow_sub_one_dvd_pow_sub_one 2 hn)) (hp5 ▸ hp)
  have h2 : ∀ k : ℕ, 2 ≤ 2 ^ k → 2 ∣ 2 ^ k := fun k hk =>
    dvd_pow_self 2 (by rintro rfl; norm_num at hk)
  rcases hcase with ⟨f, hf2, hSp | hG2 | hU4 | hU5⟩ | ⟨f, hD⟩
  · obtain ⟨hn, k, rfl⟩ := key _ (Or.inr (Or.inl hSp))
    by_cases hall : ∀ p ∈ D.sig, p ∣ 2 ^ 2 ^ k + 1
    · rcases k with _ | _ | k
      · norm_num at hf2
      · exact (hfive hn fun p hp => by simpa using hall p hp).elim
      · exact hK2T hH c L hL hX hpow ⟨_, ⟨2 ^ k, by ring⟩, Or.inl hSp,
          fun p hp => Or.inl (hall p hp)⟩ hk2 hn3 hn hBL hfaith
    · simp only [not_forall] at hall
      obtain ⟨p, hp, hpf⟩ := hall
      exact (uc22s2114_false_of_isSp4_three hGA hSg h614 h76 hH c hL hSp (h2 k hf2)
        ((dvd_mul_right 2 2).trans hn) hp hpf).elim
  · obtain ⟨hn, k, rfl⟩ := key _ (Or.inr (Or.inr (Or.inl hG2)))
    rcases k with _ | _ | k
    · norm_num at hf2
    · exact (uc22s2114_false_of_isG2_four c hL (by simpa using hG2) hn hBL hfaith).elim
    · by_cases hall : ∀ p ∈ D.sig, p ∣ 2 ^ 2 ^ (k + 1 + 1) + 1
      · exact hK2T hH c L hL hX hpow ⟨_, ⟨2 ^ k, by ring⟩, Or.inr (Or.inl hG2),
          fun p hp => Or.inl (hall p hp)⟩ hk2 hn3 hn hBL hfaith
      · simp only [not_forall] at hall
        obtain ⟨p, hp, hpf⟩ := hall
        exact (uc22s2114_false_of_isG2_three hGA hSg h614 h76 hH c hL hG2 ⟨2 ^ k, by ring⟩ hn
          hp hpf).elim
  · obtain ⟨hn, k, rfl⟩ := key _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inl hU4))))))
    by_cases hall : ∀ p ∈ D.sig, p ∣ 2 ^ 2 ^ k + 1
    · rcases k with _ | _ | k
      · norm_num at hf2
      · exact (hfive hn fun p hp => by simpa using hall p hp).elim
      · exact hK2T hH c L hL hX hpow ⟨_, ⟨2 ^ k, by ring⟩, Or.inr (Or.inr (Or.inl hU4)),
          fun p hp => Or.inl (hall p hp)⟩ hk2 hn3 hn hBL hfaith
    · simp only [not_forall] at hall
      obtain ⟨p, hp, hpf⟩ := hall
      exact (uc22s2114_false_of_isU4_three hGA hSg h614 h76 hH c hL hU4 (h2 k hf2)
        ((dvd_mul_right 2 2).trans hn) hp hpf).elim
  · obtain ⟨hn, k, rfl⟩ := key _ (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr (Or.inr hU5))))))
    exact (uc22s2114_false_of_isU5_three hGA hSg h614 h76 hH c hL hU5 (h2 k hf2) hn).elim
  · obtain ⟨hn, k, rfl⟩ := key _ (Or.inr (Or.inr (Or.inr (Or.inl hD))))
    rcases k with _ | _ | k
    · exact (uc22s2114_false_of_is3D4_two c hL (by simpa using hD) hn hBL hfaith).elim
    · exact (uc22s2114_false_of_is3D4_four c hL (by simpa using hD) hn hBL hfaith).elim
    · by_cases hall : ∀ p ∈ D.sig, p ∣ 2 ^ 2 ^ (k + 1 + 1) + 1 ∨
          p ∣ 2 ^ (2 * 2 ^ (k + 1 + 1)) - 2 ^ 2 ^ (k + 1 + 1) + 1
      · exact hK2T hH c L hL hX hpow ⟨_, ⟨2 ^ k, by ring⟩, Or.inr (Or.inr (Or.inr hD)),
          fun p hp => (hall p hp).imp_right fun h => ⟨hD, h⟩⟩ hk2 hn3 hn hBL hfaith
      · simp only [not_forall, not_or] at hall
        obtain ⟨p, hp, hpl, hpm⟩ := hall
        obtain ⟨hpp, hp2⟩ := D.sig_prime p hp
        exact (uc22s2114_false_of_is3D4_three hSg h614 h76 hH c hL hD ⟨2 ^ k, by ring⟩ hn hp hpl
          hpm fun h => hp2 ((Nat.prime_dvd_prime_iff_eq hpp Nat.prime_two).1
            (hpp.dvd_of_dvd_pow h))).elim

end CFSG.LocalAnalysis.UniquenessCase.UC22
