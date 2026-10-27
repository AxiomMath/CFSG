module

public import CFSG.RankThree.OddKernel.SporadicKernelCases

public section

namespace CFSG.RankThree.OddKernel

open CFSG.SectionRank CFSG.Blueprint

variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] {S : Type} [Group S]

theorem sporadic_kernel_restriction_of_cases (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6)
    (hJ4 : NativeSporadic.IsSporadic S .J4 → π.ker = ⊥)
    (hLy : NativeSporadic.IsSporadic S .Ly → ∀ r : ℕ, r.Prime → r ∣ Nat.card π.ker → r = 5)
    (hFi23 : NativeSporadic.IsSporadic S .Fi23 → ∀ r : ℕ, r.Prime → r ∣ Nat.card π.ker → r = 5)
    (hHN : NativeSporadic.IsSporadic S .HN → ∀ r : ℕ, r.Prime → r ∣ Nat.card π.ker → r = 5)
    (hFi24 : NativeSporadic.IsSporadic S .Fi24Prime → ∀ r : ℕ, r.Prime → r ∣ Nat.card π.ker →
      r = 5 ∨ r = 7)
    (hTh : NativeSporadic.IsSporadic S .Th → ∀ r : ℕ, r.Prime → r ∣ Nat.card π.ker →
      r = 5 ∨ r = 7)
    (hB : NativeSporadic.IsSporadic S .B → ∀ r : ℕ, r.Prime → r ∣ Nat.card π.ker →
      r = 5 ∨ r = 7) :
    (∀ s ∈ ({.M11, .M12, .M22, .M23, .M24, .J1, .J2, .J3, .J4, .HS, .He, .Ru} :
        Set TauCeti.SporadicName), NativeSporadic.IsSporadic S s → π.ker = ⊥) ∧
      (∀ s ∈ ({.Co1, .Fi24Prime, .Th, .B} : Set TauCeti.SporadicName),
        NativeSporadic.IsSporadic S s → ∀ r : ℕ, r.Prime → r ∣ Nat.card π.ker → r = 5 ∨ r = 7) ∧
      (∀ s ∈ ({.Co2, .Co3, .Fi22, .Fi23, .McL, .Suz, .HN, .Ly} : Set TauCeti.SporadicName),
        NativeSporadic.IsSporadic S s → ∀ r : ℕ, r.Prime → r ∣ Nat.card π.ker → r = 5) ∧
      (NativeSporadic.IsSporadic S .ONan → ∀ r : ℕ, r.Prime → r ∣ Nat.card π.ker → r = 7) ∧
      ∀ s : TauCeti.SporadicName, s ≠ .M → NativeSporadic.IsSporadic S s → ∀ p : ℕ, p.Prime →
        7 < p → IsPGroup p π.ker → π.ker = ⊥ := by
  have h1 : ∀ s ∈ ({.M11, .M12, .M22, .M23, .M24, .J1, .J2, .J3, .J4, .HS, .He, .Ru} :
      Set TauCeti.SporadicName), NativeSporadic.IsSporadic S s → π.ker = ⊥ := by
    intro s hs hS
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact ker_eq_bot_of_isSporadic_small π hπ hC h6 (Or.inl rfl) hS
    · exact ker_eq_bot_of_isSporadic_M12 π hπ hC h6 hS
    · exact ker_eq_bot_of_isSporadic_small π hπ hC h6 (Or.inr (Or.inl rfl)) hS
    · exact ker_eq_bot_of_isSporadic_small π hπ hC h6 (Or.inr (Or.inr (Or.inl rfl))) hS
    · exact ker_eq_bot_of_isSporadic_M24 π hπ hC h6 hS
    · exact ker_eq_bot_of_isSporadic_small π hπ hC h6 (Or.inr (Or.inr (Or.inr rfl))) hS
    · exact ker_eq_bot_of_isSporadic_J2 π hπ hC h6 hS
    · exact ker_eq_bot_of_isSporadic_J3 π hπ hC h6 hS
    · exact hJ4 hS
    · exact ker_eq_bot_of_isSporadic_HS π hπ hC h6 hS
    · exact ker_eq_bot_of_isSporadic_He π hπ hC h6 hS
    · exact ker_eq_bot_of_isSporadic_Ru π hπ hC h6 hS
  have h2 : ∀ s ∈ ({.Co1, .Fi24Prime, .Th, .B} : Set TauCeti.SporadicName),
      NativeSporadic.IsSporadic S s → ∀ r : ℕ, r.Prime → r ∣ Nat.card π.ker → r = 5 ∨ r = 7 := by
    intro s hs hS r hr hrC
    rcases hs with rfl | rfl | rfl | rfl
    · exact prime_dvd_of_isSporadic_Co1 π hπ hC h6 hS hr hrC
    · exact hFi24 hS r hr hrC
    · exact hTh hS r hr hrC
    · exact hB hS r hr hrC
  have h3 : ∀ s ∈ ({.Co2, .Co3, .Fi22, .Fi23, .McL, .Suz, .HN, .Ly} : Set TauCeti.SporadicName),
      NativeSporadic.IsSporadic S s → ∀ r : ℕ, r.Prime → r ∣ Nat.card π.ker → r = 5 := by
    intro s hs hS r hr hrC
    rcases hs with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl
    · exact prime_dvd_of_isSporadic_Co2 π hπ hC h6 hS hr hrC
    · exact prime_dvd_of_isSporadic_Co3 π hπ hC h6 hS hr hrC
    · exact prime_dvd_of_isSporadic_Fi22 π hπ hC h6 hS hr hrC
    · exact hFi23 hS r hr hrC
    · exact prime_dvd_of_isSporadic_McL π hπ hC h6 hS hr hrC
    · exact prime_dvd_of_isSporadic_Suz π hπ hC h6 hS hr hrC
    · exact hHN hS r hr hrC
    · exact hLy hS r hr hrC
  have h4 : NativeSporadic.IsSporadic S .ONan → ∀ r : ℕ, r.Prime → r ∣ Nat.card π.ker → r = 7 :=
    fun hS _ hr hrC => prime_dvd_of_isSporadic_ON π hπ hC h6 hS hr hrC
  refine ⟨h1, h2, h3, h4, fun s hsM hS p hp hp7 hpk => ?_⟩
  by_contra hne
  have hpC : p ∣ Nat.card π.ker := by
    have : Fact p.Prime := ⟨hp⟩
    have := (Subgroup.nontrivial_iff_ne_bot _).mpr hne
    obtain ⟨k, hk⟩ := hpk.exists_card_eq
    rcases k with _ | k
    · rw [pow_zero] at hk
      exact absurd (Subgroup.card_eq_one.mp hk) hne
    · rw [hk]
      exact dvd_pow_self p k.succ_ne_zero
  have hcases : s ∈ ({.M11, .M12, .M22, .M23, .M24, .J1, .J2, .J3, .J4, .HS, .He, .Ru} :
        Set TauCeti.SporadicName) ∨ s ∈ ({.Co1, .Fi24Prime, .Th, .B} : Set TauCeti.SporadicName) ∨
      s ∈ ({.Co2, .Co3, .Fi22, .Fi23, .McL, .Suz, .HN, .Ly} : Set TauCeti.SporadicName) ∨
      s = .ONan ∨ s = .M := by
    cases s <;> simp
  rcases hcases with h | h | h | h | h
  · exact hne (h1 s h hS)
  · exact absurd (h2 s h hS p hp hpC) (by omega)
  · exact absurd (h3 s h hS p hp hpC) (by omega)
  · subst h
    exact absurd (h4 hS p hp hpC) (by omega)
  · exact hsM h

end CFSG.RankThree.OddKernel
