module

public import CFSG.RankThree.OddKernel.SporadicKernelRestriction
public import CFSG.Monster.Existence.BabyOrder

public section

namespace CFSG.RankThree.OddKernel

open CFSG.SectionRank CFSG.Blueprint

theorem card_B_eq : Nat.card NativeSporadic.B = 4154781481226426191177580544000000 := by
  rw [CFSG.Monster.Existence.card_nativeB]
  decide

variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] {S : Type} [Group S]

theorem twenty_five_sporadic_central_prime_to_six_kernel_restriction (π : E →* S)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (h6 : Nat.Coprime (Nat.card π.ker) 6) :
    (∀ s ∈ ({.M11, .M12, .M22, .M23, .M24, .J1, .J2, .J3, .J4, .HS, .He, .Ru} :
        Set TauCeti.SporadicName), NativeSporadic.IsSporadic S s → π.ker = ⊥) ∧
      (∀ s ∈ ({.Co1, .Fi24Prime, .Th, .B} : Set TauCeti.SporadicName),
        NativeSporadic.IsSporadic S s → ∀ r : ℕ, r.Prime → r ∣ Nat.card π.ker → r = 5 ∨ r = 7) ∧
      (∀ s ∈ ({.Co2, .Co3, .Fi22, .Fi23, .McL, .Suz, .HN, .Ly} : Set TauCeti.SporadicName),
        NativeSporadic.IsSporadic S s → ∀ r : ℕ, r.Prime → r ∣ Nat.card π.ker → r = 5) ∧
      (NativeSporadic.IsSporadic S .ONan → ∀ r : ℕ, r.Prime → r ∣ Nat.card π.ker → r = 7) ∧
      ∀ s : TauCeti.SporadicName, s ≠ .M → NativeSporadic.IsSporadic S s → ∀ p : ℕ, p.Prime →
        7 < p → IsPGroup p π.ker → π.ker = ⊥ :=
  twenty_five_sporadic_central_prime_to_six_kernel_restriction_of_card_B card_B_eq π hπ hC h6

theorem perfect_central_large_prime_extension_sporadic_ker_eq_bot (π : E →* S)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E) {p : ℕ} (hp : p.Prime)
    (hp7 : 7 < p) (hpk : IsPGroup p π.ker) {s : TauCeti.SporadicName} (hs : s ≠ .M)
    (hS : NativeSporadic.IsSporadic S s) : π.ker = ⊥ := by
  have : Fact p.Prime := ⟨hp⟩
  have h6 : Nat.Coprime (Nat.card π.ker) 6 := by
    obtain ⟨k, hk⟩ := hpk.exists_card_eq
    rw [hk]
    refine Nat.Coprime.pow_left _ ((Nat.Prime.coprime_iff_not_dvd hp).mpr fun h => ?_)
    have := Nat.le_of_dvd (by norm_num) h
    omega
  exact (twenty_five_sporadic_central_prime_to_six_kernel_restriction π hπ hC h6).2.2.2.2 s hs hS
    p hp hp7 hpk

end CFSG.RankThree.OddKernel
