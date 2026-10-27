module

public import CFSG.RankThree.OddKernel.SporadicKernelAssembly
public import CFSG.RankThree.OddKernel.SporadicKernelJ4
public import CFSG.RankThree.OddKernel.SporadicKernelLy
public import CFSG.RankThree.OddKernel.SporadicKernelFi23
public import CFSG.RankThree.OddKernel.SporadicKernelHN
public import CFSG.RankThree.OddKernel.SporadicKernelFi24
public import CFSG.RankThree.OddKernel.SporadicKernelTh

public section

namespace CFSG.RankThree.OddKernel

open CFSG.SectionRank CFSG.Blueprint

variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] {S : Type} [Group S]

theorem prime_dvd_of_isSporadic_B_of_card
    (hB : Nat.card NativeSporadic.B = 4154781481226426191177580544000000) (π : E →* S)
    (hπ : Function.Surjective π) (hC : π.ker ≤ Subgroup.center E)
    (h6 : Nat.Coprime (Nat.card π.ker) 6) (h : NativeSporadic.IsSporadic S .B) {r : ℕ}
    (hr : r.Prime) (hrC : r ∣ Nat.card π.ker) : r = 5 ∨ r = 7 := by
  have : Finite S := Finite.of_surjective π hπ
  obtain ⟨e⟩ := h
  exact prime_mem_of_card_eq π hπ hC h6 ((Nat.card_congr e.toEquiv).trans hB)
    (fun _ hr h2 h3 h => sq_primes_B hr h2 h3 h) hr hrC

theorem twenty_five_sporadic_central_prime_to_six_kernel_restriction_of_card_B
    (hB : Nat.card NativeSporadic.B = 4154781481226426191177580544000000) (π : E →* S)
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
  sporadic_kernel_restriction_of_cases π hπ hC h6
    (ker_eq_bot_of_isSporadic_J4 π hπ hC h6)
    (fun h _ hr hrC => prime_dvd_of_isSporadic_Ly π hπ hC h6 h hr hrC)
    (fun h _ hr hrC => prime_dvd_of_isSporadic_Fi23 π hπ hC h6 h hr hrC)
    (fun h _ hr hrC => prime_dvd_of_isSporadic_HN π hπ hC h6 h hr hrC)
    (fun h _ hr hrC => prime_dvd_of_isSporadic_Fi24prime π hπ hC h6 h hr hrC)
    (fun h _ hr hrC => prime_dvd_of_isSporadic_Th π hπ hC h6 h hr hrC)
    (fun h _ hr hrC => prime_dvd_of_isSporadic_B_of_card hB π hπ hC h6 h hr hrC)

end CFSG.RankThree.OddKernel
