module

public import CFSG.Sporadic.Fi24.Simple
public import CFSG.RankThree.OddKernel.SporadicKernelTools

public section

namespace CFSG.RankThree.OddKernel

open CFSG.SectionRank CFSG.Blueprint

variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] {S : Type} [Group S]

theorem prime_dvd_of_isSporadic_Fi24prime (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6)
    (h : NativeSporadic.IsSporadic S .Fi24Prime) {r : ℕ} (hr : r.Prime)
    (hrC : r ∣ Nat.card π.ker) : r = 5 ∨ r = 7 := by
  have : Finite S := Finite.of_surjective π hπ
  obtain ⟨e⟩ := h
  exact prime_mem_of_card_eq π hπ hC h6 ((Nat.card_congr e.toEquiv).trans
    CFSG.Sporadic.Fi24.card_Fi24prime) (fun _ hr h2 h3 h => sq_primes_Fi24prime hr h2 h3 h)
    hr hrC

end CFSG.RankThree.OddKernel
