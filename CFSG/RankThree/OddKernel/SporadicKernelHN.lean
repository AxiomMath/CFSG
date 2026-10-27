module

public import CFSG.Sporadic.HN
public import CFSG.RankThree.OddKernel.SporadicKernelTools

public section

namespace CFSG.RankThree.OddKernel

open CFSG.SectionRank CFSG.Blueprint

variable {E : Type*} [Group E] [Finite E] [Group.IsPerfect E] {S : Type} [Group S]

theorem prime_dvd_of_isSporadic_HN (π : E →* S) (hπ : Function.Surjective π)
    (hC : π.ker ≤ Subgroup.center E) (h6 : Nat.Coprime (Nat.card π.ker) 6)
    (h : NativeSporadic.IsSporadic S .HN) {r : ℕ} (hr : r.Prime) (hrC : r ∣ Nat.card π.ker) :
    r = 5 := by
  have : Finite S := Finite.of_surjective π hπ
  obtain ⟨e⟩ := h
  exact prime_mem_of_card_eq π hπ hC h6 ((Nat.card_congr e.toEquiv).trans
    CFSG.Sporadic.HN.card_HN) (fun _ hr h2 h3 h => sq_primes_HN hr h2 h3 h) hr hrC

end CFSG.RankThree.OddKernel
