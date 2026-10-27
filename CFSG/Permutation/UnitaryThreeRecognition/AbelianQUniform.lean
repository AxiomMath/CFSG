module

public import CFSG.Permutation.UnitaryThreeRecognition.AbelianQFive
public import CFSG.Permutation.UnitaryThreeRecognition.AbelianQFiveCert
public import CFSG.Permutation.UnitaryThreeRecognition.AbelianQMain

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

variable {G Ω : Type*} [Group G] [MulAction G Ω] {Q : Subgroup G} {a b : Ω} {j s : G}
  {p f d : ℕ}

namespace StdHyp

theorem false_of_abelian_five
    (S : StdHyp G Q a b j s p f 3) [Finite G] [Finite Ω]
    (h5 : p ^ f = 5) (hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x)
    (hcyc : IsCyclic (pairStab G a b)) : False := by
  obtain ⟨ν, α, β, m, τ, hν, hA4, hm, hτ⟩ := S.exists_validTau_of_abelian h5 hQab hcyc
  exact AbelianQFive.not_validTau ν α β m hν hA4 hm τ hτ

theorem exists_not_commute
    (S : StdHyp G Q a b j s p f d) [Finite G] [Finite Ω]
    (hd : d = Nat.gcd (p ^ f + 1) 3) (hcyc : IsCyclic (pairStab G a b)) :
    ∃ x ∈ Q, ∃ y ∈ Q, x * y ≠ y * x := by
  by_cases h5 : p ^ f = 5
  · by_contra hcon
    have hQab : ∀ x ∈ Q, ∀ y ∈ Q, x * y = y * x := by
      intro x hx y hy
      by_contra hxy
      exact hcon ⟨x, hx, y, hy, hxy⟩
    have hd3 : d = 3 := by rw [hd, h5]; rfl
    subst hd3
    exact S.false_of_abelian_five h5 hQab hcyc
  · exact AbelianQ.exists_not_commute_of_ne_five S.root S.hb S.htwo S.hfaith S.hcomm S.hj S.hj2
      S.hj1 S.hsq S.hpp S.hp S.hf S.hpodd hd S.hQcard S.hΩcard S.hTcard S.hsa S.hs2 h5

end StdHyp

end CFSG.UnitaryThreeRecognition
