module

public import CFSG.Permutation.UnitaryThreeRecognition.MainSetup
public import CFSG.Permutation.UnitaryThreeRecognition.AssemblyThree

public section

namespace CFSG.UnitaryThreeRecognition

open MulAction

theorem onan_unitary_three
    {G Ω : Type} [Group G] [Finite G] [IsSimpleGroup G]
    (_hnonab : ∃ x y : G, x * y ≠ y * x) [MulAction G Ω] [Finite Ω]
    (h2 : IsMultiplyPretransitive G Ω 2) (p f : ℕ) (hp : p.Prime) (hpodd : p ≠ 2)
    (hf : 1 ≤ f) (hΩ : Nat.card Ω = (p ^ f) ^ 3 + 1) (α : Ω) (Q : Subgroup G)
    (hQ : Q ≤ stabilizer G α) [hQn : (Q.subgroupOf (stabilizer G α)).Normal]
    (hQcard : Nat.card Q = (p ^ f) ^ 3)
    (hreg : ∀ β γ : Ω, β ≠ α → γ ≠ α → ∃! u : Q, (u : G) • β = γ)
    (hcyc : IsCyclic (stabilizer G α ⧸ Q.subgroupOf (stabilizer G α)))
    (hcard : Nat.card (stabilizer G α ⧸ Q.subgroupOf (stabilizer G α)) =
      ((p ^ f) ^ 2 - 1) / Nat.gcd (p ^ f + 1) 3) :
    CFSG.Assembly.LowTwoRank.StatedClassicalModel G .PSU 3 p f := by
  obtain ⟨b, j, s, S, hTcyc, g, hg⟩ := exists_stdHyp h2 p f hp hpodd hf hΩ α Q hQ hQcard hreg
    hcyc hcard
  rcases (gcd_three_facts (S.hpodd.pow (n := f))).1 with hd | hd
  · exact statedClassicalModel_of_stdHyp_coprime h2 S hd
  · exact statedClassicalModel_of_stdHyp_three h2 S hd hTcyc hg

end CFSG.UnitaryThreeRecognition
