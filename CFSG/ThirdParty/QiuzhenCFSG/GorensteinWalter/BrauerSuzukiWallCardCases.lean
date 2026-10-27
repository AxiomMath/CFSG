module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.BrauerSuzukiWallDefs

namespace CFSG
end CFSG
open CFSG

/-!
# Cardinality cases for the Brauer--Suzuki--Wall subgroup

The distinguished involution belongs to `K`, so `|K|` is a positive even
integer.  This isolates the two small source cases from the character-theory
range `4 < |K|`.
-/

namespace CFSG.GorensteinWalter

universe u

/-- The subgroup `K` in a Brauer--Suzuki--Wall configuration has order `2`,
order `4`, or order strictly greater than `4`. -/
public theorem BrauerSuzukiWallHypotheses.card_K_cases
    {G : Type u} [Group G] [Finite G]
    (h : BrauerSuzukiWallHypotheses G) :
    Nat.card h.K = 2 ∨ Nat.card h.K = 4 ∨ 4 < Nat.card h.K := by
  let tK : h.K := ⟨h.t, h.t_mem_K⟩
  have htKne : tK ≠ 1 := by
    intro htKone
    exact h.t_involution.1 (congrArg Subtype.val htKone)
  have htKsq : tK ^ 2 = 1 := by
    apply Subtype.ext
    exact h.t_involution.2
  have htKorder : orderOf tK = 2 :=
    orderOf_eq_prime htKsq htKne
  have htwo : 2 ∣ Nat.card h.K := by
    rw [← htKorder]
    exact orderOf_dvd_natCard tK
  rcases htwo with ⟨n, hn⟩
  have hnpos : 0 < n := by
    have hKpos : 0 < Nat.card h.K := Nat.card_pos
    omega
  rcases n with _ | _ | n
  · omega
  · exact Or.inl (by omega)
  · rcases n with _ | n
    · exact Or.inr (Or.inl (by omega))
    · exact Or.inr (Or.inr (by omega))

end CFSG.GorensteinWalter
