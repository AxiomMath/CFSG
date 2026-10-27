module

public import CFSG.ThirdParty.QiuzhenCFSG.FeitThompson.BGsection1.Basic

namespace CFSG
end CFSG
open CFSG

open scoped Pointwise

public section

-- Proposition 1.5(b)
theorem CFSG.proposition_1_5_b {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G] (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (π : Set Nat.Primes) :
    ∀ K : Subgroup G, IsPiSubgroup (G := G) π K → IsInvariant A G K →
      ∃ H : Subgroup G, IsHallSubgroup π H ∧ IsInvariant A G H ∧ K ≤ H := by
  intro K hK_pi hK_inv
  exact exists_isHallSubgroup_isInvariant_of_isPiSubgroup
    (G := G) (A := A) hsolv hcoprime π K hK_pi hK_inv

-- Proposition 1.5(c)
theorem CFSG.proposition_1_5_c {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G] (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (π : Set Nat.Primes) :
    ∀ H₁ H₂ : Subgroup G,
      IsHallSubgroup π H₁ →
        IsHallSubgroup π H₂ →
          IsInvariant A G H₁ →
            IsInvariant A G H₂ →
              ∃ g : G, g ∈ fixedPointSubgroup A G ∧ H₂ = H₁.map (MulAut.conj g) := by
  intro H₁ H₂ hHall₁ hHall₂ hInv₁ hInv₂
  exact
    exists_mem_fixedPointSubgroup_eq_map_conj_of_isHallSubgroup_of_isInvariant
      (G := G) (A := A) hsolv hcoprime π H₁ H₂ hHall₁ hHall₂ hInv₁ hInv₂

-- Proposition 1.5(d)
theorem CFSG.proposition_1_5_d {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G] (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (π : Set Nat.Primes) :
    ∀ (H : Subgroup G) [H.Normal] (hHinv : IsInvariant A G H),
      letI : MulDistribMulAction A (G ⧸ H) :=
        quotientMulDistribMulAction (A := A) (G := G) H hHinv
      fixedPointSubgroup A (G ⧸ H) = (fixedPointSubgroup A G).map (QuotientGroup.mk' H) := by
  let _ := π
  intro H _ hHinv
  simpa using
    fixedPointSubgroup_quotient_eq_map_of_solvable_coprime_action
      (G := G) (A := A) hsolv hcoprime (π := π) H hHinv

-- Proposition 1.5(e)
theorem CFSG.proposition_1_5_e {G A : Type*} [Group G] [Finite G] [Group A] [Finite A]
    [MulDistribMulAction A G] (hsolv : Group.IsSolvable G) (hcoprime : Nat.Coprime (Nat.card A) (Nat.card G))
    (π : Set Nat.Primes) :
    ∀ Hπ' : Subgroup G,
      IsHallSubgroup {p | p ∉ π} Hπ' →
        Hπ' ≤ fixedPointSubgroup A G → commutatorAction (A := A) (G := G) ≤ piCore π G := by
  exact
    commutatorAction_le_piCore_of_hall_complement_le_fixedPointSubgroup
      (G := G) (A := A) hsolv hcoprime π


end
