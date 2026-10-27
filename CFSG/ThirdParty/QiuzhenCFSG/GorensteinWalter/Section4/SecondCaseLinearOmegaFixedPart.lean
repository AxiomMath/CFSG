module

public import CFSG.ThirdParty.QiuzhenCFSG.GorensteinWalter.Section4.SecondCaseLinearEquationEightDefs
import Mathlib.Tactic

namespace CFSG
end CFSG
open CFSG

noncomputable section
namespace CFSG.GorensteinWalter

universe u

/-- In the cyclic fixed factor, the elements of `p`-power one are exactly
`P`. -/
public theorem secondCase_linear_omega_F_order_p_eq_P
    {G : Type u} [Group G] [Finite G]
    (c : CentralizerSetup G) (w : SecondCaseWitness c)
    (d : SecondCaseComponentData w)
    (od : SecondCaseLinearOmegaData c w d) :
    {x : G | x ∈ od.F ∧ x ^ od.p = 1} = (od.P : Set G) := by
  classical
  let S : Set G := {x : G | x ∈ od.F ∧ x ^ od.p = 1}
  let : Fintype (↥od.F) := Fintype.ofFinite (↥od.F)
  let : IsCyclic (↥od.F) := od.F_cyclic
  have hp_pos : 0 < od.p := od.hp_prime.pos
  have hPsubS : (od.P : Set G) ⊆ S := by
    intro x hx
    exact ⟨od.P_le_F hx,
      (orderOf_dvd_iff_pow_eq_one (x := x) (n := od.p)).mp (by
        simpa [od.P_card] using (Subgroup.orderOf_dvd_natCard od.P hx))⟩
  have hScard : Nat.card {x : G // x ∈ S} = od.p := by
    apply le_antisymm
    · let e : {x : G // x ∈ S} ≃ {a : (↥od.F) // a ^ od.p = 1} :=
        { toFun := fun x => ⟨⟨x.1, x.2.1⟩, by
            apply Subtype.ext
            simpa using x.2.2⟩
          invFun := fun a => ⟨(a.1 : G), ⟨a.1.2, by
            exact congrArg Subtype.val a.2⟩⟩
          left_inv := by intro x; rfl
          right_inv := by intro a; rfl }
      calc
        Nat.card {x : G // x ∈ S} = Nat.card {a : (↥od.F) // a ^ od.p = 1} := Nat.card_congr e
        _ = Fintype.card {a : (↥od.F) // a ^ od.p = 1} := by rw [Nat.card_eq_fintype_card]
        _ ≤ od.p := by
          simpa [Fintype.card_subtype] using
            (IsCyclic.card_pow_eq_one_le (α := (↥od.F)) (n := od.p) hp_pos)
    · have hle : Nat.card od.P ≤ Nat.card {x : G // x ∈ S} :=
        Nat.card_le_card_of_injective (fun x : od.P => ⟨(x : G), hPsubS x.2⟩) (by
          intro a b h
          simpa using congrArg Subtype.val h)
      simpa [od.P_card] using hle
  have hcard : Nat.card {x : G // x ∈ S} ≤ Nat.card {x : G // x ∈ (od.P : Set G)} := by
    exact le_of_eq (by
      change Nat.card {x : G // x ∈ S} = Nat.card (↥od.P)
      rw [hScard, od.P_card])
  let : Fintype (↥od.P) := Fintype.ofFinite (↥od.P)
  exact (Set.eq_of_subset_of_card_le hPsubS (by
    rw [← Nat.card_eq_fintype_card, ← Nat.card_eq_fintype_card]
    exact hcard)).symm

end CFSG.GorensteinWalter
