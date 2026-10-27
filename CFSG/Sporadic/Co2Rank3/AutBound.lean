module

public import CFSG.Sporadic.Co2Rank3.Graph
public import CFSG.Sporadic.FischerOddCore.RefineSpec

public noncomputable section

namespace CFSG.Sporadic.Co2Rank3

open CFSG.Sporadic.Co2Cert CFSG.Certificates CFSG.Certificates.Native CFSG.Monster.B.Co2
  CFSG.Sporadic.Co2Rank3.Native CFSG.Sporadic.FischerOddCore MulAction

@[expose] def co2Aut :
    Subgroup (Equiv.Perm (Fin 2300)) where
  carrier := {σ | ∀ x y, co2Graph.Adj (σ x) (σ y) ↔ co2Graph.Adj x y}
  one_mem' _ _ := Iff.rfl
  mul_mem' ha hb x y := (ha _ _).trans (hb x y)
  inv_mem' {σ} ha x y := by
    rw [← ha (σ⁻¹ x) (σ⁻¹ y), perm_apply_inv_self, perm_apply_inv_self]

theorem mem_co2Aut
    {σ : Equiv.Perm (Fin 2300)} :
    σ ∈ co2Aut ↔ ∀ x y, co2Graph.Adj (σ x) (σ y) ↔ co2Graph.Adj x y := Iff.rfl

theorem co2P_le_co2Aut :
    co2P ≤ co2Aut := fun _ hg _ _ => co2Graph_adj_smul hg

theorem nbrInv_of_mem_co2Aut
    {σ : Equiv.Perm (Fin 2300)} (hσ : σ ∈ co2Aut) :
    NbrInv co2Nbr σ := by
  intro x y
  rw [co2Nbr_adj, co2Nbr_adj]
  exact (hσ x y).symm

@[expose] def co2BasePt (s : ℕ) : Fin 2300 :=
  ⟨refineBase.getD s 0 % 2300, Nat.mod_lt _ (by norm_num)⟩

@[expose] def co2AutStab
    (s : ℕ) : Subgroup co2Aut := stabChain co2BasePt s

theorem refineBase_lt {v : ℕ} (hv : v ∈ refineBase) : v < 2300 := by
  simp only [refineBase, List.mem_cons, List.not_mem_nil, or_false] at hv
  omega

theorem co2Aut_bounds :
    (∀ s < 6, (orbit (co2AutStab s) (co2BasePt s)).ncard ≤ refineBounds.getD s 0) ∧
    co2AutStab 6 = ⊥ ∧ Nat.card co2Aut ≤ refineBounds.prod :=
  card_le_of_boundsOK (K := co2Aut) co2Nbr_facts.point rep_idA
    (fun _ hσ => ⟨nbrInv_of_mem_co2Aut hσ, by rw [mul_one, one_mul]⟩) (by norm_num)
    (fun _ hx => refineBase_lt hx) co2Rank3Facts.bounds

theorem card_co2Aut_le :
    Nat.card co2Aut ≤ 42305421312000 :=
  co2Aut_bounds.2.2.trans (le_of_eq (by norm_num [refineBounds]))

theorem co2Aut_eq :
    co2Aut = co2P :=
  (Subgroup.eq_of_le_of_card_ge co2P_le_co2Aut (by rw [card_co2P]; exact card_co2Aut_le)).symm

theorem card_co2Aut :

    Nat.card co2Aut = 42305421312000 := by rw [co2Aut_eq, card_co2P]

end CFSG.Sporadic.Co2Rank3
