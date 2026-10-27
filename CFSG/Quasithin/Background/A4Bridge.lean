module

public import CFSG.Quasithin.Background.A4Defs
public import CFSG.Quasithin.Background.A1cTransfer

public section

namespace CFSG.Quasithin

open CFSG.Quasithin.A4

variable {G : Type*} [Group G] [Finite G]

theorem oTwoUpper_eq_pResidualOf (X : Subgroup G) : oTwoUpper X = pResidualOf 2 X := by
  apply le_antisymm
  · refine (Subgroup.closure_le _).mpr fun x hx => ?_
    refine ⟨⟨x, hx.1⟩, ?_, rfl⟩
    show (⟨x, hx.1⟩ : X) ∈ pResidual 2 X
    unfold pResidual
    simp only [Subgroup.mem_iInf]
    intro N hN hNk
    obtain ⟨k, hk⟩ := hNk ⟨x, hx.1⟩
    have hord : orderOf (⟨x, hx.1⟩ : X) = orderOf x := Subgroup.orderOf_mk x hx.1
    have hcop : Nat.Coprime (2 ^ k) (orderOf (⟨x, hx.1⟩ : X)) := by
      rw [hord]
      exact Nat.Coprime.pow_left k (Nat.coprime_two_left.mpr hx.2)
    exact (Subgroup.zpowers_le.mpr hk) (A4.mem_zpowers_pow_of_coprime hcop)
  · have hN : ((oTwoUpper X).subgroupOf X).Normal :=
      Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_oTwoUpper X)
    have h1 : pResidual 2 X ≤ (oTwoUpper X).subgroupOf X :=
      pResidual_le (N := (oTwoUpper X).subgroupOf X) fun x => exists_pow_mem_oTwoUpper X x.2
    calc pResidualOf 2 X ≤ ((oTwoUpper X).subgroupOf X).map X.subtype := Subgroup.map_mono h1
      _ = oTwoUpper X := Subgroup.map_subgroupOf_eq_of_le (oTwoUpper_le X)

theorem eq_oTwoUpper_iff_forall_normal (L : Subgroup G) :
    L = oTwoUpper L ↔ ∀ N : Subgroup G, N ≤ L → (N.subgroupOf L).Normal →
      (∀ x ∈ L, ∃ k : ℕ, x ^ 2 ^ k ∈ N) → N = L := by
  constructor
  · intro hL N hNL _ hN
    exact le_antisymm hNL (hL.le.trans (oTwoUpper_le_of_pow_mem hN))
  · intro h
    have := h (oTwoUpper L) (oTwoUpper_le L)
      (Subgroup.normal_subgroupOf_of_le_normalizer (le_normalizer_oTwoUpper L))
      fun x hx => exists_pow_mem_oTwoUpper L hx
    exact this.symm

omit [Finite G] in
theorem VY_eq_quasithinV2 (L : Subgroup G) : VY L = CFSG.Open.quasithinV2 L := rfl

end CFSG.Quasithin
