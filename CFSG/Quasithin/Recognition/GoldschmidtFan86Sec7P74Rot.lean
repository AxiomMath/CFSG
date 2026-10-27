module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Sec7P74Cen2

public section

namespace CFSG.Quasithin.Fan86

namespace P74

open SimpleGraph CFSG.Quasithin.F6.GoldAmL3T

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem zpow_smul_of_smul_eq {x : G} {α : V} (hxα : x • α = α) (n : ℤ) : (x ^ n) • α = α := by
  have hxiα : x⁻¹ • α = α := by rw [inv_smul_eq_iff]; exact hxα.symm
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih => rw [zpow_add_one, mul_smul, hxα, ih]
  | pred i ih => rw [zpow_sub_one, mul_smul, hxiα, ih]

theorem exists_zpow_smul_eq (F : FanTree Γ G) (h65 : Fan65 F) {α : V} (hα : valence Γ α = 5)
    {x : G} (hx : x ∈ MulAction.stabilizer G α) (hx5 : orderOf x = 5) {u v : V}
    (hu : Γ.Adj α u) (hv : Γ.Adj α v) : ∃ j : ℤ, (x ^ j) • u = v := by
  have hxα : x • α = α := MulAction.mem_stabilizer_iff.1 hx
  have hxu : x • u ≠ u := by
    intro h
    obtain ⟨hE2, -⟩ := edge_isPGroup F h65 hα hu
    have hmem : x ∈ MulAction.stabilizer G α ⊓ MulAction.stabilizer G u :=
      Subgroup.mem_inf.2 ⟨hx, MulAction.mem_stabilizer_iff.2 h⟩
    obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 hE2) ⟨x, hmem⟩
    have : orderOf x = 2 ^ k := by rw [← hk]; exact (Subgroup.orderOf_mk _ _).symm
    rw [hx5] at this
    have h2 : (2 : ℕ) ∣ 5 := by
      rw [this]; exact dvd_pow_self 2 (by rintro rfl; simp at this)
    omega
  set H := Subgroup.zpowers x with hH
  have hHcard : Nat.card H = 5 := by rw [hH, Nat.card_zpowers, hx5]
  have hHfin : Finite H := Nat.finite_of_card_ne_zero (by rw [hHcard]; norm_num)
  have hstab : Nat.card (MulAction.orbit H u) * Nat.card (MulAction.stabilizer H u) =
      Nat.card H := by
    rw [← Nat.card_prod]; exact Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H u)
  rw [hHcard] at hstab
  have hdvd : Nat.card (MulAction.stabilizer H u) ∣ 5 := by
    rw [← hHcard]; exact Subgroup.card_subgroup_dvd_card _
  have hne : Nat.card (MulAction.stabilizer H u) ≠ 5 := by
    intro h5
    have htop : MulAction.stabilizer H u = ⊤ :=
      Subgroup.eq_top_of_card_eq _ (by rw [h5, hHcard])
    have : (⟨x, Subgroup.mem_zpowers x⟩ : H) ∈ MulAction.stabilizer H u := by rw [htop]; trivial
    exact hxu (MulAction.mem_stabilizer_iff.1 this)
  have h1 : Nat.card (MulAction.stabilizer H u) = 1 := by
    rcases (Nat.dvd_prime Nat.prime_five).1 hdvd with h | h
    · exact h
    · exact absurd h hne
  rw [h1, mul_one] at hstab
  have hsub : (MulAction.orbit H u) ⊆ Γ.neighborSet α := by
    rintro _ ⟨⟨h, hh⟩, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    show Γ.Adj α ((x ^ n) • u)
    have hfix : (x ^ n) • α = α := zpow_smul_of_smul_eq hxα n
    have := (F.adj_smul (x ^ n) α u).2 hu
    rwa [hfix] at this
  have hvcard : valence Γ α = Nat.card (Γ.neighborSet α) := rfl
  have hfin : (Γ.neighborSet α).Finite :=
    Set.finite_coe_iff.1 (Nat.finite_of_card_ne_zero (by omega))
  have hcardN : (Γ.neighborSet α).ncard = 5 := by
    rw [← Nat.card_coe_set_eq, ← hvcard, hα]
  have hocard : (MulAction.orbit H u).ncard = 5 := by
    rw [← Nat.card_coe_set_eq]; exact hstab
  have heq : MulAction.orbit H u = Γ.neighborSet α :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hocard, hcardN]) hfin
  have hvmem : v ∈ MulAction.orbit H u := by rw [heq]; exact hv
  obtain ⟨⟨h, hh⟩, hhv⟩ := hvmem
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  exact ⟨n, hhv⟩

end P74

end CFSG.Quasithin.Fan86
