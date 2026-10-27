module

public import CFSG.Quasithin.Recognition.GoldschmidtFan86Arcs
public import CFSG.Quasithin.Recognition.GoldschmidtFan86Setting

public section

namespace CFSG.Quasithin.Fan86

namespace P518

open SimpleGraph

variable {V G : Type*} [Group G] [MulAction G V] {Γ : SimpleGraph V}

theorem eZpow_fix {x : G} {v : V} (hxv : x • v = v) (n : ℤ) : (x ^ n) • v = v := by
  have hxiv : x⁻¹ • v = v := by rw [inv_smul_eq_iff]; exact hxv.symm
  induction n using Int.induction_on with
  | zero => simp
  | succ i ih => rw [zpow_add_one, mul_smul, hxv, ih]
  | pred i ih => rw [zpow_sub_one, mul_smul, hxiv, ih]

theorem eFive_not_fix (F : FanTree Γ G) {x : G} {o p : V} (hord : orderOf x = 5)
    (hxo : x ∈ MulAction.stabilizer G o) (hop : Γ.Adj o p) (hxp : x • p = p) : False := by
  have h2 := F.edge_two o p hop
  obtain ⟨k, hk⟩ := (IsPGroup.iff_orderOf.1 h2)
    (⟨x, hxo, MulAction.mem_stabilizer_iff.2 hxp⟩ :
      ↥(MulAction.stabilizer G o ⊓ MulAction.stabilizer G p))
  rw [← Subgroup.orderOf_coe] at hk
  simp only [hord] at hk
  rcases k with _ | k
  · norm_num at hk
  · have : 2 ∣ 5 := by rw [hk]; exact dvd_pow_self 2 (by omega)
    omega

theorem eExists_zpow_nbr (F : FanTree Γ G) {v : V} (hv : valence Γ v = 5)
    {x : G} (hx : x ∈ MulAction.stabilizer G v) (hx5 : orderOf x = 5) {u w : V}
    (hu : Γ.Adj v u) (hw : Γ.Adj v w) : ∃ j : ℤ, (x ^ j) • u = w := by
  have hxv : x • v = v := MulAction.mem_stabilizer_iff.1 hx
  have hxu : x • u ≠ u := fun h => eFive_not_fix F hx5 hx hu h
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
  have hsub : (MulAction.orbit H u) ⊆ Γ.neighborSet v := by
    rintro _ ⟨⟨h, hh⟩, rfl⟩
    obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
    show Γ.Adj v ((x ^ n) • u)
    have hfix : (x ^ n) • v = v := eZpow_fix hxv n
    have := (F.adj_smul (x ^ n) v u).2 hu
    rwa [hfix] at this
  have hvcard : valence Γ v = Nat.card (Γ.neighborSet v) := rfl
  have hfin : (Γ.neighborSet v).Finite :=
    Set.finite_coe_iff.1 (Nat.finite_of_card_ne_zero (by omega))
  have hcardN : (Γ.neighborSet v).ncard = 5 := by
    rw [← Nat.card_coe_set_eq, ← hvcard, hv]
  have hocard : (MulAction.orbit H u).ncard = 5 := by
    rw [← Nat.card_coe_set_eq]; exact hstab
  have heq : MulAction.orbit H u = Γ.neighborSet v :=
    Set.eq_of_subset_of_ncard_le hsub (by rw [hocard, hcardN]) hfin
  have hwmem : w ∈ MulAction.orbit H u := by rw [heq]; exact hw
  obtain ⟨⟨h, hh⟩, hhw⟩ := hwmem
  obtain ⟨n, rfl⟩ := Subgroup.mem_zpowers_iff.1 hh
  exact ⟨n, hhw⟩

theorem eExists_pow_nbr (F : FanTree Γ G) {v : V} (hv : valence Γ v = 5)
    {x : G} (hx : x ∈ MulAction.stabilizer G v) (hx5 : orderOf x = 5) {u w : V}
    (hu : Γ.Adj v u) (hw : Γ.Adj v w) : ∃ n : ℕ, (x ^ n) • u = w := by
  obtain ⟨j, hj⟩ := eExists_zpow_nbr F hv hx hx5 hu hw
  refine ⟨(j % 5).toNat, ?_⟩
  have h5 : (orderOf x : ℤ) = 5 := by rw [hx5]; norm_num
  have hmod : x ^ (j % 5) = x ^ j := by
    have := zpow_mod_orderOf x j
    rwa [h5] at this
  rw [← zpow_natCast, Int.toNat_of_nonneg (Int.emod_nonneg _ (by norm_num)), hmod]
  exact hj

end P518

end CFSG.Quasithin.Fan86
